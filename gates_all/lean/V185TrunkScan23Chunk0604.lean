import V185TrunkScan23Chunk0603

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3572163 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3572163 : Nat := 118140960795 + 3572163 * 2 ^ 59
def prefixEnd_3572163 : Nat := 4983230072969 + 3 ^ 40 * 3572163 * 2
def baseEnd_3572163 : Nat := 1834236595206812629534427

theorem tailTrace_3572163 : CollatzResearch.WordTrace tailWord_3572163 prefixEnd_3572163 1834236595206812629534427 := by
  unfold tailWord_3572163
  simp only [CollatzResearch.WordTrace]
  refine ⟨130287488157671002714809143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86858325438447335143206095 130287488157671002714809143)
  ·
    refine ⟨195431232236506504072213715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130287488157671002714809143 195431232236506504072213715)
    ·
      refine ⟨293146848354759756108320573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195431232236506504072213715 293146848354759756108320573)
      ·
        refine ⟨109930068133034908540620215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293146848354759756108320573 109930068133034908540620215)
        ·
          refine ⟨164895102199552362810930323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109930068133034908540620215 164895102199552362810930323)
          ·
            refine ⟨247342653299328544216395485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164895102199552362810930323 247342653299328544216395485)
            ·
              refine ⟨92753494987248204081148307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247342653299328544216395485 92753494987248204081148307)
              ·
                refine ⟨139130242480872306121722461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92753494987248204081148307 139130242480872306121722461)
                ·
                  refine ⟨52173840930327114795645923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139130242480872306121722461 52173840930327114795645923)
                  ·
                    refine ⟨78260761395490672193468885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52173840930327114795645923 78260761395490672193468885)
                    ·
                      refine ⟨1834236595206812629534427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78260761395490672193468885 1834236595206812629534427)
                      ·
                        rfl

theorem cell23_3572163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3572163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572163 prefixEnd_3572163 := by exact prefixLift 3572163
  have htrace : WordTrace (prefixWord ++ tailWord_3572163) baseStart_3572163 baseEnd_3572163 := by
    simpa [prefixWord, tailWord_3572163, baseEnd_3572163] using wordTrace_append hprefix tailTrace_3572163
  have hstable : (prefixWord ++ tailWord_3572163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572163).length < 2 ^ (prefixWord ++ tailWord_3572163).sum := by decide
  have hdescent : baseEnd_3572163 < baseStart_3572163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572250 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3572250 : Nat := 118140960795 + 3572250 * 2 ^ 59
def prefixEnd_3572250 : Nat := 4983230072969 + 3 ^ 40 * 3572250 * 2
def baseEnd_3572250 : Nat := 1834281268023753789146527

theorem tailTrace_3572250 : CollatzResearch.WordTrace tailWord_3572250 prefixEnd_3572250 1834281268023753789146527 := by
  unfold tailWord_3572250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572665327088954143306551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86860440872237211048817469 32572665327088954143306551)
  ·
    refine ⟨48858997990633431214959827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32572665327088954143306551 48858997990633431214959827)
    ·
      refine ⟨73288496985950146822439741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48858997990633431214959827 73288496985950146822439741)
      ·
        refine ⟨27483186369731305058414903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73288496985950146822439741 27483186369731305058414903)
        ·
          refine ⟨41224779554596957587622355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27483186369731305058414903 41224779554596957587622355)
          ·
            refine ⟨61837169331895436381433533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41224779554596957587622355 61837169331895436381433533)
            ·
              refine ⟨23188938499460788643037575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61837169331895436381433533 23188938499460788643037575)
              ·
                refine ⟨34783407749191182964556363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23188938499460788643037575 34783407749191182964556363)
                ·
                  refine ⟨52175111623786774446834545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34783407749191182964556363 52175111623786774446834545)
                  ·
                    refine ⟨39131333717840080835125909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52175111623786774446834545 39131333717840080835125909)
                    ·
                      refine ⟨1834281268023753789146527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39131333717840080835125909 1834281268023753789146527)
                      ·
                        rfl

theorem cell23_3572250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3572250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572250 prefixEnd_3572250 := by exact prefixLift 3572250
  have htrace : WordTrace (prefixWord ++ tailWord_3572250) baseStart_3572250 baseEnd_3572250 := by
    simpa [prefixWord, tailWord_3572250, baseEnd_3572250] using wordTrace_append hprefix tailTrace_3572250
  have hstable : (prefixWord ++ tailWord_3572250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572250).length < 2 ^ (prefixWord ++ tailWord_3572250).sum := by decide
  have hdescent : baseEnd_3572250 < baseStart_3572250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572274 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3572274 : Nat := 118140960795 + 3572274 * 2 ^ 59
def prefixEnd_3572274 : Nat := 4983230072969 + 3 ^ 40 * 3572274 * 2
def baseEnd_3572274 : Nat := 1834293591559461695246417

theorem tailTrace_3572274 : CollatzResearch.WordTrace tailWord_3572274 prefixEnd_3572274 1834293591559461695246417 := by
  unfold tailWord_3572274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572884165067217168024969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86861024440179245781399917 32572884165067217168024969)
  ·
    refine ⟨24429663123800412876018727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32572884165067217168024969 24429663123800412876018727)
    ·
      refine ⟨36644494685700619314028091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24429663123800412876018727 36644494685700619314028091)
      ·
        refine ⟨54966742028550928971042137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36644494685700619314028091 54966742028550928971042137)
        ·
          refine ⟨41225056521413196728281603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54966742028550928971042137 41225056521413196728281603)
          ·
            refine ⟨61837584782119795092422405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41225056521413196728281603 61837584782119795092422405)
            ·
              refine ⟨11594547146647461579829201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61837584782119795092422405 11594547146647461579829201)
              ·
                refine ⟨8695910359985596184871901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11594547146647461579829201 8695910359985596184871901)
                ·
                  refine ⟨3260966384994598569326963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8695910359985596184871901 3260966384994598569326963)
                  ·
                    refine ⟨4891449577491897853990445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3260966384994598569326963 4891449577491897853990445)
                    ·
                      refine ⟨1834293591559461695246417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4891449577491897853990445 1834293591559461695246417)
                      ·
                        rfl

theorem cell23_3572274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3572274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572274 prefixEnd_3572274 := by exact prefixLift 3572274
  have htrace : WordTrace (prefixWord ++ tailWord_3572274) baseStart_3572274 baseEnd_3572274 := by
    simpa [prefixWord, tailWord_3572274, baseEnd_3572274] using wordTrace_append hprefix tailTrace_3572274
  have hstable : (prefixWord ++ tailWord_3572274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572274).length < 2 ^ (prefixWord ++ tailWord_3572274).sum := by decide
  have hdescent : baseEnd_3572274 < baseStart_3572274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572284 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_3572284 : Nat := 118140960795 + 3572284 * 2 ^ 59
def prefixEnd_3572284 : Nat := 4983230072969 + 3 ^ 40 * 3572284 * 2
def baseEnd_3572284 : Nat := 1834298726366006656121371

theorem tailTrace_3572284 : CollatzResearch.WordTrace tailWord_3572284 prefixEnd_3572284 1834298726366006656121371 := by
  unfold tailWord_3572284
  simp only [CollatzResearch.WordTrace]
  refine ⟨65145950695116320189981953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86861267593488426919975937 65145950695116320189981953)
  ·
    refine ⟨48859463021337240142486465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65145950695116320189981953 48859463021337240142486465)
    ·
      refine ⟨36644597266002930106864849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48859463021337240142486465 36644597266002930106864849)
      ·
        refine ⟨27483447949502197580148637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36644597266002930106864849 27483447949502197580148637)
        ·
          refine ⟨10306292981063324092555739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27483447949502197580148637 10306292981063324092555739)
          ·
            refine ⟨15459439471594986138833609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10306292981063324092555739 15459439471594986138833609)
            ·
              refine ⟨11594579603696239604125207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15459439471594986138833609 11594579603696239604125207)
              ·
                refine ⟨17391869405544359406187811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594579603696239604125207 17391869405544359406187811)
                ·
                  refine ⟨26087804108316539109281717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17391869405544359406187811 26087804108316539109281717)
                  ·
                    refine ⟨2445731635154675541495161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26087804108316539109281717 2445731635154675541495161)
                    ·
                      refine ⟨1834298726366006656121371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445731635154675541495161 1834298726366006656121371)
                      ·
                        rfl

theorem cell23_3572284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_3572284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572284 prefixEnd_3572284 := by exact prefixLift 3572284
  have htrace : WordTrace (prefixWord ++ tailWord_3572284) baseStart_3572284 baseEnd_3572284 := by
    simpa [prefixWord, tailWord_3572284, baseEnd_3572284] using wordTrace_append hprefix tailTrace_3572284
  have hstable : (prefixWord ++ tailWord_3572284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572284).length < 2 ^ (prefixWord ++ tailWord_3572284).sum := by decide
  have hdescent : baseEnd_3572284 < baseStart_3572284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572301 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3572301 : Nat := 118140960795 + 3572301 * 2 ^ 59
def prefixEnd_3572301 : Nat := 4983230072969 + 3 ^ 40 * 3572301 * 2
def baseEnd_3572301 : Nat := 1834307455537133089608793

theorem tailTrace_3572301 : CollatzResearch.WordTrace tailWord_3572301 prefixEnd_3572301 1834307455537133089608793 := by
  unfold tailWord_3572301
  simp only [CollatzResearch.WordTrace]
  refine ⟨130292521431171052283332757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86861680954114034855555171 130292521431171052283332757)
  ·
    refine ⟨6107461942086143075781223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130292521431171052283332757 6107461942086143075781223)
    ·
      refine ⟨9161192913129214613671835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6107461942086143075781223 9161192913129214613671835)
      ·
        refine ⟨13741789369693821920507753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161192913129214613671835 13741789369693821920507753)
        ·
          refine ⟨10306342027270366440380815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13741789369693821920507753 10306342027270366440380815)
          ·
            refine ⟨15459513040905549660571223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10306342027270366440380815 15459513040905549660571223)
            ·
              refine ⟨23189269561358324490856835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15459513040905549660571223 23189269561358324490856835)
              ·
                refine ⟨34783904342037486736285253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23189269561358324490856835 34783904342037486736285253)
                ·
                  refine ⟨6521982064132028763053485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34783904342037486736285253 6521982064132028763053485)
                  ·
                    refine ⟨2445743274049510786145057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6521982064132028763053485 2445743274049510786145057)
                    ·
                      refine ⟨1834307455537133089608793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445743274049510786145057 1834307455537133089608793)
                      ·
                        rfl

theorem cell23_3572301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3572301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572301 prefixEnd_3572301 := by exact prefixLift 3572301
  have htrace : WordTrace (prefixWord ++ tailWord_3572301) baseStart_3572301 baseEnd_3572301 := by
    simpa [prefixWord, tailWord_3572301, baseEnd_3572301] using wordTrace_append hprefix tailTrace_3572301
  have hstable : (prefixWord ++ tailWord_3572301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572301).length < 2 ^ (prefixWord ++ tailWord_3572301).sum := by decide
  have hdescent : baseEnd_3572301 < baseStart_3572301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572320 : List Nat := [2, 1, 1, 3, 2, 1, 3, 10]
def baseStart_3572320 : Nat := 118140960795 + 3572320 * 2 ^ 59
def prefixEnd_3572320 : Nat := 4983230072969 + 3 ^ 40 * 3572320 * 2
def baseEnd_3572320 : Nat := 67937674506280315380415

theorem tailTrace_3572320 : CollatzResearch.WordTrace tailWord_3572320 prefixEnd_3572320 67937674506280315380415 := by
  unfold tailWord_3572320
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146607209051109264137207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86862142945401479018849609 65146607209051109264137207)
  ·
    refine ⟨97719910813576663896205811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65146607209051109264137207 97719910813576663896205811)
    ·
      refine ⟨146579866220364995844308717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97719910813576663896205811 146579866220364995844308717)
      ·
        refine ⟨54967449832636873441615769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146579866220364995844308717 54967449832636873441615769)
        ·
          refine ⟨41225587374477655081211827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54967449832636873441615769 41225587374477655081211827)
          ·
            refine ⟨61838381061716482621817741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41225587374477655081211827 61838381061716482621817741)
            ·
              refine ⟨23189392898143680983181653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61838381061716482621817741 23189392898143680983181653)
              ·
                refine ⟨67937674506280315380415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23189392898143680983181653 67937674506280315380415)
                ·
                  rfl

theorem cell23_3572320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_3572320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572320 prefixEnd_3572320 := by exact prefixLift 3572320
  have htrace : WordTrace (prefixWord ++ tailWord_3572320) baseStart_3572320 baseEnd_3572320 := by
    simpa [prefixWord, tailWord_3572320, baseEnd_3572320] using wordTrace_append hprefix tailTrace_3572320
  have hstable : (prefixWord ++ tailWord_3572320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572320).length < 2 ^ (prefixWord ++ tailWord_3572320).sum := by decide
  have hdescent : baseEnd_3572320 < baseStart_3572320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572324 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_3572324 : Nat := 118140960795 + 3572324 * 2 ^ 59
def prefixEnd_3572324 : Nat := 4983230072969 + 3 ^ 40 * 3572324 * 2
def baseEnd_3572324 : Nat := 611439755197395499873729

theorem tailTrace_3572324 : CollatzResearch.WordTrace tailWord_3572324 prefixEnd_3572324 611439755197395499873729 := by
  unfold tailWord_3572324
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146680155043863605710013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86862240206725151474280017 65146680155043863605710013)
  ·
    refine ⟨24430005058141448852141255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65146680155043863605710013 24430005058141448852141255)
    ·
      refine ⟨36645007587212173278211883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24430005058141448852141255 36645007587212173278211883)
      ·
        refine ⟨54967511380818259917317825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36645007587212173278211883 54967511380818259917317825)
        ·
          refine ⟨41225633535613694937988369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54967511380818259917317825 41225633535613694937988369)
          ·
            refine ⟨30919225151710271203491277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41225633535613694937988369 30919225151710271203491277)
            ·
              refine ⟨11594709431891351701309229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30919225151710271203491277 11594709431891351701309229)
              ·
                refine ⟨4348016036959256887990961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11594709431891351701309229 4348016036959256887990961)
                ·
                  refine ⟨3261012027719442665993221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348016036959256887990961 3261012027719442665993221)
                  ·
                    refine ⟨611439755197395499873729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261012027719442665993221 611439755197395499873729)
                    ·
                      rfl

theorem cell23_3572324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_3572324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572324 prefixEnd_3572324 := by exact prefixLift 3572324
  have htrace : WordTrace (prefixWord ++ tailWord_3572324) baseStart_3572324 baseEnd_3572324 := by
    simpa [prefixWord, tailWord_3572324, baseEnd_3572324] using wordTrace_append hprefix tailTrace_3572324
  have hstable : (prefixWord ++ tailWord_3572324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572324).length < 2 ^ (prefixWord ++ tailWord_3572324).sum := by decide
  have hdescent : baseEnd_3572324 < baseStart_3572324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572327 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3572327 : Nat := 118140960795 + 3572327 * 2 ^ 59
def prefixEnd_3572327 : Nat := 4983230072969 + 3 ^ 40 * 3572327 * 2
def baseEnd_3572327 : Nat := 1834320806034149987883673

theorem tailTrace_3572327 : CollatzResearch.WordTrace tailWord_3572327 prefixEnd_3572327 1834320806034149987883673 := by
  unfold tailWord_3572327
  simp only [CollatzResearch.WordTrace]
  refine ⟨130293469729076858723779235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86862313152717905815852823 130293469729076858723779235)
  ·
    refine ⟨195440204593615288085668853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130293469729076858723779235 195440204593615288085668853)
    ·
      refine ⟨18322519180651433258031455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195440204593615288085668853 18322519180651433258031455)
      ·
        refine ⟨27483778770977149887047183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322519180651433258031455 27483778770977149887047183)
        ·
          refine ⟨41225668156465724830570775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27483778770977149887047183 41225668156465724830570775)
          ·
            refine ⟨61838502234698587245856163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41225668156465724830570775 61838502234698587245856163)
            ·
              refine ⟨92757753352047880868784245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61838502234698587245856163 92757753352047880868784245)
              ·
                refine ⟨8696039376754488831448523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92757753352047880868784245 8696039376754488831448523)
                ·
                  refine ⟨13044059065131733247172785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8696039376754488831448523 13044059065131733247172785)
                  ·
                    refine ⟨9783044298848799935379589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13044059065131733247172785 9783044298848799935379589)
                    ·
                      refine ⟨1834320806034149987883673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9783044298848799935379589 1834320806034149987883673)
                      ·
                        rfl

theorem cell23_3572327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3572327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572327 prefixEnd_3572327 := by exact prefixLift 3572327
  have htrace : WordTrace (prefixWord ++ tailWord_3572327) baseStart_3572327 baseEnd_3572327 := by
    simpa [prefixWord, tailWord_3572327, baseEnd_3572327] using wordTrace_append hprefix tailTrace_3572327
  have hstable : (prefixWord ++ tailWord_3572327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572327).length < 2 ^ (prefixWord ++ tailWord_3572327).sum := by decide
  have hdescent : baseEnd_3572327 < baseStart_3572327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572328 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_3572328 : Nat := 118140960795 + 3572328 * 2 ^ 59
def prefixEnd_3572328 : Nat := 4983230072969 + 3 ^ 40 * 3572328 * 2
def baseEnd_3572328 : Nat := 611440439838268161323723

theorem tailTrace_3572328 : CollatzResearch.WordTrace tailWord_3572328 prefixEnd_3572328 611440439838268161323723 := by
  unfold tailWord_3572328
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146753101036617947282819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86862337468048823929710425 65146753101036617947282819)
  ·
    refine ⟨97720129651554926920924229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65146753101036617947282819 97720129651554926920924229)
    ·
      refine ⟨18322524309666548797673293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97720129651554926920924229 18322524309666548797673293)
      ·
        refine ⟨6870946616124955799127485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18322524309666548797673293 6870946616124955799127485)
        ·
          refine ⟨2576604981046858424672807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6870946616124955799127485 2576604981046858424672807)
          ·
            refine ⟨3864907471570287637009211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576604981046858424672807 3864907471570287637009211)
            ·
              refine ⟨5797361207355431455513817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864907471570287637009211 5797361207355431455513817)
              ·
                refine ⟨4348020905516573591635363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797361207355431455513817 4348020905516573591635363)
                ·
                  refine ⟨6522031358274860387453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348020905516573591635363 6522031358274860387453045)
                  ·
                    refine ⟨611440439838268161323723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6522031358274860387453045 611440439838268161323723)
                    ·
                      rfl

theorem cell23_3572328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_3572328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572328 prefixEnd_3572328 := by exact prefixLift 3572328
  have htrace : WordTrace (prefixWord ++ tailWord_3572328) baseStart_3572328 baseEnd_3572328 := by
    simpa [prefixWord, tailWord_3572328, baseEnd_3572328] using wordTrace_append hprefix tailTrace_3572328
  have hstable : (prefixWord ++ tailWord_3572328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572328).length < 2 ^ (prefixWord ++ tailWord_3572328).sum := by decide
  have hdescent : baseEnd_3572328 < baseStart_3572328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572381 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3572381 : Nat := 118140960795 + 3572381 * 2 ^ 59
def prefixEnd_3572381 : Nat := 4983230072969 + 3 ^ 40 * 3572381 * 2
def baseEnd_3572381 : Nat := 1834348533989492776608425

theorem tailTrace_3572381 : CollatzResearch.WordTrace tailWord_3572381 prefixEnd_3572381 1834348533989492776608425 := by
  unfold tailWord_3572381
  simp only [CollatzResearch.WordTrace]
  refine ⟨130295439270881225946244997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86863626180587483964163331 130295439270881225946244997)
  ·
    refine ⟨24430394863290229864920937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130295439270881225946244997 24430394863290229864920937)
    ·
      refine ⟨18322796147467672398690703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24430394863290229864920937 18322796147467672398690703)
      ·
        refine ⟨27484194221201508598036055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322796147467672398690703 27484194221201508598036055)
        ·
          refine ⟨41226291331802262897054083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27484194221201508598036055 41226291331802262897054083)
          ·
            refine ⟨61839436997703394345581125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41226291331802262897054083 61839436997703394345581125)
            ·
              refine ⟨11594894437069386439796461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61839436997703394345581125 11594894437069386439796461)
              ·
                refine ⟨4348085413901019914923673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11594894437069386439796461 4348085413901019914923673)
                ·
                  refine ⟨3261064060425764936192755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348085413901019914923673 3261064060425764936192755)
                  ·
                    refine ⟨4891596090638647404289133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3261064060425764936192755 4891596090638647404289133)
                    ·
                      refine ⟨1834348533989492776608425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4891596090638647404289133 1834348533989492776608425)
                      ·
                        rfl

theorem cell23_3572381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3572381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572381 prefixEnd_3572381 := by exact prefixLift 3572381
  have htrace : WordTrace (prefixWord ++ tailWord_3572381) baseStart_3572381 baseEnd_3572381 := by
    simpa [prefixWord, tailWord_3572381, baseEnd_3572381] using wordTrace_append hprefix tailTrace_3572381
  have hstable : (prefixWord ++ tailWord_3572381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572381).length < 2 ^ (prefixWord ++ tailWord_3572381).sum := by decide
  have hdescent : baseEnd_3572381 < baseStart_3572381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572457 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_3572457 : Nat := 118140960795 + 3572457 * 2 ^ 59
def prefixEnd_3572457 : Nat := 4983230072969 + 3 ^ 40 * 3572457 * 2
def baseEnd_3572457 : Nat := 611462519506411493086025

theorem tailTrace_3572457 : CollatzResearch.WordTrace tailWord_3572457 prefixEnd_3572457 611462519506411493086025 := by
  unfold tailWord_3572457
  simp only [CollatzResearch.WordTrace]
  refine ⟨130298211218605890926011625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86865474145737260617341083 130298211218605890926011625)
  ·
    refine ⟨97723658413954418194508719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130298211218605890926011625 97723658413954418194508719)
    ·
      refine ⟨146585487620931627291763079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97723658413954418194508719 146585487620931627291763079)
      ·
        refine ⟨219878231431397440937644619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146585487620931627291763079 219878231431397440937644619)
        ·
          refine ⟨329817347147096161406466929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219878231431397440937644619 329817347147096161406466929)
          ·
            refine ⟨247363010360322121054850197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329817347147096161406466929 247363010360322121054850197)
            ·
              refine ⟨11595141110640099424446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247363010360322121054850197 11595141110640099424446103)
              ·
                refine ⟨17392711665960149136669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595141110640099424446103 17392711665960149136669155)
                ·
                  refine ⟨26089067498940223705003733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392711665960149136669155 26089067498940223705003733)
                  ·
                    refine ⟨611462519506411493086025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26089067498940223705003733 611462519506411493086025)
                    ·
                      rfl

theorem cell23_3572457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_3572457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572457 prefixEnd_3572457 := by exact prefixLift 3572457
  have htrace : WordTrace (prefixWord ++ tailWord_3572457) baseStart_3572457 baseEnd_3572457 := by
    simpa [prefixWord, tailWord_3572457, baseEnd_3572457] using wordTrace_append hprefix tailTrace_3572457
  have hstable : (prefixWord ++ tailWord_3572457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572457).length < 2 ^ (prefixWord ++ tailWord_3572457).sum := by decide
  have hdescent : baseEnd_3572457 < baseStart_3572457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572467 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_3572467 : Nat := 118140960795 + 3572467 * 2 ^ 59
def prefixEnd_3572467 : Nat := 4983230072969 + 3 ^ 40 * 3572467 * 2
def baseEnd_3572467 : Nat := 1834392693325779440133029

theorem tailTrace_3572467 : CollatzResearch.WordTrace tailWord_3572467 prefixEnd_3572467 1834392693325779440133029 := by
  unfold tailWord_3572467
  simp only [CollatzResearch.WordTrace]
  refine ⟨130298575948569662633875655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86865717299046441755917103 130298575948569662633875655)
  ·
    refine ⟨195447863922854493950813483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130298575948569662633875655 195447863922854493950813483)
    ·
      refine ⟨293171795884281740926220225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195447863922854493950813483 293171795884281740926220225)
      ·
        refine ⟨219878846913211305694665169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293171795884281740926220225 219878846913211305694665169)
        ·
          refine ⟨164909135184908479270998877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219878846913211305694665169 164909135184908479270998877)
          ·
            refine ⟨61840925694340679726624579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164909135184908479270998877 61840925694340679726624579)
            ·
              refine ⟨92761388541511019589936869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61840925694340679726624579 92761388541511019589936869)
              ·
                refine ⟨17392760351533316173113163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92761388541511019589936869 17392760351533316173113163)
                ·
                  refine ⟨26089140527299974259669745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392760351533316173113163 26089140527299974259669745)
                  ·
                    refine ⟨19566855395474980694752309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26089140527299974259669745 19566855395474980694752309)
                    ·
                      refine ⟨1834392693325779440133029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19566855395474980694752309 1834392693325779440133029)
                      ·
                        rfl

theorem cell23_3572467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_3572467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572467 prefixEnd_3572467 := by exact prefixLift 3572467
  have htrace : WordTrace (prefixWord ++ tailWord_3572467) baseStart_3572467 baseEnd_3572467 := by
    simpa [prefixWord, tailWord_3572467, baseEnd_3572467] using wordTrace_append hprefix tailTrace_3572467
  have hstable : (prefixWord ++ tailWord_3572467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572467).length < 2 ^ (prefixWord ++ tailWord_3572467).sum := by decide
  have hdescent : baseEnd_3572467 < baseStart_3572467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572484 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3572484 : Nat := 118140960795 + 3572484 * 2 ^ 59
def prefixEnd_3572484 : Nat := 4983230072969 + 3 ^ 40 * 3572484 * 2
def baseEnd_3572484 : Nat := 1834401422496905873620451

theorem tailTrace_3572484 : CollatzResearch.WordTrace tailWord_3572484 prefixEnd_3572484 1834401422496905873620451 := by
  unfold tailWord_3572484
  simp only [CollatzResearch.WordTrace]
  refine ⟨65149597994754037268622253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86866130659672049691496337 65149597994754037268622253)
  ·
    refine ⟨24431099248032763975733345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65149597994754037268622253 24431099248032763975733345)
    ·
      refine ⟨18323324436024572981800009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24431099248032763975733345 18323324436024572981800009)
      ·
        refine ⟨13742493327018429736350007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18323324436024572981800009 13742493327018429736350007)
        ·
          refine ⟨20613739990527644604525011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13742493327018429736350007 20613739990527644604525011)
          ·
            refine ⟨30920609985791466906787517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20613739990527644604525011 30920609985791466906787517)
            ·
              refine ⟨11595228744671800090045319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30920609985791466906787517 11595228744671800090045319)
              ·
                refine ⟨17392843117007700135067979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595228744671800090045319 17392843117007700135067979)
                ·
                  refine ⟨26089264675511550202601969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392843117007700135067979 26089264675511550202601969)
                  ·
                    refine ⟨19566948506633662651951477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26089264675511550202601969 19566948506633662651951477)
                    ·
                      refine ⟨1834401422496905873620451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19566948506633662651951477 1834401422496905873620451)
                      ·
                        rfl

theorem cell23_3572484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3572484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572484 prefixEnd_3572484 := by exact prefixLift 3572484
  have htrace : WordTrace (prefixWord ++ tailWord_3572484) baseStart_3572484 baseEnd_3572484 := by
    simpa [prefixWord, tailWord_3572484, baseEnd_3572484] using wordTrace_append hprefix tailTrace_3572484
  have hstable : (prefixWord ++ tailWord_3572484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572484).length < 2 ^ (prefixWord ++ tailWord_3572484).sum := by decide
  have hdescent : baseEnd_3572484 < baseStart_3572484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572494 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3572494 : Nat := 118140960795 + 3572494 * 2 ^ 59
def prefixEnd_3572494 : Nat := 4983230072969 + 3 ^ 40 * 3572494 * 2
def baseEnd_3572494 : Nat := 1834406557303450834495405

theorem tailTrace_3572494 : CollatzResearch.WordTrace tailWord_3572494 prefixEnd_3572494 1834406557303450834495405 := by
  unfold tailWord_3572494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287445089933980780638567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86866373812981230830072357 16287445089933980780638567)
  ·
    refine ⟨24431167634900971170957851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287445089933980780638567 24431167634900971170957851)
    ·
      refine ⟨36646751452351456756436777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431167634900971170957851 36646751452351456756436777)
      ·
        refine ⟨27485063589263592567327583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36646751452351456756436777 27485063589263592567327583)
        ·
          refine ⟨41227595383895388850991375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485063589263592567327583 41227595383895388850991375)
          ·
            refine ⟨61841393075843083276487063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41227595383895388850991375 61841393075843083276487063)
            ·
              refine ⟨92762089613764624914730595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61841393075843083276487063 92762089613764624914730595)
              ·
                refine ⟨139143134420646937372095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92762089613764624914730595 139143134420646937372095893)
                ·
                  refine ⟨6522334425967825189316995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139143134420646937372095893 6522334425967825189316995)
                  ·
                    refine ⟨9783501638951737783975493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522334425967825189316995 9783501638951737783975493)
                    ·
                      refine ⟨1834406557303450834495405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9783501638951737783975493 1834406557303450834495405)
                      ·
                        rfl

theorem cell23_3572494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3572494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572494 prefixEnd_3572494 := by exact prefixLift 3572494
  have htrace : WordTrace (prefixWord ++ tailWord_3572494) baseStart_3572494 baseEnd_3572494 := by
    simpa [prefixWord, tailWord_3572494, baseEnd_3572494] using wordTrace_append hprefix tailTrace_3572494
  have hstable : (prefixWord ++ tailWord_3572494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572494).length < 2 ^ (prefixWord ++ tailWord_3572494).sum := by decide
  have hdescent : baseEnd_3572494 < baseStart_3572494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572504 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_3572504 : Nat := 118140960795 + 3572504 * 2 ^ 59
def prefixEnd_3572504 : Nat := 4983230072969 + 3 ^ 40 * 3572504 * 2
def baseEnd_3572504 : Nat := 611470564036665265123453

theorem tailTrace_3572504 : CollatzResearch.WordTrace tailWord_3572504 prefixEnd_3572504 611470564036665265123453 := by
  unfold tailWord_3572504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65149962724717808976486283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86866616966290411968648377 65149962724717808976486283)
  ·
    refine ⟨97724944087076713464729425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65149962724717808976486283 97724944087076713464729425)
    ·
      refine ⟨73293708065307535098547069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97724944087076713464729425 73293708065307535098547069)
      ·
        refine ⟨27485140524490325661955151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73293708065307535098547069 27485140524490325661955151)
        ·
          refine ⟨41227710786735488492932727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485140524490325661955151 41227710786735488492932727)
          ·
            refine ⟨61841566180103232739399091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41227710786735488492932727 61841566180103232739399091)
            ·
              refine ⟨92762349270154849109098637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61841566180103232739399091 92762349270154849109098637)
              ·
                refine ⟨34785880976308068415911989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92762349270154849109098637 34785880976308068415911989)
                ·
                  refine ⟨3261176341528881413991749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34785880976308068415911989 3261176341528881413991749)
                  ·
                    refine ⟨611470564036665265123453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261176341528881413991749 611470564036665265123453)
                    ·
                      rfl

theorem cell23_3572504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_3572504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572504 prefixEnd_3572504 := by exact prefixLift 3572504
  have htrace : WordTrace (prefixWord ++ tailWord_3572504) baseStart_3572504 baseEnd_3572504 := by
    simpa [prefixWord, tailWord_3572504, baseEnd_3572504] using wordTrace_append hprefix tailTrace_3572504
  have hstable : (prefixWord ++ tailWord_3572504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572504).length < 2 ^ (prefixWord ++ tailWord_3572504).sum := by decide
  have hdescent : baseEnd_3572504 < baseStart_3572504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572511 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_3572511 : Nat := 118140960795 + 3572511 * 2 ^ 59
def prefixEnd_3572511 : Nat := 4983230072969 + 3 ^ 40 * 3572511 * 2
def baseEnd_3572511 : Nat := 1834415286474577267982827

theorem tailTrace_3572511 : CollatzResearch.WordTrace tailWord_3572511 prefixEnd_3572511 1834415286474577267982827 := by
  unfold tailWord_3572511
  simp only [CollatzResearch.WordTrace]
  refine ⟨130300180760410258148477387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86866787173606838765651591 130300180760410258148477387)
  ·
    refine ⟨195450271140615387222716081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130300180760410258148477387 195450271140615387222716081)
    ·
      refine ⟨146587703355461540417037061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195450271140615387222716081 146587703355461540417037061)
      ·
        refine ⟨27485194379149038828194449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146587703355461540417037061 27485194379149038828194449)
        ·
          refine ⟨20613895784361779121145837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27485194379149038828194449 20613895784361779121145837)
          ·
            refine ⟨7730210919135667170429689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20613895784361779121145837 7730210919135667170429689)
            ·
              refine ⟨5797658189351750377822267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730210919135667170429689 5797658189351750377822267)
              ·
                refine ⟨8696487284027625566733401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797658189351750377822267 8696487284027625566733401)
                ·
                  refine ⟨6522365463020719175050051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8696487284027625566733401 6522365463020719175050051)
                  ·
                    refine ⟨9783548194531078762575077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522365463020719175050051 9783548194531078762575077)
                    ·
                      refine ⟨1834415286474577267982827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9783548194531078762575077 1834415286474577267982827)
                      ·
                        rfl

theorem cell23_3572511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_3572511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572511 prefixEnd_3572511 := by exact prefixLift 3572511
  have htrace : WordTrace (prefixWord ++ tailWord_3572511) baseStart_3572511 baseEnd_3572511 := by
    simpa [prefixWord, tailWord_3572511, baseEnd_3572511] using wordTrace_append hprefix tailTrace_3572511
  have hstable : (prefixWord ++ tailWord_3572511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572511).length < 2 ^ (prefixWord ++ tailWord_3572511).sum := by decide
  have hdescent : baseEnd_3572511 < baseStart_3572511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572531 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3]
def baseStart_3572531 : Nat := 118140960795 + 3572531 * 2 ^ 59
def prefixEnd_3572531 : Nat := 4983230072969 + 3 ^ 40 * 3572531 * 2
def baseEnd_3572531 : Nat := 1834425556087667189732735

theorem tailTrace_3572531 : CollatzResearch.WordTrace tailWord_3572531 prefixEnd_3572531 1834425556087667189732735 := by
  unfold tailWord_3572531
  simp only [CollatzResearch.WordTrace]
  refine ⟨130300910220337801564205447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86867273480225201042803631 130300910220337801564205447)
  ·
    refine ⟨195451365330506702346308171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130300910220337801564205447 195451365330506702346308171)
    ·
      refine ⟨293177047995760053519462257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195451365330506702346308171 293177047995760053519462257)
      ·
        refine ⟨219882785996820040139596693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293177047995760053519462257 219882785996820040139596693)
        ·
          refine ⟨10307005593600939381543595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219882785996820040139596693 10307005593600939381543595)
          ·
            refine ⟨15460508390401409072315393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307005593600939381543595 15460508390401409072315393)
            ·
              refine ⟨11595381292801056804236545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15460508390401409072315393 11595381292801056804236545)
              ·
                refine ⟨8696535969600792603177409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11595381292801056804236545 8696535969600792603177409)
                ·
                  refine ⟨6522401977200594452383057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8696535969600792603177409 6522401977200594452383057)
                  ·
                    refine ⟨4891801482900445839287293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522401977200594452383057 4891801482900445839287293)
                    ·
                      refine ⟨1834425556087667189732735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4891801482900445839287293 1834425556087667189732735)
                      ·
                        rfl

theorem cell23_3572531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_3572531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572531 prefixEnd_3572531 := by exact prefixLift 3572531
  have htrace : WordTrace (prefixWord ++ tailWord_3572531) baseStart_3572531 baseEnd_3572531 := by
    simpa [prefixWord, tailWord_3572531, baseEnd_3572531] using wordTrace_append hprefix tailTrace_3572531
  have hstable : (prefixWord ++ tailWord_3572531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572531).length < 2 ^ (prefixWord ++ tailWord_3572531).sum := by decide
  have hdescent : baseEnd_3572531 < baseStart_3572531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572545 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3572545 : Nat := 118140960795 + 3572545 * 2 ^ 59
def prefixEnd_3572545 : Nat := 4983230072969 + 3 ^ 40 * 3572545 * 2
def baseEnd_3572545 : Nat := 1834432744816830134957671

theorem tailTrace_3572545 : CollatzResearch.WordTrace tailWord_3572545 prefixEnd_3572545 1834432744816830134957671 := by
  unfold tailWord_3572545
  simp only [CollatzResearch.WordTrace]
  refine ⟨130301420842287081955215089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86867613894858054636810059 130301420842287081955215089)
  ·
    refine ⟨97726065631715311466411317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130301420842287081955215089 97726065631715311466411317)
    ·
      refine ⟨9161818652973310449976061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97726065631715311466411317 9161818652973310449976061)
      ·
        refine ⟨3435681994864991418741023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9161818652973310449976061 3435681994864991418741023)
        ·
          refine ⟨5153522992297487128111535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435681994864991418741023 5153522992297487128111535)
          ·
            refine ⟨7730284488446230692167303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153522992297487128111535 7730284488446230692167303)
            ·
              refine ⟨11595426732669346038250955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730284488446230692167303 11595426732669346038250955)
              ·
                refine ⟨17393140099004019057376433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595426732669346038250955 17393140099004019057376433)
                ·
                  refine ⟨13044855074253014293032325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17393140099004019057376433 13044855074253014293032325)
                  ·
                    refine ⟨2445910326422440179943561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13044855074253014293032325 2445910326422440179943561)
                    ·
                      refine ⟨1834432744816830134957671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2445910326422440179943561 1834432744816830134957671)
                      ·
                        rfl

theorem cell23_3572545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3572545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572545 prefixEnd_3572545 := by exact prefixLift 3572545
  have htrace : WordTrace (prefixWord ++ tailWord_3572545) baseStart_3572545 baseEnd_3572545 := by
    simpa [prefixWord, tailWord_3572545, baseEnd_3572545] using wordTrace_append hprefix tailTrace_3572545
  have hstable : (prefixWord ++ tailWord_3572545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572545).length < 2 ^ (prefixWord ++ tailWord_3572545).sum := by decide
  have hdescent : baseEnd_3572545 < baseStart_3572545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572594 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3572594 : Nat := 118140960795 + 3572594 * 2 ^ 59
def prefixEnd_3572594 : Nat := 4983230072969 + 3 ^ 40 * 3572594 * 2
def baseEnd_3572594 : Nat := 611485968456300147748315

theorem tailTrace_3572594 : CollatzResearch.WordTrace tailWord_3572594 prefixEnd_3572594 611485968456300147748315 := by
  unfold tailWord_3572594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32575802004777390830937209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86868805346073042215832557 32575802004777390830937209)
  ·
    refine ⟨24431851503583043123202907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32575802004777390830937209 24431851503583043123202907)
    ·
      refine ⟨36647777255374564684804361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431851503583043123202907 36647777255374564684804361)
      ·
        refine ⟨27485832941530923513603271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36647777255374564684804361 27485832941530923513603271)
        ·
          refine ⟨41228749412296385270404907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485832941530923513603271 41228749412296385270404907)
          ·
            refine ⟨61843124118444577905607361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41228749412296385270404907 61843124118444577905607361)
            ·
              refine ⟨46382343088833433429205521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61843124118444577905607361 46382343088833433429205521)
              ·
                refine ⟨34786757316625075071904141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46382343088833433429205521 34786757316625075071904141)
                ·
                  refine ⟨13045033993734403151964053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34786757316625075071904141 13045033993734403151964053)
                  ·
                    refine ⟨611485968456300147748315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13045033993734403151964053 611485968456300147748315)
                    ·
                      rfl

theorem cell23_3572594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3572594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572594 prefixEnd_3572594 := by exact prefixLift 3572594
  have htrace : WordTrace (prefixWord ++ tailWord_3572594) baseStart_3572594 baseEnd_3572594 := by
    simpa [prefixWord, tailWord_3572594, baseEnd_3572594] using wordTrace_append hprefix tailTrace_3572594
  have hstable : (prefixWord ++ tailWord_3572594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572594).length < 2 ^ (prefixWord ++ tailWord_3572594).sum := by decide
  have hdescent : baseEnd_3572594 < baseStart_3572594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572618 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3572618 : Nat := 118140960795 + 3572618 * 2 ^ 59
def prefixEnd_3572618 : Nat := 4983230072969 + 3 ^ 40 * 3572618 * 2
def baseEnd_3572618 : Nat := 1834470228904608349344835

theorem tailTrace_3572618 : CollatzResearch.WordTrace tailWord_3572618 prefixEnd_3572618 1834470228904608349344835 := by
  unfold tailWord_3572618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32576020842755653855655627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86869388914015076948415005 32576020842755653855655627)
  ·
    refine ⟨48864031264133480783483441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32576020842755653855655627 48864031264133480783483441)
    ·
      refine ⟨36648023448100110587612581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48864031264133480783483441 36648023448100110587612581)
      ·
        refine ⟨6871504396518770735177359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36648023448100110587612581 6871504396518770735177359)
        ·
          refine ⟨10307256594778156102766039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871504396518770735177359 10307256594778156102766039)
          ·
            refine ⟨15460884892167234154149059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307256594778156102766039 15460884892167234154149059)
            ·
              refine ⟨23191327338250851231223589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15460884892167234154149059 23191327338250851231223589)
              ·
                refine ⟨4348373875922034605854423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23191327338250851231223589 4348373875922034605854423)
                ·
                  refine ⟨6522560813883051908781635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348373875922034605854423 6522560813883051908781635)
                  ·
                    refine ⟨9783841220824577863172453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522560813883051908781635 9783841220824577863172453)
                    ·
                      refine ⟨1834470228904608349344835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9783841220824577863172453 1834470228904608349344835)
                      ·
                        rfl

theorem cell23_3572618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3572618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572618 prefixEnd_3572618 := by exact prefixLift 3572618
  have htrace : WordTrace (prefixWord ++ tailWord_3572618) baseStart_3572618 baseEnd_3572618 := by
    simpa [prefixWord, tailWord_3572618, baseEnd_3572618] using wordTrace_append hprefix tailTrace_3572618
  have hstable : (prefixWord ++ tailWord_3572618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572618).length < 2 ^ (prefixWord ++ tailWord_3572618).sum := by decide
  have hdescent : baseEnd_3572618 < baseStart_3572618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572641 : List Nat := [1, 2, 3, 4, 1, 3, 9]
def baseStart_3572641 : Nat := 118140960795 + 3572641 * 2 ^ 59
def prefixEnd_3572641 : Nat := 4983230072969 + 3 ^ 40 * 3572641 * 2
def baseEnd_3572641 : Nat := 22647926406909404436509

theorem tailTrace_3572641 : CollatzResearch.WordTrace tailWord_3572641 prefixEnd_3572641 22647926406909404436509 := by
  unfold tailWord_3572641
  simp only [CollatzResearch.WordTrace]
  refine ⟨130304922249939290350709777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86869948166626193567139851 130304922249939290350709777)
  ·
    refine ⟨97728691687454467763032333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130304922249939290350709777 97728691687454467763032333)
    ·
      refine ⟨36648259382795425411137125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97728691687454467763032333 36648259382795425411137125)
      ·
        refine ⟨6871548634274142264588211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36648259382795425411137125 6871548634274142264588211)
        ·
          refine ⟨10307322951411213396882317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871548634274142264588211 10307322951411213396882317)
          ·
            refine ⟨3865246106779205023830869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10307322951411213396882317 3865246106779205023830869)
            ·
              refine ⟨22647926406909404436509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3865246106779205023830869 22647926406909404436509)
              ·
                rfl

theorem cell23_3572641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 9].length) (baseStart_3572641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572641 prefixEnd_3572641 := by exact prefixLift 3572641
  have htrace : WordTrace (prefixWord ++ tailWord_3572641) baseStart_3572641 baseEnd_3572641 := by
    simpa [prefixWord, tailWord_3572641, baseEnd_3572641] using wordTrace_append hprefix tailTrace_3572641
  have hstable : (prefixWord ++ tailWord_3572641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572641).length < 2 ^ (prefixWord ++ tailWord_3572641).sum := by decide
  have hdescent : baseEnd_3572641 < baseStart_3572641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3572704 : Nat := 118140960795 + 3572704 * 2 ^ 59
def prefixEnd_3572704 : Nat := 4983230072969 + 3 ^ 40 * 3572704 * 2
def baseEnd_3572704 : Nat := 1834514388240895012869439

theorem tailTrace_3572704 : CollatzResearch.WordTrace tailWord_3572704 prefixEnd_3572704 1834514388240895012869439 := by
  unfold tailWord_3572704
  simp only [CollatzResearch.WordTrace]
  refine ⟨65153610024355526055126583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86871480032474034740168777 65153610024355526055126583)
  ·
    refine ⟨97730415036533289082689875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65153610024355526055126583 97730415036533289082689875)
    ·
      refine ⟨146595622554799933624034813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97730415036533289082689875 146595622554799933624034813)
      ·
        refine ⟨54973358458049975109013055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146595622554799933624034813 54973358458049975109013055)
        ·
          refine ⟨82460037687074962663519583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54973358458049975109013055 82460037687074962663519583)
          ·
            refine ⟨123690056530612443995279375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82460037687074962663519583 123690056530612443995279375)
            ·
              refine ⟨185535084795918665992919063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123690056530612443995279375 185535084795918665992919063)
              ·
                refine ⟨278302627193877998989378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185535084795918665992919063 278302627193877998989378595)
                ·
                  refine ⟨417453940790816998484067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278302627193877998989378595 417453940790816998484067893)
                  ·
                    refine ⟨39136306949139093607881365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 417453940790816998484067893 39136306949139093607881365)
                    ·
                      refine ⟨1834514388240895012869439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39136306949139093607881365 1834514388240895012869439)
                      ·
                        rfl

theorem cell23_3572704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3572704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572704 prefixEnd_3572704 := by exact prefixLift 3572704
  have htrace : WordTrace (prefixWord ++ tailWord_3572704) baseStart_3572704 baseEnd_3572704 := by
    simpa [prefixWord, tailWord_3572704, baseEnd_3572704] using wordTrace_append hprefix tailTrace_3572704
  have hstable : (prefixWord ++ tailWord_3572704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572704).length < 2 ^ (prefixWord ++ tailWord_3572704).sum := by decide
  have hdescent : baseEnd_3572704 < baseStart_3572704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572718 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3572718 : Nat := 118140960795 + 3572718 * 2 ^ 59
def prefixEnd_3572718 : Nat := 4983230072969 + 3 ^ 40 * 3572718 * 2
def baseEnd_3572718 : Nat := 611507192323352652698125

theorem tailTrace_3572718 : CollatzResearch.WordTrace tailWord_3572718 prefixEnd_3572718 611507192323352652698125 := by
  unfold tailWord_3572718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288466333832541562657851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86871820447106888334175205 16288466333832541562657851)
  ·
    refine ⟨24432699500748812343986777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16288466333832541562657851 24432699500748812343986777)
    ·
      refine ⟨18324524625561609257990083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24432699500748812343986777 18324524625561609257990083)
      ·
        refine ⟨27486786938342413886985125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18324524625561609257990083 27486786938342413886985125)
        ·
          refine ⟨5153772550939202603809711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27486786938342413886985125 5153772550939202603809711)
          ·
            refine ⟨7730658826408803905714567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153772550939202603809711 7730658826408803905714567)
            ·
              refine ⟨11595988239613205858571851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730658826408803905714567 11595988239613205858571851)
              ·
                refine ⟨17393982359419808787857777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595988239613205858571851 17393982359419808787857777)
                ·
                  refine ⟨13045486769564856590893333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17393982359419808787857777 13045486769564856590893333)
                  ·
                    refine ⟨611507192323352652698125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13045486769564856590893333 611507192323352652698125)
                    ·
                      rfl

theorem cell23_3572718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3572718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572718 prefixEnd_3572718 := by exact prefixLift 3572718
  have htrace : WordTrace (prefixWord ++ tailWord_3572718) baseStart_3572718 baseEnd_3572718 := by
    simpa [prefixWord, tailWord_3572718, baseEnd_3572718] using wordTrace_append hprefix tailTrace_3572718
  have hstable : (prefixWord ++ tailWord_3572718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572718).length < 2 ^ (prefixWord ++ tailWord_3572718).sum := by decide
  have hdescent : baseEnd_3572718 < baseStart_3572718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572721 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3572721 : Nat := 118140960795 + 3572721 * 2 ^ 59
def prefixEnd_3572721 : Nat := 4983230072969 + 3 ^ 40 * 3572721 * 2
def baseEnd_3572721 : Nat := 1834523117412021446356861

theorem tailTrace_3572721 : CollatzResearch.WordTrace tailWord_3572721 prefixEnd_3572721 1834523117412021446356861 := by
  unfold tailWord_3572721
  simp only [CollatzResearch.WordTrace]
  refine ⟨130307840089649464013622017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86871893393099642675748011 130307840089649464013622017)
  ·
    refine ⟨97730880067237098010216513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130307840089649464013622017 97730880067237098010216513)
    ·
      refine ⟨73298160050427823507662385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97730880067237098010216513 73298160050427823507662385)
      ·
        refine ⟨54973620037820867630746789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73298160050427823507662385 54973620037820867630746789)
        ·
          refine ⟨10307553757091412680765023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54973620037820867630746789 10307553757091412680765023)
          ·
            refine ⟨15461330635637119021147535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307553757091412680765023 15461330635637119021147535)
            ·
              refine ⟨23191995953455678531721303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461330635637119021147535 23191995953455678531721303)
              ·
                refine ⟨34787993930183517797581955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23191995953455678531721303 34787993930183517797581955)
                ·
                  refine ⟨52181990895275276696372933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34787993930183517797581955 52181990895275276696372933)
                  ·
                    refine ⟨9784123292864114380569925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52181990895275276696372933 9784123292864114380569925)
                    ·
                      refine ⟨1834523117412021446356861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9784123292864114380569925 1834523117412021446356861)
                      ·
                        rfl

theorem cell23_3572721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3572721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572721 prefixEnd_3572721 := by exact prefixLift 3572721
  have htrace : WordTrace (prefixWord ++ tailWord_3572721) baseStart_3572721 baseEnd_3572721 := by
    simpa [prefixWord, tailWord_3572721, baseEnd_3572721] using wordTrace_append hprefix tailTrace_3572721
  have hstable : (prefixWord ++ tailWord_3572721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572721).length < 2 ^ (prefixWord ++ tailWord_3572721).sum := by decide
  have hdescent : baseEnd_3572721 < baseStart_3572721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572741 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_3572741 : Nat := 118140960795 + 3572741 * 2 ^ 59
def prefixEnd_3572741 : Nat := 4983230072969 + 3 ^ 40 * 3572741 * 2
def baseEnd_3572741 : Nat := 1834533387025111368106769

theorem tailTrace_3572741 : CollatzResearch.WordTrace tailWord_3572741 prefixEnd_3572741 1834533387025111368106769 := by
  unfold tailWord_3572741
  simp only [CollatzResearch.WordTrace]
  refine ⟨130308569549577007429350077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86872379699718004952900051 130308569549577007429350077)
  ·
    refine ⟨48865713581091377786006279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130308569549577007429350077 48865713581091377786006279)
    ·
      refine ⟨73298570371637066679009419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48865713581091377786006279 73298570371637066679009419)
      ·
        refine ⟨109947855557455600018514129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73298570371637066679009419 109947855557455600018514129)
        ·
          refine ⟨82460891668091700013885597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109947855557455600018514129 82460891668091700013885597)
          ·
            refine ⟨30922834375534387505207099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82460891668091700013885597 30922834375534387505207099)
            ·
              refine ⟨46384251563301581257810649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30922834375534387505207099 46384251563301581257810649)
              ·
                refine ⟨34788188672476185943357987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46384251563301581257810649 34788188672476185943357987)
                ·
                  refine ⟨52182283008714278915036981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34788188672476185943357987 52182283008714278915036981)
                  ·
                    refine ⟨4892089032066963648284717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52182283008714278915036981 4892089032066963648284717)
                    ·
                      refine ⟨1834533387025111368106769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4892089032066963648284717 1834533387025111368106769)
                      ·
                        rfl

theorem cell23_3572741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_3572741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572741 prefixEnd_3572741 := by exact prefixLift 3572741
  have htrace : WordTrace (prefixWord ++ tailWord_3572741) baseStart_3572741 baseEnd_3572741 := by
    simpa [prefixWord, tailWord_3572741, baseEnd_3572741] using wordTrace_append hprefix tailTrace_3572741
  have hstable : (prefixWord ++ tailWord_3572741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572741).length < 2 ^ (prefixWord ++ tailWord_3572741).sum := by decide
  have hdescent : baseEnd_3572741 < baseStart_3572741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572748 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 5]
def baseStart_3572748 : Nat := 118140960795 + 3572748 * 2 ^ 59
def prefixEnd_3572748 : Nat := 4983230072969 + 3 ^ 40 * 3572748 * 2
def baseEnd_3572748 : Nat := 203837442376632537857693

theorem tailTrace_3572748 : CollatzResearch.WordTrace tailWord_3572748 prefixEnd_3572748 203837442376632537857693 := by
  unfold tailWord_3572748
  simp only [CollatzResearch.WordTrace]
  refine ⟨65154412430275823812427449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86872549907034431749903265 65154412430275823812427449)
  ·
    refine ⟨48865809322706867859320587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65154412430275823812427449 48865809322706867859320587)
    ·
      refine ⟨73298713984060301788980881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48865809322706867859320587 73298713984060301788980881)
      ·
        refine ⟨54974035488045226341735661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73298713984060301788980881 54974035488045226341735661)
        ·
          refine ⟨20615263308016959878150873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54974035488045226341735661 20615263308016959878150873)
          ·
            refine ⟨15461447481012719908613155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20615263308016959878150873 15461447481012719908613155)
            ·
              refine ⟨23192171221519079862919733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461447481012719908613155 23192171221519079862919733)
              ·
                refine ⟨2174266052017413737148725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23192171221519079862919733 2174266052017413737148725)
                ·
                  refine ⟨203837442376632537857693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174266052017413737148725 203837442376632537857693)
                  ·
                    rfl

theorem cell23_3572748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_3572748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572748 prefixEnd_3572748 := by exact prefixLift 3572748
  have htrace : WordTrace (prefixWord ++ tailWord_3572748) baseStart_3572748 baseEnd_3572748 := by
    simpa [prefixWord, tailWord_3572748, baseEnd_3572748] using wordTrace_append hprefix tailTrace_3572748
  have hstable : (prefixWord ++ tailWord_3572748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572748).length < 2 ^ (prefixWord ++ tailWord_3572748).sum := by decide
  have hdescent : baseEnd_3572748 < baseStart_3572748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572759 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3572759 : Nat := 118140960795 + 3572759 * 2 ^ 59
def prefixEnd_3572759 : Nat := 4983230072969 + 3 ^ 40 * 3572759 * 2
def baseEnd_3572759 : Nat := 1834542629676892297681687

theorem tailTrace_3572759 : CollatzResearch.WordTrace tailWord_3572759 prefixEnd_3572759 1834542629676892297681687 := by
  unfold tailWord_3572759
  simp only [CollatzResearch.WordTrace]
  refine ⟨130309226063511796503505331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86872817375674531002336887 130309226063511796503505331)
  ·
    refine ⟨195463839095267694755257997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130309226063511796503505331 195463839095267694755257997)
    ·
      refine ⟨73298939660725385533221749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195463839095267694755257997 73298939660725385533221749)
      ·
        refine ⟨6871775593193004893739539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73298939660725385533221749 6871775593193004893739539)
        ·
          refine ⟨10307663389789507340609309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871775593193004893739539 10307663389789507340609309)
          ·
            refine ⟨3865373771171065252728491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10307663389789507340609309 3865373771171065252728491)
            ·
              refine ⟨5798060656756597879092737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865373771171065252728491 5798060656756597879092737)
              ·
                refine ⟨4348545492567448409319553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798060656756597879092737 4348545492567448409319553)
                ·
                  refine ⟨3261409119425586306989665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348545492567448409319553 3261409119425586306989665)
                  ·
                    refine ⟨2446056839569189730242249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3261409119425586306989665 2446056839569189730242249)
                    ·
                      refine ⟨1834542629676892297681687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446056839569189730242249 1834542629676892297681687)
                      ·
                        rfl

theorem cell23_3572759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3572759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572759 prefixEnd_3572759 := by exact prefixLift 3572759
  have htrace : WordTrace (prefixWord ++ tailWord_3572759) baseStart_3572759 baseEnd_3572759 := by
    simpa [prefixWord, tailWord_3572759, baseEnd_3572759] using wordTrace_append hprefix tailTrace_3572759
  have hstable : (prefixWord ++ tailWord_3572759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572759).length < 2 ^ (prefixWord ++ tailWord_3572759).sum := by decide
  have hdescent : baseEnd_3572759 < baseStart_3572759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572761 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_3572761 : Nat := 118140960795 + 3572761 * 2 ^ 59
def prefixEnd_3572761 : Nat := 4983230072969 + 3 ^ 40 * 3572761 * 2
def baseEnd_3572761 : Nat := 611514552212733763285559

theorem tailTrace_3572761 : CollatzResearch.WordTrace tailWord_3572761 prefixEnd_3572761 611514552212733763285559 := by
  unfold tailWord_3572761
  simp only [CollatzResearch.WordTrace]
  refine ⟨130309299009504550845078137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86872866006336367230052091 130309299009504550845078137)
  ·
    refine ⟨97731974257128413133808603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130309299009504550845078137 97731974257128413133808603)
    ·
      refine ⟨146597961385692619700712905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97731974257128413133808603 146597961385692619700712905)
      ·
        refine ⟨109948471039269464775534679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146597961385692619700712905 109948471039269464775534679)
        ·
          refine ⟨164922706558904197163302019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109948471039269464775534679 164922706558904197163302019)
          ·
            refine ⟨247384059838356295744953029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164922706558904197163302019 247384059838356295744953029)
            ·
              refine ⟨46384511219691805452178693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247384059838356295744953029 46384511219691805452178693)
              ·
                refine ⟨8697095853692213522283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46384511219691805452178693 8697095853692213522283505)
                ·
                  refine ⟨6522821890269160141712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8697095853692213522283505 6522821890269160141712629)
                  ·
                    refine ⟨611514552212733763285559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6522821890269160141712629 611514552212733763285559)
                    ·
                      rfl

theorem cell23_3572761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_3572761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572761 prefixEnd_3572761 := by exact prefixLift 3572761
  have htrace : WordTrace (prefixWord ++ tailWord_3572761) baseStart_3572761 baseEnd_3572761 := by
    simpa [prefixWord, tailWord_3572761, baseEnd_3572761] using wordTrace_append hprefix tailTrace_3572761
  have hstable : (prefixWord ++ tailWord_3572761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572761).length < 2 ^ (prefixWord ++ tailWord_3572761).sum := by decide
  have hdescent : baseEnd_3572761 < baseStart_3572761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572775 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3572775 : Nat := 118140960795 + 3572775 * 2 ^ 59
def prefixEnd_3572775 : Nat := 4983230072969 + 3 ^ 40 * 3572775 * 2
def baseEnd_3572775 : Nat := 1834550845367364235081613

theorem tailTrace_3572775 : CollatzResearch.WordTrace tailWord_3572775 prefixEnd_3572775 1834550845367364235081613 := by
  unfold tailWord_3572775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130309809631453831236087779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86873206420969220824058519 130309809631453831236087779)
  ·
    refine ⟨195464714447180746854131669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130309809631453831236087779 195464714447180746854131669)
    ·
      refine ⟨4581204244855798754393711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 195464714447180746854131669 4581204244855798754393711)
      ·
        refine ⟨6871806367283698131590567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581204244855798754393711 6871806367283698131590567)
        ·
          refine ⟨10307709550925547197385851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871806367283698131590567 10307709550925547197385851)
          ·
            refine ⟨15461564326388320796078777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307709550925547197385851 15461564326388320796078777)
            ·
              refine ⟨11596173244791240597059083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15461564326388320796078777 11596173244791240597059083)
              ·
                refine ⟨17394259867186860895588625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11596173244791240597059083 17394259867186860895588625)
                ·
                  refine ⟨13045694900390145671691469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17394259867186860895588625 13045694900390145671691469)
                  ·
                    refine ⟨4892135587646304626884301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13045694900390145671691469 4892135587646304626884301)
                    ·
                      refine ⟨1834550845367364235081613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4892135587646304626884301 1834550845367364235081613)
                      ·
                        rfl

theorem cell23_3572775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3572775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572775 prefixEnd_3572775 := by exact prefixLift 3572775
  have htrace : WordTrace (prefixWord ++ tailWord_3572775) baseStart_3572775 baseEnd_3572775 := by
    simpa [prefixWord, tailWord_3572775, baseEnd_3572775] using wordTrace_append hprefix tailTrace_3572775
  have hstable : (prefixWord ++ tailWord_3572775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572775).length < 2 ^ (prefixWord ++ tailWord_3572775).sum := by decide
  have hdescent : baseEnd_3572775 < baseStart_3572775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572821 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 8]
def baseStart_3572821 : Nat := 118140960795 + 3572821 * 2 ^ 59
def prefixEnd_3572821 : Nat := 4983230072969 + 3 ^ 40 * 3572821 * 2
def baseEnd_3572821 : Nat := 203841607275274561678489

theorem tailTrace_3572821 : CollatzResearch.WordTrace tailWord_3572821 prefixEnd_3572821 203841607275274561678489 := by
  unfold tailWord_3572821
  simp only [CollatzResearch.WordTrace]
  refine ⟨130311487389287181092262317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86874324926191454061508211 130311487389287181092262317)
  ·
    refine ⟨48866807770982692909598369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130311487389287181092262317 48866807770982692909598369)
    ·
      refine ⟨36650105828237019682198777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48866807770982692909598369 36650105828237019682198777)
      ·
        refine ⟨27487579371177764761649083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36650105828237019682198777 27487579371177764761649083)
        ·
          refine ⟨41231369056766647142473625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27487579371177764761649083 41231369056766647142473625)
          ·
            refine ⟨30923526792574985356855219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41231369056766647142473625 30923526792574985356855219)
            ·
              refine ⟨46385290188862478035282829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30923526792574985356855219 46385290188862478035282829)
              ·
                refine ⟨17394483820823429263231061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46385290188862478035282829 17394483820823429263231061)
                ·
                  refine ⟨203841607275274561678489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17394483820823429263231061 203841607275274561678489)
                  ·
                    rfl

theorem cell23_3572821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_3572821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572821 prefixEnd_3572821 := by exact prefixLift 3572821
  have htrace : WordTrace (prefixWord ++ tailWord_3572821) baseStart_3572821 baseEnd_3572821 := by
    simpa [prefixWord, tailWord_3572821, baseEnd_3572821] using wordTrace_append hprefix tailTrace_3572821
  have hstable : (prefixWord ++ tailWord_3572821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572821).length < 2 ^ (prefixWord ++ tailWord_3572821).sum := by decide
  have hdescent : baseEnd_3572821 < baseStart_3572821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572822 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3572822 : Nat := 118140960795 + 3572822 * 2 ^ 59
def prefixEnd_3572822 : Nat := 4983230072969 + 3 ^ 40 * 3572822 * 2
def baseEnd_3572822 : Nat := 1834574978958125551193897

theorem tailTrace_3572822 : CollatzResearch.WordTrace tailWord_3572822 prefixEnd_3572822 1834574978958125551193897 := by
  unfold tailWord_3572822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144470241392722391440545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86874349241522372175365813 8144470241392722391440545)
  ·
    refine ⟨6108352681044541793580409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8144470241392722391440545 6108352681044541793580409)
    ·
      refine ⟨4581264510783406345185307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6108352681044541793580409 4581264510783406345185307)
      ·
        refine ⟨6871896766175109517777961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581264510783406345185307 6871896766175109517777961)
        ·
          refine ⟨5153922574631332138333471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6871896766175109517777961 5153922574631332138333471)
          ·
            refine ⟨7730883861946998207500207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153922574631332138333471 7730883861946998207500207)
            ·
              refine ⟨11596325792920497311250311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730883861946998207500207 11596325792920497311250311)
              ·
                refine ⟨17394488689380745966875467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11596325792920497311250311 17394488689380745966875467)
                ·
                  refine ⟨26091733034071118950313201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17394488689380745966875467 26091733034071118950313201)
                  ·
                    refine ⟨19568799775553339212734901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26091733034071118950313201 19568799775553339212734901)
                    ·
                      refine ⟨1834574978958125551193897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19568799775553339212734901 1834574978958125551193897)
                      ·
                        rfl

theorem cell23_3572822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3572822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572822 prefixEnd_3572822 := by exact prefixLift 3572822
  have htrace : WordTrace (prefixWord ++ tailWord_3572822) baseStart_3572822 baseEnd_3572822 := by
    simpa [prefixWord, tailWord_3572822, baseEnd_3572822] using wordTrace_append hprefix tailTrace_3572822
  have hstable : (prefixWord ++ tailWord_3572822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572822).length < 2 ^ (prefixWord ++ tailWord_3572822).sum := by decide
  have hdescent : baseEnd_3572822 < baseStart_3572822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572911 : List Nat := [1, 1, 2, 1, 2, 3, 2, 11]
def baseStart_3572911 : Nat := 118140960795 + 3572911 * 2 ^ 59
def prefixEnd_3572911 : Nat := 4983230072969 + 3 ^ 40 * 3572911 * 2
def baseEnd_3572911 : Nat := 67948914027273174184481

theorem tailTrace_3572911 : CollatzResearch.WordTrace tailWord_3572911 prefixEnd_3572911 67948914027273174184481 := by
  unfold tailWord_3572911
  simp only [CollatzResearch.WordTrace]
  refine ⟨130314769958961126463038587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86876513305974084308692391 130314769958961126463038587)
  ·
    refine ⟨195472154938441689694557881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130314769958961126463038587 195472154938441689694557881)
    ·
      refine ⟨146604116203831267270918411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195472154938441689694557881 146604116203831267270918411)
      ·
        refine ⟨219906174305746900906377617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146604116203831267270918411 219906174305746900906377617)
        ·
          refine ⟨164929630729310175679783213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219906174305746900906377617 164929630729310175679783213)
          ·
            refine ⟨61848611523491315879918705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164929630729310175679783213 61848611523491315879918705)
            ·
              refine ⟨46386458642618486909939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61848611523491315879918705 46386458642618486909939029)
              ·
                refine ⟨67948914027273174184481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46386458642618486909939029 67948914027273174184481)
                ·
                  rfl

theorem cell23_3572911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 11].length) (baseStart_3572911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572911 prefixEnd_3572911 := by exact prefixLift 3572911
  have htrace : WordTrace (prefixWord ++ tailWord_3572911) baseStart_3572911 baseEnd_3572911 := by
    simpa [prefixWord, tailWord_3572911, baseEnd_3572911] using wordTrace_append hprefix tailTrace_3572911
  have hstable : (prefixWord ++ tailWord_3572911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572911).length < 2 ^ (prefixWord ++ tailWord_3572911).sum := by decide
  have hdescent : baseEnd_3572911 < baseStart_3572911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572928 : List Nat := [2, 1, 1, 2, 6, 1, 10]
def baseStart_3572928 : Nat := 118140960795 + 3572928 * 2 ^ 59
def prefixEnd_3572928 : Nat := 4983230072969 + 3 ^ 40 * 3572928 * 2
def baseEnd_3572928 : Nat := 22649745776635828845289

theorem tailTrace_3572928 : CollatzResearch.WordTrace tailWord_3572928 prefixEnd_3572928 22649745776635828845289 := by
  unfold tailWord_3572928
  simp only [CollatzResearch.WordTrace]
  refine ⟨65157694999949769183203719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86876926666599692244271625 65157694999949769183203719)
  ·
    refine ⟨97736542499924653774805579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65157694999949769183203719 97736542499924653774805579)
    ·
      refine ⟨146604813749886980662208369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97736542499924653774805579 146604813749886980662208369)
      ·
        refine ⟨109953610312415235496656277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146604813749886980662208369 109953610312415235496656277)
        ·
          refine ⟨5154075483394464163905763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109953610312415235496656277 5154075483394464163905763)
          ·
            refine ⟨7731113225091696245858645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154075483394464163905763 7731113225091696245858645)
            ·
              refine ⟨22649745776635828845289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7731113225091696245858645 22649745776635828845289)
              ·
                rfl

theorem cell23_3572928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 10].length) (baseStart_3572928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572928 prefixEnd_3572928 := by exact prefixLift 3572928
  have htrace : WordTrace (prefixWord ++ tailWord_3572928) baseStart_3572928 baseEnd_3572928 := by
    simpa [prefixWord, tailWord_3572928, baseEnd_3572928] using wordTrace_append hprefix tailTrace_3572928
  have hstable : (prefixWord ++ tailWord_3572928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572928).length < 2 ^ (prefixWord ++ tailWord_3572928).sum := by decide
  have hdescent : baseEnd_3572928 < baseStart_3572928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572932 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3572932 : Nat := 118140960795 + 3572932 * 2 ^ 59
def prefixEnd_3572932 : Nat := 4983230072969 + 3 ^ 40 * 3572932 * 2
def baseEnd_3572932 : Nat := 611543820610040040272797

theorem tailTrace_3572932 : CollatzResearch.WordTrace tailWord_3572932 prefixEnd_3572932 611543820610040040272797 := by
  unfold tailWord_3572932
  simp only [CollatzResearch.WordTrace]
  refine ⟨65157767945942523524776525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86877023927923364699702033 65157767945942523524776525)
  ·
    refine ⟨24434162979728446321791197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65157767945942523524776525 24434162979728446321791197)
    ·
      refine ⟨9162811117398167370671699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24434162979728446321791197 9162811117398167370671699)
      ·
        refine ⟨13744216676097251056007549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9162811117398167370671699 13744216676097251056007549)
        ·
          refine ⟨5154081253536469146002831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13744216676097251056007549 5154081253536469146002831)
          ·
            refine ⟨7731121880304703719004247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154081253536469146002831 7731121880304703719004247)
            ·
              refine ⟨11596682820457055578506371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731121880304703719004247 11596682820457055578506371)
              ·
                refine ⟨17395024230685583367759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11596682820457055578506371 17395024230685583367759557)
                ·
                  refine ⟨3261567043253546881454917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17395024230685583367759557 3261567043253546881454917)
                  ·
                    refine ⟨611543820610040040272797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261567043253546881454917 611543820610040040272797)
                    ·
                      rfl

theorem cell23_3572932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3572932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572932 prefixEnd_3572932 := by exact prefixLift 3572932
  have htrace : WordTrace (prefixWord ++ tailWord_3572932) baseStart_3572932 baseEnd_3572932 := by
    simpa [prefixWord, tailWord_3572932, baseEnd_3572932] using wordTrace_append hprefix tailTrace_3572932
  have hstable : (prefixWord ++ tailWord_3572932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572932).length < 2 ^ (prefixWord ++ tailWord_3572932).sum := by decide
  have hdescent : baseEnd_3572932 < baseStart_3572932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572949 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3572949 : Nat := 118140960795 + 3572949 * 2 ^ 59
def prefixEnd_3572949 : Nat := 4983230072969 + 3 ^ 40 * 3572949 * 2
def baseEnd_3572949 : Nat := 611546730333748851435271

theorem tailTrace_3572949 : CollatzResearch.WordTrace tailWord_3572949 prefixEnd_3572949 611546730333748851435271 := by
  unfold tailWord_3572949
  simp only [CollatzResearch.WordTrace]
  refine ⟨130316155932823458952921901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86877437288548972635281267 130316155932823458952921901)
  ·
    refine ⟨48868558474808797107345713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130316155932823458952921901 48868558474808797107345713)
    ·
      refine ⟨36651418856106597830509285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48868558474808797107345713 36651418856106597830509285)
      ·
        refine ⟨6872141035519987093220491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36651418856106597830509285 6872141035519987093220491)
        ·
          refine ⟨10308211553279980639830737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6872141035519987093220491 10308211553279980639830737)
          ·
            refine ⟨7731158664959985479873053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10308211553279980639830737 7731158664959985479873053)
            ·
              refine ⟨2899184499359994554952395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7731158664959985479873053 2899184499359994554952395)
              ·
                refine ⟨4348776749039991832428593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899184499359994554952395 4348776749039991832428593)
                ·
                  refine ⟨3261582561779993874321445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348776749039991832428593 3261582561779993874321445)
                  ·
                    refine ⟨611546730333748851435271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261582561779993874321445 611546730333748851435271)
                    ·
                      rfl

theorem cell23_3572949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3572949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572949 prefixEnd_3572949 := by exact prefixLift 3572949
  have htrace : WordTrace (prefixWord ++ tailWord_3572949) baseStart_3572949 baseEnd_3572949 := by
    simpa [prefixWord, tailWord_3572949, baseEnd_3572949] using wordTrace_append hprefix tailTrace_3572949
  have hstable : (prefixWord ++ tailWord_3572949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572949).length < 2 ^ (prefixWord ++ tailWord_3572949).sum := by decide
  have hdescent : baseEnd_3572949 < baseStart_3572949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572952 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3572952 : Nat := 118140960795 + 3572952 * 2 ^ 59
def prefixEnd_3572952 : Nat := 4983230072969 + 3 ^ 40 * 3572952 * 2
def baseEnd_3572952 : Nat := 1834641731443210042568299

theorem tailTrace_3572952 : CollatzResearch.WordTrace tailWord_3572952 prefixEnd_3572952 1834641731443210042568299 := by
  unfold tailWord_3572952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65158132675906295232640555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86877510234541726976854073 65158132675906295232640555)
  ·
    refine ⟨97737199013859442848960833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65158132675906295232640555 97737199013859442848960833)
    ·
      refine ⟨73302899260394582136720625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97737199013859442848960833 73302899260394582136720625)
      ·
        refine ⟨54977174445295936602540469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73302899260394582136720625 54977174445295936602540469)
        ·
          refine ⟨5154110104246494056488169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54977174445295936602540469 5154110104246494056488169)
          ·
            refine ⟨3865582578184870542366127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154110104246494056488169 3865582578184870542366127)
            ·
              refine ⟨5798373867277305813549191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865582578184870542366127 5798373867277305813549191)
              ·
                refine ⟨8697560800915958720323787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798373867277305813549191 8697560800915958720323787)
                ·
                  refine ⟨13046341201373938080485681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697560800915958720323787 13046341201373938080485681)
                  ·
                    refine ⟨9784755901030453560364261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13046341201373938080485681 9784755901030453560364261)
                    ·
                      refine ⟨1834641731443210042568299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9784755901030453560364261 1834641731443210042568299)
                      ·
                        rfl

theorem cell23_3572952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3572952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572952 prefixEnd_3572952 := by exact prefixLift 3572952
  have htrace : WordTrace (prefixWord ++ tailWord_3572952) baseStart_3572952 baseEnd_3572952 := by
    simpa [prefixWord, tailWord_3572952, baseEnd_3572952] using wordTrace_append hprefix tailTrace_3572952
  have hstable : (prefixWord ++ tailWord_3572952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572952).length < 2 ^ (prefixWord ++ tailWord_3572952).sum := by decide
  have hdescent : baseEnd_3572952 < baseStart_3572952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572968 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3572968 : Nat := 118140960795 + 3572968 * 2 ^ 59
def prefixEnd_3572968 : Nat := 4983230072969 + 3 ^ 40 * 3572968 * 2
def baseEnd_3572968 : Nat := 1834649947133681979968225

theorem tailTrace_3572968 : CollatzResearch.WordTrace tailWord_3572968 prefixEnd_3572968 1834649947133681979968225 := by
  unfold tailWord_3572968
  simp only [CollatzResearch.WordTrace]
  refine ⟨65158424459877312598931779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86877899279836416798575705 65158424459877312598931779)
  ·
    refine ⟨97737636689815968898397669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65158424459877312598931779 97737636689815968898397669)
    ·
      refine ⟨18325806879340494168449563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97737636689815968898397669 18325806879340494168449563)
      ·
        refine ⟨27488710319010741252674345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325806879340494168449563 27488710319010741252674345)
        ·
          refine ⟨20616532739258055939505759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27488710319010741252674345 20616532739258055939505759)
          ·
            refine ⟨30924799108887083909258639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20616532739258055939505759 30924799108887083909258639)
            ·
              refine ⟨46387198663330625863887959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30924799108887083909258639 46387198663330625863887959)
              ·
                refine ⟨69580797994995938795831939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46387198663330625863887959 69580797994995938795831939)
                ·
                  refine ⟨104371196992493908193747909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69580797994995938795831939 104371196992493908193747909)
                  ·
                    refine ⟨19569599436092607786327733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104371196992493908193747909 19569599436092607786327733)
                    ·
                      refine ⟨1834649947133681979968225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19569599436092607786327733 1834649947133681979968225)
                      ·
                        rfl

theorem cell23_3572968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3572968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572968 prefixEnd_3572968 := by exact prefixLift 3572968
  have htrace : WordTrace (prefixWord ++ tailWord_3572968) baseStart_3572968 baseEnd_3572968 := by
    simpa [prefixWord, tailWord_3572968, baseEnd_3572968] using wordTrace_append hprefix tailTrace_3572968
  have hstable : (prefixWord ++ tailWord_3572968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572968).length < 2 ^ (prefixWord ++ tailWord_3572968).sum := by decide
  have hdescent : baseEnd_3572968 < baseStart_3572968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572973 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3572973 : Nat := 118140960795 + 3572973 * 2 ^ 59
def prefixEnd_3572973 : Nat := 4983230072969 + 3 ^ 40 * 3572973 * 2
def baseEnd_3572973 : Nat := 1834652514536954460405703

theorem tailTrace_3572973 : CollatzResearch.WordTrace tailWord_3572973 prefixEnd_3572973 1834652514536954460405703 := by
  unfold tailWord_3572973
  simp only [CollatzResearch.WordTrace]
  refine ⟨130317031284736511051795573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86878020856491007367863715 130317031284736511051795573)
  ·
    refine ⟨12217221682944047911105835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130317031284736511051795573 12217221682944047911105835)
    ·
      refine ⟨18325832524416071866658753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217221682944047911105835 18325832524416071866658753)
      ·
        refine ⟨13744374393312053899994065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18325832524416071866658753 13744374393312053899994065)
        ·
          refine ⟨10308280794984040424995549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13744374393312053899994065 10308280794984040424995549)
          ·
            refine ⟨3865605298119015159373331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10308280794984040424995549 3865605298119015159373331)
            ·
              refine ⟨5798407947178522739059997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865605298119015159373331 5798407947178522739059997)
              ·
                refine ⟨2174402980191946027147499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5798407947178522739059997 2174402980191946027147499)
                ·
                  refine ⟨3261604470287919040721249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174402980191946027147499 3261604470287919040721249)
                  ·
                    refine ⟨2446203352715939280540937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3261604470287919040721249 2446203352715939280540937)
                    ·
                      refine ⟨1834652514536954460405703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446203352715939280540937 1834652514536954460405703)
                      ·
                        rfl

theorem cell23_3572973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3572973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572973 prefixEnd_3572973 := by exact prefixLift 3572973
  have htrace : WordTrace (prefixWord ++ tailWord_3572973) baseStart_3572973 baseEnd_3572973 := by
    simpa [prefixWord, tailWord_3572973, baseEnd_3572973] using wordTrace_append hprefix tailTrace_3572973
  have hstable : (prefixWord ++ tailWord_3572973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572973).length < 2 ^ (prefixWord ++ tailWord_3572973).sum := by decide
  have hdescent : baseEnd_3572973 < baseStart_3572973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572982 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3572982 : Nat := 118140960795 + 3572982 * 2 ^ 59
def prefixEnd_3572982 : Nat := 4983230072969 + 3 ^ 40 * 3572982 * 2
def baseEnd_3572982 : Nat := 1834657135862844925193161

theorem tailTrace_3572982 : CollatzResearch.WordTrace tailWord_3572982 prefixEnd_3572982 1834657135862844925193161 := by
  unfold tailWord_3572982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144834971356494099304575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86878239694469270392582133 8144834971356494099304575)
  ·
    refine ⟨12217252457034741148956863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8144834971356494099304575 12217252457034741148956863)
    ·
      refine ⟨18325878685552111723435295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217252457034741148956863 18325878685552111723435295)
      ·
        refine ⟨27488818028328167585152943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325878685552111723435295 27488818028328167585152943)
        ·
          refine ⟨41233227042492251377729415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488818028328167585152943 41233227042492251377729415)
          ·
            refine ⟨61849840563738377066594123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41233227042492251377729415 61849840563738377066594123)
            ·
              refine ⟨92774760845607565599891185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61849840563738377066594123 92774760845607565599891185)
              ·
                refine ⟨69581070634205674199918389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92774760845607565599891185 69581070634205674199918389)
                ·
                  refine ⟨6523225371956781956242349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69581070634205674199918389 6523225371956781956242349)
                  ·
                    refine ⟨2446209514483793233590881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6523225371956781956242349 2446209514483793233590881)
                    ·
                      refine ⟨1834657135862844925193161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446209514483793233590881 1834657135862844925193161)
                      ·
                        rfl

theorem cell23_3572982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3572982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3572982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3572982 prefixEnd_3572982 := by exact prefixLift 3572982
  have htrace : WordTrace (prefixWord ++ tailWord_3572982) baseStart_3572982 baseEnd_3572982 := by
    simpa [prefixWord, tailWord_3572982, baseEnd_3572982] using wordTrace_append hprefix tailTrace_3572982
  have hstable : (prefixWord ++ tailWord_3572982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572982).length < 2 ^ (prefixWord ++ tailWord_3572982).sum := by decide
  have hdescent : baseEnd_3572982 < baseStart_3572982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573006 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3573006 : Nat := 118140960795 + 3573006 * 2 ^ 59
def prefixEnd_3573006 : Nat := 4983230072969 + 3 ^ 40 * 3573006 * 2
def baseEnd_3573006 : Nat := 1834669459398552831293051

theorem tailTrace_3573006 : CollatzResearch.WordTrace tailWord_3573006 prefixEnd_3573006 1834669459398552831293051 := by
  unfold tailWord_3573006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289779361702119710968359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86878823262411305125164581 16289779361702119710968359)
  ·
    refine ⟨24434669042553179566452539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16289779361702119710968359 24434669042553179566452539)
    ·
      refine ⟨36652003563829769349678809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24434669042553179566452539 36652003563829769349678809)
      ·
        refine ⟨27489002672872327012259107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36652003563829769349678809 27489002672872327012259107)
        ·
          refine ⟨41233504009308490518388661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27489002672872327012259107 41233504009308490518388661)
          ·
            refine ⟨3865641000872670986098937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41233504009308490518388661 3865641000872670986098937)
            ·
              refine ⟨2899230750654503239574203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865641000872670986098937 2899230750654503239574203)
              ·
                refine ⟨4348846125981754859361305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899230750654503239574203 4348846125981754859361305)
                ·
                  refine ⟨3261634594486316144520979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348846125981754859361305 3261634594486316144520979)
                  ·
                    refine ⟨4892451891729474216781469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3261634594486316144520979 4892451891729474216781469)
                    ·
                      refine ⟨1834669459398552831293051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4892451891729474216781469 1834669459398552831293051)
                      ·
                        rfl

theorem cell23_3573006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3573006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573006 prefixEnd_3573006 := by exact prefixLift 3573006
  have htrace : WordTrace (prefixWord ++ tailWord_3573006) baseStart_3573006 baseEnd_3573006 := by
    simpa [prefixWord, tailWord_3573006, baseEnd_3573006] using wordTrace_append hprefix tailTrace_3573006
  have hstable : (prefixWord ++ tailWord_3573006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573006).length < 2 ^ (prefixWord ++ tailWord_3573006).sum := by decide
  have hdescent : baseEnd_3573006 < baseStart_3573006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573008 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_3573008 : Nat := 118140960795 + 3573008 * 2 ^ 59
def prefixEnd_3573008 : Nat := 4983230072969 + 3 ^ 40 * 3573008 * 2
def baseEnd_3573008 : Nat := 1834670486359861823468041

theorem tailTrace_3573008 : CollatzResearch.WordTrace tailWord_3573008 prefixEnd_3573008 1834670486359861823468041 := by
  unfold tailWord_3573008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159153919804856014659839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86878871893073141352879785 65159153919804856014659839)
  ·
    refine ⟨97738730879707284021989759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65159153919804856014659839 97738730879707284021989759)
    ·
      refine ⟨146608096319560926032984639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97738730879707284021989759 146608096319560926032984639)
      ·
        refine ⟨219912144479341389049476959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146608096319560926032984639 219912144479341389049476959)
        ·
          refine ⟨329868216719012083574215439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219912144479341389049476959 329868216719012083574215439)
          ·
            refine ⟨494802325078518125361323159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329868216719012083574215439 494802325078518125361323159)
            ·
              refine ⟨742203487617777188041984739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494802325078518125361323159 742203487617777188041984739)
              ·
                refine ⟨1113305231426665782062977109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742203487617777188041984739 1113305231426665782062977109)
                ·
                  refine ⟨13046545680781239633550513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1113305231426665782062977109 13046545680781239633550513)
                  ·
                    refine ⟨9784909260585929725162885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13046545680781239633550513 9784909260585929725162885)
                    ·
                      refine ⟨1834670486359861823468041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9784909260585929725162885 1834670486359861823468041)
                      ·
                        rfl

theorem cell23_3573008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_3573008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573008 prefixEnd_3573008 := by exact prefixLift 3573008
  have htrace : WordTrace (prefixWord ++ tailWord_3573008) baseStart_3573008 baseEnd_3573008 := by
    simpa [prefixWord, tailWord_3573008, baseEnd_3573008] using wordTrace_append hprefix tailTrace_3573008
  have hstable : (prefixWord ++ tailWord_3573008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573008).length < 2 ^ (prefixWord ++ tailWord_3573008).sum := by decide
  have hdescent : baseEnd_3573008 < baseStart_3573008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573048 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_3573048 : Nat := 118140960795 + 3573048 * 2 ^ 59
def prefixEnd_3573048 : Nat := 4983230072969 + 3 ^ 40 * 3573048 * 2
def baseEnd_3573048 : Nat := 611563675195347222322619

theorem tailTrace_3573048 : CollatzResearch.WordTrace tailWord_3573048 prefixEnd_3573048 611563675195347222322619 := by
  unfold tailWord_3573048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159883379732399430387899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86879844506309865907183865 65159883379732399430387899)
  ·
    refine ⟨97739825069598599145581849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65159883379732399430387899 97739825069598599145581849)
    ·
      refine ⟨73304868802198949359186387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97739825069598599145581849 73304868802198949359186387)
      ·
        refine ⟨109957303203298424038779581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73304868802198949359186387 109957303203298424038779581)
        ·
          refine ⟨41233988701236909014542343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109957303203298424038779581 41233988701236909014542343)
          ·
            refine ⟨61850983051855363521813515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41233988701236909014542343 61850983051855363521813515)
            ·
              refine ⟨92776474577783045282720273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61850983051855363521813515 92776474577783045282720273)
              ·
                refine ⟨69582355933337283962040205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92776474577783045282720273 69582355933337283962040205)
                ·
                  refine ⟨26093383475001481485765077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69582355933337283962040205 26093383475001481485765077)
                  ·
                    refine ⟨611563675195347222322619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26093383475001481485765077 611563675195347222322619)
                    ·
                      rfl

theorem cell23_3573048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_3573048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573048 prefixEnd_3573048 := by exact prefixLift 3573048
  have htrace : WordTrace (prefixWord ++ tailWord_3573048) baseStart_3573048 baseEnd_3573048 := by
    simpa [prefixWord, tailWord_3573048, baseEnd_3573048] using wordTrace_append hprefix tailTrace_3573048
  have hstable : (prefixWord ++ tailWord_3573048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573048).length < 2 ^ (prefixWord ++ tailWord_3573048).sum := by decide
  have hdescent : baseEnd_3573048 < baseStart_3573048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573052 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 5]
def baseStart_3573052 : Nat := 118140960795 + 3573052 * 2 ^ 59
def prefixEnd_3573052 : Nat := 4983230072969 + 3 ^ 40 * 3573052 * 2
def baseEnd_3573052 : Nat := 203854786612073294590871

theorem tailTrace_3573052 : CollatzResearch.WordTrace tailWord_3573052 prefixEnd_3573052 203854786612073294590871 := by
  unfold tailWord_3573052
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159956325725153771960705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86879941767633538362614273 65159956325725153771960705)
  ·
    refine ⟨48869967244293865328970529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65159956325725153771960705 48869967244293865328970529)
    ·
      refine ⟨36652475433220398996727897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48869967244293865328970529 36652475433220398996727897)
      ·
        refine ⟨27489356574915299247545923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36652475433220398996727897 27489356574915299247545923)
        ·
          refine ⟨41234034862372948871318885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27489356574915299247545923 41234034862372948871318885)
          ·
            refine ⟨7731381536694927913372291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41234034862372948871318885 7731381536694927913372291)
            ·
              refine ⟨11597072305042391870058437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731381536694927913372291 11597072305042391870058437)
              ·
                refine ⟨2174451057195448475635957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11597072305042391870058437 2174451057195448475635957)
                ·
                  refine ⟨203854786612073294590871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174451057195448475635957 203854786612073294590871)
                  ·
                    rfl

theorem cell23_3573052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_3573052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573052 prefixEnd_3573052 := by exact prefixLift 3573052
  have htrace : WordTrace (prefixWord ++ tailWord_3573052) baseStart_3573052 baseEnd_3573052 := by
    simpa [prefixWord, tailWord_3573052, baseEnd_3573052] using wordTrace_append hprefix tailTrace_3573052
  have hstable : (prefixWord ++ tailWord_3573052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573052).length < 2 ^ (prefixWord ++ tailWord_3573052).sum := by decide
  have hdescent : baseEnd_3573052 < baseStart_3573052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573069 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3573069 : Nat := 118140960795 + 3573069 * 2 ^ 59
def prefixEnd_3573069 : Nat := 4983230072969 + 3 ^ 40 * 3573069 * 2
def baseEnd_3573069 : Nat := 203855756519976231645029

theorem tailTrace_3573069 : CollatzResearch.WordTrace tailWord_3573069 prefixEnd_3573069 203855756519976231645029 := by
  unfold tailWord_3573069
  simp only [CollatzResearch.WordTrace]
  refine ⟨130320532692388719447290261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86880355128259146298193507 130320532692388719447290261)
  ·
    refine ⟨6108774969955721224091731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130320532692388719447290261 6108774969955721224091731)
    ·
      refine ⟨9163162454933581836137597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108774969955721224091731 9163162454933581836137597)
      ·
        refine ⟨3436185920600093188551599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9163162454933581836137597 3436185920600093188551599)
        ·
          refine ⟨5154278880900139782827399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436185920600093188551599 5154278880900139782827399)
          ·
            refine ⟨7731418321350209674241099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154278880900139782827399 7731418321350209674241099)
            ·
              refine ⟨11597127482025314511361649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731418321350209674241099 11597127482025314511361649)
              ·
                refine ⟨8697845611518985883521237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11597127482025314511361649 8697845611518985883521237)
                ·
                  refine ⟨203855756519976231645029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8697845611518985883521237 203855756519976231645029)
                  ·
                    rfl

theorem cell23_3573069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3573069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573069 prefixEnd_3573069 := by exact prefixLift 3573069
  have htrace : WordTrace (prefixWord ++ tailWord_3573069) baseStart_3573069 baseEnd_3573069 := by
    simpa [prefixWord, tailWord_3573069, baseEnd_3573069] using wordTrace_append hprefix tailTrace_3573069
  have hstable : (prefixWord ++ tailWord_3573069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573069).length < 2 ^ (prefixWord ++ tailWord_3573069).sum := by decide
  have hdescent : baseEnd_3573069 < baseStart_3573069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573125 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 6]
def baseStart_3573125 : Nat := 118140960795 + 3573125 * 2 ^ 59
def prefixEnd_3573125 : Nat := 4983230072969 + 3 ^ 40 * 3573125 * 2
def baseEnd_3573125 : Nat := 203858951510715318411667

theorem tailTrace_3573125 : CollatzResearch.WordTrace tailWord_3573125 prefixEnd_3573125 203858951510715318411667 := by
  unfold tailWord_3573125
  simp only [CollatzResearch.WordTrace]
  refine ⟨130322575180185841011328829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86881716786790560674219219 130322575180185841011328829)
  ·
    refine ⟨48870965692569690379248311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130322575180185841011328829 48870965692569690379248311)
    ·
      refine ⟨73306448538854535568872467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48870965692569690379248311 73306448538854535568872467)
      ·
        refine ⟨109959672808281803353308701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73306448538854535568872467 109959672808281803353308701)
        ·
          refine ⟨41234877303105676257490763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109959672808281803353308701 41234877303105676257490763)
          ·
            refine ⟨61852315954658514386236145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41234877303105676257490763 61852315954658514386236145)
            ·
              refine ⟨46389236965993885789677109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61852315954658514386236145 46389236965993885789677109)
              ·
                refine ⟨4348990965561926792782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46389236965993885789677109 4348990965561926792782229)
                ·
                  refine ⟨203858951510715318411667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4348990965561926792782229 203858951510715318411667)
                  ·
                    rfl

theorem cell23_3573125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_3573125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573125 prefixEnd_3573125 := by exact prefixLift 3573125
  have htrace : WordTrace (prefixWord ++ tailWord_3573125) baseStart_3573125 baseEnd_3573125 := by
    simpa [prefixWord, tailWord_3573125, baseEnd_3573125] using wordTrace_append hprefix tailTrace_3573125
  have hstable : (prefixWord ++ tailWord_3573125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573125).length < 2 ^ (prefixWord ++ tailWord_3573125).sum := by decide
  have hdescent : baseEnd_3573125 < baseStart_3573125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573192 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3573192 : Nat := 118140960795 + 3573192 * 2 ^ 59
def prefixEnd_3573192 : Nat := 4983230072969 + 3 ^ 40 * 3573192 * 2
def baseEnd_3573192 : Nat := 1834764966800289103567195

theorem tailTrace_3573192 : CollatzResearch.WordTrace tailWord_3573192 prefixEnd_3573192 1834764966800289103567195 := by
  unfold tailWord_3573192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65162509435471555727008915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86883345913962074302678553 65162509435471555727008915)
  ·
    refine ⟨97743764153207333590513373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65162509435471555727008915 97743764153207333590513373)
    ·
      refine ⟨36653911557452750096442515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97743764153207333590513373 36653911557452750096442515)
      ·
        refine ⟨54980867336179125144663773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36653911557452750096442515 54980867336179125144663773)
        ·
          refine ⟨20617825251067171929248915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54980867336179125144663773 20617825251067171929248915)
          ·
            refine ⟨30926737876600757893873373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20617825251067171929248915 30926737876600757893873373)
            ·
              refine ⟨11597526703725284210202515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30926737876600757893873373 11597526703725284210202515)
              ·
                refine ⟨17396290055587926315303773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11597526703725284210202515 17396290055587926315303773)
                ·
                  refine ⟨6523608770845472368238915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17396290055587926315303773 6523608770845472368238915)
                  ·
                    refine ⟨9785413156268208552358373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6523608770845472368238915 9785413156268208552358373)
                    ·
                      refine ⟨1834764966800289103567195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9785413156268208552358373 1834764966800289103567195)
                      ·
                        rfl

theorem cell23_3573192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3573192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573192 prefixEnd_3573192 := by exact prefixLift 3573192
  have htrace : WordTrace (prefixWord ++ tailWord_3573192) baseStart_3573192 baseEnd_3573192 := by
    simpa [prefixWord, tailWord_3573192, baseEnd_3573192] using wordTrace_append hprefix tailTrace_3573192
  have hstable : (prefixWord ++ tailWord_3573192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573192).length < 2 ^ (prefixWord ++ tailWord_3573192).sum := by decide
  have hdescent : baseEnd_3573192 < baseStart_3573192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573195 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_3573195 : Nat := 118140960795 + 3573195 * 2 ^ 59
def prefixEnd_3573195 : Nat := 4983230072969 + 3 ^ 40 * 3573195 * 2
def baseEnd_3573195 : Nat := 1834766507242252591829681

theorem tailTrace_3573195 : CollatzResearch.WordTrace tailWord_3573195 prefixEnd_3573195 1834766507242252591829681 := by
  unfold tailWord_3573195
  simp only [CollatzResearch.WordTrace]
  refine ⟨130325128289932242966377039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86883418859954828644251359 130325128289932242966377039)
  ·
    refine ⟨195487692434898364449565559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130325128289932242966377039 195487692434898364449565559)
    ·
      refine ⟨293231538652347546674348339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195487692434898364449565559 293231538652347546674348339)
      ·
        refine ⟨439847307978521320011522509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293231538652347546674348339 439847307978521320011522509)
        ·
          refine ⟨164942740491945495004320941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439847307978521320011522509 164942740491945495004320941)
          ·
            refine ⟨61853527684479560626620353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164942740491945495004320941 61853527684479560626620353)
            ·
              refine ⟨46390145763359670469965265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61853527684479560626620353 46390145763359670469965265)
              ·
                refine ⟨34792609322519752852473949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46390145763359670469965265 34792609322519752852473949)
                ·
                  refine ⟨13047228495944907319677731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34792609322519752852473949 13047228495944907319677731)
                  ·
                    refine ⟨19570842743917360979516597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13047228495944907319677731 19570842743917360979516597)
                    ·
                      refine ⟨1834766507242252591829681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19570842743917360979516597 1834766507242252591829681)
                      ·
                        rfl

theorem cell23_3573195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_3573195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573195 prefixEnd_3573195 := by exact prefixLift 3573195
  have htrace : WordTrace (prefixWord ++ tailWord_3573195) baseStart_3573195 baseEnd_3573195 := by
    simpa [prefixWord, tailWord_3573195, baseEnd_3573195] using wordTrace_append hprefix tailTrace_3573195
  have hstable : (prefixWord ++ tailWord_3573195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573195).length < 2 ^ (prefixWord ++ tailWord_3573195).sum := by decide
  have hdescent : baseEnd_3573195 < baseStart_3573195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573196 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3573196 : Nat := 118140960795 + 3573196 * 2 ^ 59
def prefixEnd_3573196 : Nat := 4983230072969 + 3 ^ 40 * 3573196 * 2
def baseEnd_3573196 : Nat := 1834767020722907087917177

theorem tailTrace_3573196 : CollatzResearch.WordTrace tailWord_3573196 prefixEnd_3573196 1834767020722907087917177 := by
  unfold tailWord_3573196
  simp only [CollatzResearch.WordTrace]
  refine ⟨65162582381464310068581721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86883443175285746758108961 65162582381464310068581721)
  ·
    refine ⟨48871936786098232551436291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65162582381464310068581721 48871936786098232551436291)
    ·
      refine ⟨73307905179147348827154437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48871936786098232551436291 73307905179147348827154437)
      ·
        refine ⟨13745232221090127905091457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73307905179147348827154437 13745232221090127905091457)
        ·
          refine ⟨10308924165817595928818593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13745232221090127905091457 10308924165817595928818593)
          ·
            refine ⟨7731693124363196946613945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10308924165817595928818593 7731693124363196946613945)
            ·
              refine ⟨5798769843272397709960459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731693124363196946613945 5798769843272397709960459)
              ·
                refine ⟨8698154764908596564940689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798769843272397709960459 8698154764908596564940689)
                ·
                  refine ⟨6523616073681447423705517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698154764908596564940689 6523616073681447423705517)
                  ·
                    refine ⟨2446356027630542783889569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6523616073681447423705517 2446356027630542783889569)
                    ·
                      refine ⟨1834767020722907087917177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446356027630542783889569 1834767020722907087917177)
                      ·
                        rfl

theorem cell23_3573196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3573196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573196 prefixEnd_3573196 := by exact prefixLift 3573196
  have htrace : WordTrace (prefixWord ++ tailWord_3573196) baseStart_3573196 baseEnd_3573196 := by
    simpa [prefixWord, tailWord_3573196, baseEnd_3573196] using wordTrace_append hprefix tailTrace_3573196
  have hstable : (prefixWord ++ tailWord_3573196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573196).length < 2 ^ (prefixWord ++ tailWord_3573196).sum := by decide
  have hdescent : baseEnd_3573196 < baseStart_3573196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573219 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 2, 4]
def baseStart_3573219 : Nat := 118140960795 + 3573219 * 2 ^ 59
def prefixEnd_3573219 : Nat := 4983230072969 + 3 ^ 40 * 3573219 * 2
def baseEnd_3573219 : Nat := 611592943592653499309857

theorem tailTrace_3573219 : CollatzResearch.WordTrace tailWord_3573219 prefixEnd_3573219 611592943592653499309857 := by
  unfold tailWord_3573219
  simp only [CollatzResearch.WordTrace]
  refine ⟨130326003641845295065250711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86884002427896863376833807 130326003641845295065250711)
  ·
    refine ⟨195489005462767942597876067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130326003641845295065250711 195489005462767942597876067)
    ·
      refine ⟨293233508194151913896814101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195489005462767942597876067 293233508194151913896814101)
      ·
        refine ⟨13745320696600870963913161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293233508194151913896814101 13745320696600870963913161)
        ·
          refine ⟨10308990522450653222934871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13745320696600870963913161 10308990522450653222934871)
          ·
            refine ⟨15463485783675979834402307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308990522450653222934871 15463485783675979834402307)
            ·
              refine ⟨23195228675513969751603461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15463485783675979834402307 23195228675513969751603461)
              ·
                refine ⟨4349105376658869328425649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23195228675513969751603461 4349105376658869328425649)
                ·
                  refine ⟨3261829032494151996319237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4349105376658869328425649 3261829032494151996319237)
                  ·
                    refine ⟨611592943592653499309857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261829032494151996319237 611592943592653499309857)
                    ·
                      rfl

theorem cell23_3573219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 4].length) (baseStart_3573219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573219 prefixEnd_3573219 := by exact prefixLift 3573219
  have htrace : WordTrace (prefixWord ++ tailWord_3573219) baseStart_3573219 baseEnd_3573219 := by
    simpa [prefixWord, tailWord_3573219, baseEnd_3573219] using wordTrace_append hprefix tailTrace_3573219
  have hstable : (prefixWord ++ tailWord_3573219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573219).length < 2 ^ (prefixWord ++ tailWord_3573219).sum := by decide
  have hdescent : baseEnd_3573219 < baseStart_3573219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573232 : List Nat := [2, 1, 1, 1, 3, 6, 1, 8]
def baseStart_3573232 : Nat := 118140960795 + 3573232 * 2 ^ 59
def prefixEnd_3573232 : Nat := 4983230072969 + 3 ^ 40 * 3573232 * 2
def baseEnd_3573232 : Nat := 67955018741721072113593

theorem tailTrace_3573232 : CollatzResearch.WordTrace tailWord_3573232 prefixEnd_3573232 67955018741721072113593 := by
  unfold tailWord_3573232
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163238895399099142736975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86884318527198798856982633 65163238895399099142736975)
  ·
    refine ⟨97744858343098648714105463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65163238895399099142736975 97744858343098648714105463)
    ·
      refine ⟨146617287514647973071158195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97744858343098648714105463 146617287514647973071158195)
      ·
        refine ⟨219925931271971959606737293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146617287514647973071158195 219925931271971959606737293)
        ·
          refine ⟨82472224226989484852526485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219925931271971959606737293 82472224226989484852526485)
          ·
            refine ⟨3865885510640132102462179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82472224226989484852526485 3865885510640132102462179)
            ·
              refine ⟨5798828265960198153693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865885510640132102462179 5798828265960198153693269)
              ·
                refine ⟨67955018741721072113593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5798828265960198153693269 67955018741721072113593)
                ·
                  rfl

theorem cell23_3573232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_3573232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573232 prefixEnd_3573232 := by exact prefixLift 3573232
  have htrace : WordTrace (prefixWord ++ tailWord_3573232) baseStart_3573232 baseEnd_3573232 := by
    simpa [prefixWord, tailWord_3573232, baseEnd_3573232] using wordTrace_append hprefix tailTrace_3573232
  have hstable : (prefixWord ++ tailWord_3573232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573232).length < 2 ^ (prefixWord ++ tailWord_3573232).sum := by decide
  have hdescent : baseEnd_3573232 < baseStart_3573232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573249 : List Nat := [1, 2, 4, 1, 4, 1, 3, 7]
def baseStart_3573249 : Nat := 118140960795 + 3573249 * 2 ^ 59
def prefixEnd_3573249 : Nat := 4983230072969 + 3 ^ 40 * 3573249 * 2
def baseEnd_3573249 : Nat := 67955342044355384464979

theorem tailTrace_3573249 : CollatzResearch.WordTrace tailWord_3573249 prefixEnd_3573249 67955342044355384464979 := by
  unfold tailWord_3573249
  simp only [CollatzResearch.WordTrace]
  refine ⟨130327097831736610188842801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86884731887824406792561867 130327097831736610188842801)
  ·
    refine ⟨97745323373802457641632101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130327097831736610188842801 97745323373802457641632101)
    ·
      refine ⟨18327248132587960807806019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97745323373802457641632101 18327248132587960807806019)
      ·
        refine ⟨27490872198881941211709029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327248132587960807806019 27490872198881941211709029)
        ·
          refine ⟨5154538537290363977195443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27490872198881941211709029 5154538537290363977195443)
          ·
            refine ⟨7731807805935545965793165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154538537290363977195443 7731807805935545965793165)
            ·
              refine ⟨2899427927225829737172437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7731807805935545965793165 2899427927225829737172437)
              ·
                refine ⟨67955342044355384464979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899427927225829737172437 67955342044355384464979)
                ·
                  rfl

theorem cell23_3573249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 7].length) (baseStart_3573249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573249 prefixEnd_3573249 := by exact prefixLift 3573249
  have htrace : WordTrace (prefixWord ++ tailWord_3573249) baseStart_3573249 baseEnd_3573249 := by
    simpa [prefixWord, tailWord_3573249, baseEnd_3573249] using wordTrace_append hprefix tailTrace_3573249
  have hstable : (prefixWord ++ tailWord_3573249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573249).length < 2 ^ (prefixWord ++ tailWord_3573249).sum := by decide
  have hdescent : baseEnd_3573249 < baseStart_3573249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573254 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3573254 : Nat := 118140960795 + 3573254 * 2 ^ 59
def prefixEnd_3573254 : Nat := 4983230072969 + 3 ^ 40 * 3573254 * 2
def baseEnd_3573254 : Nat := 1834796802600867860991911

theorem tailTrace_3573254 : CollatzResearch.WordTrace tailWord_3573254 prefixEnd_3573254 1834796802600867860991911 := by
  unfold tailWord_3573254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072727506147453001336713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86884853464478997361849877 4072727506147453001336713)
  ·
    refine ⟨3054545629610589751002535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4072727506147453001336713 3054545629610589751002535)
    ·
      refine ⟨4581818444415884626503803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054545629610589751002535 4581818444415884626503803)
      ·
        refine ⟨6872727666623826939755705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581818444415884626503803 6872727666623826939755705)
        ·
          refine ⟨5154545749967870204816779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6872727666623826939755705 5154545749967870204816779)
          ·
            refine ⟨7731818624951805307225169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154545749967870204816779 7731818624951805307225169)
            ·
              refine ⟨5798863968713853980418877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731818624951805307225169 5798863968713853980418877)
              ·
                refine ⟨2174573988267695242657079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5798863968713853980418877 2174573988267695242657079)
                ·
                  refine ⟨3261860982401542863985619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174573988267695242657079 3261860982401542863985619)
                  ·
                    refine ⟨4892791473602314295978429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3261860982401542863985619 4892791473602314295978429)
                    ·
                      refine ⟨1834796802600867860991911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4892791473602314295978429 1834796802600867860991911)
                      ·
                        rfl

theorem cell23_3573254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3573254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573254 prefixEnd_3573254 := by exact prefixLift 3573254
  have htrace : WordTrace (prefixWord ++ tailWord_3573254) baseStart_3573254 baseEnd_3573254 := by
    simpa [prefixWord, tailWord_3573254, baseEnd_3573254] using wordTrace_append hprefix tailTrace_3573254
  have hstable : (prefixWord ++ tailWord_3573254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573254).length < 2 ^ (prefixWord ++ tailWord_3573254).sum := by decide
  have hdescent : baseEnd_3573254 < baseStart_3573254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573260 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_3573260 : Nat := 118140960795 + 3573260 * 2 ^ 59
def prefixEnd_3573260 : Nat := 4983230072969 + 3 ^ 40 * 3573260 * 2
def baseEnd_3573260 : Nat := 1834799883484794837516883

theorem tailTrace_3573260 : CollatzResearch.WordTrace tailWord_3573260 prefixEnd_3573260 1834799883484794837516883 := by
  unfold tailWord_3573260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163749517348379533746617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86884999356464506044995489 65163749517348379533746617)
  ·
    refine ⟨48872812138011284650309963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65163749517348379533746617 48872812138011284650309963)
    ·
      refine ⟨73309218207016926975464945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48872812138011284650309963 73309218207016926975464945)
      ·
        refine ⟨54981913655262695231598709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73309218207016926975464945 54981913655262695231598709)
        ·
          refine ⟨5154554405180877677962379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54981913655262695231598709 5154554405180877677962379)
          ·
            refine ⟨7731831607771316516943569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154554405180877677962379 7731831607771316516943569)
            ·
              refine ⟨5798873705828487387707677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731831607771316516943569 5798873705828487387707677)
              ·
                refine ⟨2174577639685682770390379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5798873705828487387707677 2174577639685682770390379)
                ·
                  refine ⟨3261866459528524155585569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174577639685682770390379 3261866459528524155585569)
                  ·
                    refine ⟨2446399844646393116689177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3261866459528524155585569 2446399844646393116689177)
                    ·
                      refine ⟨1834799883484794837516883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446399844646393116689177 1834799883484794837516883)
                      ·
                        rfl

theorem cell23_3573260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_3573260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573260 prefixEnd_3573260 := by exact prefixLift 3573260
  have htrace : WordTrace (prefixWord ++ tailWord_3573260) baseStart_3573260 baseEnd_3573260 := by
    simpa [prefixWord, tailWord_3573260, baseEnd_3573260] using wordTrace_append hprefix tailTrace_3573260
  have hstable : (prefixWord ++ tailWord_3573260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573260).length < 2 ^ (prefixWord ++ tailWord_3573260).sum := by decide
  have hdescent : baseEnd_3573260 < baseStart_3573260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573282 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3573282 : Nat := 118140960795 + 3573282 * 2 ^ 59
def prefixEnd_3573282 : Nat := 4983230072969 + 3 ^ 40 * 3573282 * 2
def baseEnd_3573282 : Nat := 1834811180059193751441781

theorem tailTrace_3573282 : CollatzResearch.WordTrace tailWord_3573282 prefixEnd_3573282 1834811180059193751441781 := by
  unfold tailWord_3573282
  simp only [CollatzResearch.WordTrace]
  refine ⟨32582075360154264206198525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86885534293744704549862733 32582075360154264206198525)
  ·
    refine ⟨12218278260057849077324447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32582075360154264206198525 12218278260057849077324447)
    ·
      refine ⟨18327417390086773615986671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218278260057849077324447 18327417390086773615986671)
      ·
        refine ⟨27491126085130160423980007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327417390086773615986671 27491126085130160423980007)
        ·
          refine ⟨41236689127695240635970011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27491126085130160423980007 41236689127695240635970011)
          ·
            refine ⟨61855033691542860953955017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41236689127695240635970011 61855033691542860953955017)
            ·
              refine ⟨46391275268657145715466263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61855033691542860953955017 46391275268657145715466263)
              ·
                refine ⟨69586912902985718573199395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46391275268657145715466263 69586912902985718573199395)
                ·
                  refine ⟨104380369354478577859799093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69586912902985718573199395 104380369354478577859799093)
                  ·
                    refine ⟨9785659626982366674356165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104380369354478577859799093 9785659626982366674356165)
                    ·
                      refine ⟨1834811180059193751441781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9785659626982366674356165 1834811180059193751441781)
                      ·
                        rfl

theorem cell23_3573282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3573282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573282 prefixEnd_3573282 := by exact prefixLift 3573282
  have htrace : WordTrace (prefixWord ++ tailWord_3573282) baseStart_3573282 baseEnd_3573282 := by
    simpa [prefixWord, tailWord_3573282, baseEnd_3573282] using wordTrace_append hprefix tailTrace_3573282
  have hstable : (prefixWord ++ tailWord_3573282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573282).length < 2 ^ (prefixWord ++ tailWord_3573282).sum := by decide
  have hdescent : baseEnd_3573282 < baseStart_3573282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573295 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_3573295 : Nat := 118140960795 + 3573295 * 2 ^ 59
def prefixEnd_3573295 : Nat := 4983230072969 + 3 ^ 40 * 3573295 * 2
def baseEnd_3573295 : Nat := 1834817855307702200579221

theorem tailTrace_3573295 : CollatzResearch.WordTrace tailWord_3573295 prefixEnd_3573295 1834817855307702200579221 := by
  unfold tailWord_3573295
  simp only [CollatzResearch.WordTrace]
  refine ⟨130328775589569960045017339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86885850393046640030011559 130328775589569960045017339)
  ·
    refine ⟨195493163384354940067526009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130328775589569960045017339 195493163384354940067526009)
    ·
      refine ⟨146619872538266205050644507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195493163384354940067526009 146619872538266205050644507)
      ·
        refine ⟨219929808807399307575966761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146619872538266205050644507 219929808807399307575966761)
        ·
          refine ⟨164947356605549480681975071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219929808807399307575966761 164947356605549480681975071)
          ·
            refine ⟨247421034908324221022962607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164947356605549480681975071 247421034908324221022962607)
            ·
              refine ⟨371131552362486331534443911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247421034908324221022962607 371131552362486331534443911)
              ·
                refine ⟨556697328543729497301665867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371131552362486331534443911 556697328543729497301665867)
                ·
                  refine ⟨835045992815594245952498801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556697328543729497301665867 835045992815594245952498801)
                  ·
                    refine ⟨626284494611695684464374101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 835045992815594245952498801 626284494611695684464374101)
                    ·
                      refine ⟨1834817855307702200579221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 626284494611695684464374101 1834817855307702200579221)
                      ·
                        rfl

theorem cell23_3573295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_3573295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573295 prefixEnd_3573295 := by exact prefixLift 3573295
  have htrace : WordTrace (prefixWord ++ tailWord_3573295) baseStart_3573295 baseEnd_3573295 := by
    simpa [prefixWord, tailWord_3573295, baseEnd_3573295] using wordTrace_append hprefix tailTrace_3573295
  have hstable : (prefixWord ++ tailWord_3573295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573295).length < 2 ^ (prefixWord ++ tailWord_3573295).sum := by decide
  have hdescent : baseEnd_3573295 < baseStart_3573295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573319 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3573319 : Nat := 118140960795 + 3573319 * 2 ^ 59
def prefixEnd_3573319 : Nat := 4983230072969 + 3 ^ 40 * 3573319 * 2
def baseEnd_3573319 : Nat := 1834830178843410106679111

theorem tailTrace_3573319 : CollatzResearch.WordTrace tailWord_3573319 prefixEnd_3573319 1834830178843410106679111 := by
  unfold tailWord_3573319
  simp only [CollatzResearch.WordTrace]
  refine ⟨130329650941483012143891011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86886433960988674762594007 130329650941483012143891011)
  ·
    refine ⟨195494476412224518215836517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130329650941483012143891011 195494476412224518215836517)
    ·
      refine ⟨36655214327292097165469347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195494476412224518215836517 36655214327292097165469347)
      ·
        refine ⟨54982821490938145748204021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36655214327292097165469347 54982821490938145748204021)
        ·
          refine ⟨5154639514775451163894127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54982821490938145748204021 5154639514775451163894127)
          ·
            refine ⟨7731959272163176745841191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154639514775451163894127 7731959272163176745841191)
            ·
              refine ⟨11597938908244765118761787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731959272163176745841191 11597938908244765118761787)
              ·
                refine ⟨17396908362367147678142681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11597938908244765118761787 17396908362367147678142681)
                ·
                  refine ⟨13047681271775360758607011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17396908362367147678142681 13047681271775360758607011)
                  ·
                    refine ⟨19571521907663041137910517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13047681271775360758607011 19571521907663041137910517)
                    ·
                      refine ⟨1834830178843410106679111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19571521907663041137910517 1834830178843410106679111)
                      ·
                        rfl

theorem cell23_3573319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3573319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573319 prefixEnd_3573319 := by exact prefixLift 3573319
  have htrace : WordTrace (prefixWord ++ tailWord_3573319) baseStart_3573319 baseEnd_3573319 := by
    simpa [prefixWord, tailWord_3573319, baseEnd_3573319] using wordTrace_append hprefix tailTrace_3573319
  have hstable : (prefixWord ++ tailWord_3573319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573319).length < 2 ^ (prefixWord ++ tailWord_3573319).sum := by decide
  have hdescent : baseEnd_3573319 < baseStart_3573319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573332 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3573332 : Nat := 118140960795 + 3573332 * 2 ^ 59
def prefixEnd_3573332 : Nat := 4983230072969 + 3 ^ 40 * 3573332 * 2
def baseEnd_3573332 : Nat := 1834836854091918555816551

theorem tailTrace_3573332 : CollatzResearch.WordTrace tailWord_3573332 prefixEnd_3573332 1834836854091918555816551 := by
  unfold tailWord_3573332
  simp only [CollatzResearch.WordTrace]
  refine ⟨65165062545217957682057125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86886750060290610242742833 65165062545217957682057125)
  ·
    refine ⟨12218449227228367065385711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65165062545217957682057125 12218449227228367065385711)
    ·
      refine ⟨18327673840842550598078567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218449227228367065385711 18327673840842550598078567)
      ·
        refine ⟨27491510761263825897117851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327673840842550598078567 27491510761263825897117851)
        ·
          refine ⟨41237266141895738845676777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27491510761263825897117851 41237266141895738845676777)
          ·
            refine ⟨30927949606421804134257583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41237266141895738845676777 30927949606421804134257583)
            ·
              refine ⟨46391924409632706201386375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30927949606421804134257583 46391924409632706201386375)
              ·
                refine ⟨69587886614449059302079563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46391924409632706201386375 69587886614449059302079563)
                ·
                  refine ⟨104381829921673588953119345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69587886614449059302079563 104381829921673588953119345)
                  ·
                    refine ⟨78286372441255191714839509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104381829921673588953119345 78286372441255191714839509)
                    ·
                      refine ⟨1834836854091918555816551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78286372441255191714839509 1834836854091918555816551)
                      ·
                        rfl

theorem cell23_3573332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3573332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573332 prefixEnd_3573332 := by exact prefixLift 3573332
  have htrace : WordTrace (prefixWord ++ tailWord_3573332) baseStart_3573332 baseEnd_3573332 := by
    simpa [prefixWord, tailWord_3573332, baseEnd_3573332] using wordTrace_append hprefix tailTrace_3573332
  have hstable : (prefixWord ++ tailWord_3573332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573332).length < 2 ^ (prefixWord ++ tailWord_3573332).sum := by decide
  have hdescent : baseEnd_3573332 < baseStart_3573332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573369 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_3573369 : Nat := 118140960795 + 3573369 * 2 ^ 59
def prefixEnd_3573369 : Nat := 4983230072969 + 3 ^ 40 * 3573369 * 2
def baseEnd_3573369 : Nat := 611618617625378303684627

theorem tailTrace_3573369 : CollatzResearch.WordTrace tailWord_3573369 prefixEnd_3573369 611618617625378303684627 := by
  unfold tailWord_3573369
  simp only [CollatzResearch.WordTrace]
  refine ⟨130331474591301870683211161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86887649727534580455474107 130331474591301870683211161)
  ·
    refine ⟨97748605943476403012408371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130331474591301870683211161 97748605943476403012408371)
    ·
      refine ⟨146622908915214604518612557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97748605943476403012408371 146622908915214604518612557)
      ·
        refine ⟨54983590843205476694479709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146622908915214604518612557 54983590843205476694479709)
        ·
          refine ⟨20618846566202053760429891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54983590843205476694479709 20618846566202053760429891)
          ·
            refine ⟨30928269849303080640644837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20618846566202053760429891 30928269849303080640644837)
            ·
              refine ⟨5799050596744327620120907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30928269849303080640644837 5799050596744327620120907)
              ·
                refine ⟨8698575895116491430181361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799050596744327620120907 8698575895116491430181361)
                ·
                  refine ⟨6523931921337368572636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698575895116491430181361 6523931921337368572636021)
                  ·
                    refine ⟨611618617625378303684627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6523931921337368572636021 611618617625378303684627)
                    ·
                      rfl

theorem cell23_3573369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_3573369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573369 prefixEnd_3573369 := by exact prefixLift 3573369
  have htrace : WordTrace (prefixWord ++ tailWord_3573369) baseStart_3573369 baseEnd_3573369 := by
    simpa [prefixWord, tailWord_3573369, baseEnd_3573369] using wordTrace_append hprefix tailTrace_3573369
  have hstable : (prefixWord ++ tailWord_3573369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573369).length < 2 ^ (prefixWord ++ tailWord_3573369).sum := by decide
  have hdescent : baseEnd_3573369 < baseStart_3573369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573426 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3573426 : Nat := 118140960795 + 3573426 * 2 ^ 59
def prefixEnd_3573426 : Nat := 4983230072969 + 3 ^ 40 * 3573426 * 2
def baseEnd_3573426 : Nat := 1834885121273441188041119

theorem tailTrace_3573426 : CollatzResearch.WordTrace tailWord_3573426 prefixEnd_3573426 1834885121273441188041119 := by
  unfold tailWord_3573426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32583388388023842354509033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86889035701396912945357421 32583388388023842354509033)
  ·
    refine ⟨24437541291017881765881775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32583388388023842354509033 24437541291017881765881775)
    ·
      refine ⟨36656311936526822648822663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24437541291017881765881775 36656311936526822648822663)
      ·
        refine ⟨54984467904790233973233995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36656311936526822648822663 54984467904790233973233995)
        ·
          refine ⟨82476701857185350959850993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54984467904790233973233995 82476701857185350959850993)
          ·
            refine ⟨61857526392889013219888245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82476701857185350959850993 61857526392889013219888245)
            ·
              refine ⟨5799143099333344989364523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61857526392889013219888245 5799143099333344989364523)
              ·
                refine ⟨8698714649000017484046785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799143099333344989364523 8698714649000017484046785)
                ·
                  refine ⟨6524035986750013113035089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698714649000017484046785 6524035986750013113035089)
                  ·
                    refine ⟨4893026990062509834776317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524035986750013113035089 4893026990062509834776317)
                    ·
                      refine ⟨1834885121273441188041119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893026990062509834776317 1834885121273441188041119)
                      ·
                        rfl

theorem cell23_3573426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3573426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573426 prefixEnd_3573426 := by exact prefixLift 3573426
  have htrace : WordTrace (prefixWord ++ tailWord_3573426) baseStart_3573426 baseEnd_3573426 := by
    simpa [prefixWord, tailWord_3573426, baseEnd_3573426] using wordTrace_append hprefix tailTrace_3573426
  have hstable : (prefixWord ++ tailWord_3573426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573426).length < 2 ^ (prefixWord ++ tailWord_3573426).sum := by decide
  have hdescent : baseEnd_3573426 < baseStart_3573426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_3573432 : Nat := 118140960795 + 3573432 * 2 ^ 59
def prefixEnd_3573432 : Nat := 4983230072969 + 3 ^ 40 * 3573432 * 2
def baseEnd_3573432 : Nat := 1834888202157368164566091

theorem tailTrace_3573432 : CollatzResearch.WordTrace tailWord_3573432 prefixEnd_3573432 1834888202157368164566091 := by
  unfold tailWord_3573432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65166886195036816221377275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86889181593382421628503033 65166886195036816221377275)
  ·
    refine ⟨97750329292555224332065913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65166886195036816221377275 97750329292555224332065913)
    ·
      refine ⟨73312746969416418249049435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97750329292555224332065913 73312746969416418249049435)
      ·
        refine ⟨109969120454124627373574153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73312746969416418249049435 109969120454124627373574153)
        ·
          refine ⟨82476840340593470530180615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109969120454124627373574153 82476840340593470530180615)
          ·
            refine ⟨123715260510890205795270923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82476840340593470530180615 123715260510890205795270923)
            ·
              refine ⟨185572890766335308692906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123715260510890205795270923 185572890766335308692906385)
              ·
                refine ⟨139179668074751481519679789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185572890766335308692906385 139179668074751481519679789)
                ·
                  refine ⟨52192375528031805569879921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139179668074751481519679789 52192375528031805569879921)
                  ·
                    refine ⟨39144281646023854177409941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52192375528031805569879921 39144281646023854177409941)
                    ·
                      refine ⟨1834888202157368164566091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39144281646023854177409941 1834888202157368164566091)
                      ·
                        rfl

theorem cell23_3573432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_3573432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573432 prefixEnd_3573432 := by exact prefixLift 3573432
  have htrace : WordTrace (prefixWord ++ tailWord_3573432) baseStart_3573432 baseEnd_3573432 := by
    simpa [prefixWord, tailWord_3573432, baseEnd_3573432] using wordTrace_append hprefix tailTrace_3573432
  have hstable : (prefixWord ++ tailWord_3573432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573432).length < 2 ^ (prefixWord ++ tailWord_3573432).sum := by decide
  have hdescent : baseEnd_3573432 < baseStart_3573432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573466 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_3573466 : Nat := 118140960795 + 3573466 * 2 ^ 59
def prefixEnd_3573466 : Nat := 4983230072969 + 3 ^ 40 * 3573466 * 2
def baseEnd_3573466 : Nat := 1834905660499621031540935

theorem tailTrace_3573466 : CollatzResearch.WordTrace tailWord_3573466 prefixEnd_3573466 1834905660499621031540935 := by
  unfold tailWord_3573466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32583753117987614062373063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86890008314633637499661501 32583753117987614062373063)
  ·
    refine ⟨48875629676981421093559595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32583753117987614062373063 48875629676981421093559595)
    ·
      refine ⟨73313444515472131640339393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48875629676981421093559595 73313444515472131640339393)
      ·
        refine ⟨54985083386604098730254545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73313444515472131640339393 54985083386604098730254545)
        ·
          refine ⟨41238812539953074047690909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54985083386604098730254545 41238812539953074047690909)
          ·
            refine ⟨15464554702482402767884091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41238812539953074047690909 15464554702482402767884091)
            ·
              refine ⟨23196832053723604151826137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15464554702482402767884091 23196832053723604151826137)
              ·
                refine ⟨17397624040292703113869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23196832053723604151826137 17397624040292703113869603)
                ·
                  refine ⟨26096436060439054670804405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17397624040292703113869603 26096436060439054670804405)
                  ·
                    refine ⟨2446540880666161375387913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26096436060439054670804405 2446540880666161375387913)
                    ·
                      refine ⟨1834905660499621031540935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446540880666161375387913 1834905660499621031540935)
                      ·
                        rfl

theorem cell23_3573466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_3573466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573466 prefixEnd_3573466 := by exact prefixLift 3573466
  have htrace : WordTrace (prefixWord ++ tailWord_3573466) baseStart_3573466 baseEnd_3573466 := by
    simpa [prefixWord, tailWord_3573466, baseEnd_3573466] using wordTrace_append hprefix tailTrace_3573466
  have hstable : (prefixWord ++ tailWord_3573466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573466).length < 2 ^ (prefixWord ++ tailWord_3573466).sum := by decide
  have hdescent : baseEnd_3573466 < baseStart_3573466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573476 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_3573476 : Nat := 118140960795 + 3573476 * 2 ^ 59
def prefixEnd_3573476 : Nat := 4983230072969 + 3 ^ 40 * 3573476 * 2
def baseEnd_3573476 : Nat := 611636931768721997471963

theorem tailTrace_3573476 : CollatzResearch.WordTrace tailWord_3573476 prefixEnd_3573476 611636931768721997471963 := by
  unfold tailWord_3573476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65167688600957113978678141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86890251467942818638237521 65167688600957113978678141)
  ·
    refine ⟨24437883225358917742004303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65167688600957113978678141 24437883225358917742004303)
    ·
      refine ⟨36656824838038376613006455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24437883225358917742004303 36656824838038376613006455)
      ·
        refine ⟨54985237257057564919509683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36656824838038376613006455 54985237257057564919509683)
        ·
          refine ⟨82477855885586347379264525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54985237257057564919509683 82477855885586347379264525)
          ·
            refine ⟨30929195957094880267224197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82477855885586347379264525 30929195957094880267224197)
            ·
              refine ⟨5799224241955290050104537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30929195957094880267224197 5799224241955290050104537)
              ·
                refine ⟨4349418181466467537578403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5799224241955290050104537 4349418181466467537578403)
                ·
                  refine ⟨6524127272199701306367605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349418181466467537578403 6524127272199701306367605)
                  ·
                    refine ⟨611636931768721997471963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6524127272199701306367605 611636931768721997471963)
                    ·
                      rfl

theorem cell23_3573476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_3573476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573476 prefixEnd_3573476 := by exact prefixLift 3573476
  have htrace : WordTrace (prefixWord ++ tailWord_3573476) baseStart_3573476 baseEnd_3573476 := by
    simpa [prefixWord, tailWord_3573476, baseEnd_3573476] using wordTrace_append hprefix tailTrace_3573476
  have hstable : (prefixWord ++ tailWord_3573476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573476).length < 2 ^ (prefixWord ++ tailWord_3573476).sum := by decide
  have hdescent : baseEnd_3573476 < baseStart_3573476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573534 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3573534 : Nat := 118140960795 + 3573534 * 2 ^ 59
def prefixEnd_3573534 : Nat := 4983230072969 + 3 ^ 40 * 3573534 * 2
def baseEnd_3573534 : Nat := 1834940577184126765490623

theorem tailTrace_3573534 : CollatzResearch.WordTrace tailWord_3573534 prefixEnd_3573534 1834940577184126765490623 := by
  unfold tailWord_3573534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292186579463012982870957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86891661757136069241978437 16292186579463012982870957)
  ·
    refine ⟨6109569967298629868576609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16292186579463012982870957 6109569967298629868576609)
    ·
      refine ⟨4582177475473972401432457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6109569967298629868576609 4582177475473972401432457)
      ·
        refine ⟨3436633106605479301074343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4582177475473972401432457 3436633106605479301074343)
        ·
          refine ⟨5154949659908218951611515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436633106605479301074343 5154949659908218951611515)
          ·
            refine ⟨7732424489862328427417273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154949659908218951611515 7732424489862328427417273)
            ·
              refine ⟨5799318367396746320562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7732424489862328427417273 5799318367396746320562955)
              ·
                refine ⟨8698977551095119480844433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799318367396746320562955 8698977551095119480844433)
                ·
                  refine ⟨6524233163321339610633325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698977551095119480844433 6524233163321339610633325)
                  ·
                    refine ⟨2446587436245502353987497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6524233163321339610633325 2446587436245502353987497)
                    ·
                      refine ⟨1834940577184126765490623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446587436245502353987497 1834940577184126765490623)
                      ·
                        rfl

theorem cell23_3573534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3573534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573534 prefixEnd_3573534 := by exact prefixLift 3573534
  have htrace : WordTrace (prefixWord ++ tailWord_3573534) baseStart_3573534 baseEnd_3573534 := by
    simpa [prefixWord, tailWord_3573534, baseEnd_3573534] using wordTrace_append hprefix tailTrace_3573534
  have hstable : (prefixWord ++ tailWord_3573534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573534).length < 2 ^ (prefixWord ++ tailWord_3573534).sum := by decide
  have hdescent : baseEnd_3573534 < baseStart_3573534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573550 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3573550 : Nat := 118140960795 + 3573550 * 2 ^ 59
def prefixEnd_3573550 : Nat := 4983230072969 + 3 ^ 40 * 3573550 * 2
def baseEnd_3573550 : Nat := 1834948792874598702890549

theorem tailTrace_3573550 : CollatzResearch.WordTrace tailWord_3573550 prefixEnd_3573550 1834948792874598702890549 := by
  unfold tailWord_3573550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292259525455767324443763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86892050802430759063700069 16292259525455767324443763)
  ·
    refine ⟨24438389288183650986665645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292259525455767324443763 24438389288183650986665645)
    ·
      refine ⟨9164395983068869119999617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24438389288183650986665645 9164395983068869119999617)
      ·
        refine ⟨6873296987301651839999713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9164395983068869119999617 6873296987301651839999713)
        ·
          refine ⟨5154972740476238879999785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873296987301651839999713 5154972740476238879999785)
          ·
            refine ⟨3866229555357179159999839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154972740476238879999785 3866229555357179159999839)
            ·
              refine ⟨5799344333035768739999759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866229555357179159999839 5799344333035768739999759)
              ·
                refine ⟨8699016499553653109999639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799344333035768739999759 8699016499553653109999639)
                ·
                  refine ⟨13048524749330479664999459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699016499553653109999639 13048524749330479664999459)
                  ·
                    refine ⟨19572787123995719497499189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13048524749330479664999459 19572787123995719497499189)
                    ·
                      refine ⟨1834948792874598702890549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19572787123995719497499189 1834948792874598702890549)
                      ·
                        rfl

theorem cell23_3573550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3573550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573550 prefixEnd_3573550 := by exact prefixLift 3573550
  have htrace : WordTrace (prefixWord ++ tailWord_3573550) baseStart_3573550 baseEnd_3573550 := by
    simpa [prefixWord, tailWord_3573550, baseEnd_3573550] using wordTrace_append hprefix tailTrace_3573550
  have hstable : (prefixWord ++ tailWord_3573550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573550).length < 2 ^ (prefixWord ++ tailWord_3573550).sum := by decide
  have hdescent : baseEnd_3573550 < baseStart_3573550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573566 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3573566 : Nat := 118140960795 + 3573566 * 2 ^ 59
def prefixEnd_3573566 : Nat := 4983230072969 + 3 ^ 40 * 3573566 * 2
def baseEnd_3573566 : Nat := 611652336188356880096825

theorem tailTrace_3573566 : CollatzResearch.WordTrace tailWord_3573566 prefixEnd_3573566 611652336188356880096825 := by
  unfold tailWord_3573566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292332471448521666016569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86892439847725448885421701 16292332471448521666016569)
  ·
    refine ⟨12219249353586391249512427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16292332471448521666016569 12219249353586391249512427)
    ·
      refine ⟨18328874030379586874268641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12219249353586391249512427 18328874030379586874268641)
      ·
        refine ⟨13746655522784690155701481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18328874030379586874268641 13746655522784690155701481)
        ·
          refine ⟨10309991642088517616776111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13746655522784690155701481 10309991642088517616776111)
          ·
            refine ⟨15464987463132776425164167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10309991642088517616776111 15464987463132776425164167)
            ·
              refine ⟨23197481194699164637746251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15464987463132776425164167 23197481194699164637746251)
              ·
                refine ⟨34796221792048746956619377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23197481194699164637746251 34796221792048746956619377)
                ·
                  refine ⟨26097166344036560217464533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34796221792048746956619377 26097166344036560217464533)
                  ·
                    refine ⟨611652336188356880096825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26097166344036560217464533 611652336188356880096825)
                    ·
                      rfl

theorem cell23_3573566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3573566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573566 prefixEnd_3573566 := by exact prefixLift 3573566
  have htrace : WordTrace (prefixWord ++ tailWord_3573566) baseStart_3573566 baseEnd_3573566 := by
    simpa [prefixWord, tailWord_3573566, baseEnd_3573566] using wordTrace_append hprefix tailTrace_3573566
  have hstable : (prefixWord ++ tailWord_3573566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573566).length < 2 ^ (prefixWord ++ tailWord_3573566).sum := by decide
  have hdescent : baseEnd_3573566 < baseStart_3573566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573637 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_3573637 : Nat := 118140960795 + 3573637 * 2 ^ 59
def prefixEnd_3573637 : Nat := 4983230072969 + 3 ^ 40 * 3573637 * 2
def baseEnd_3573637 : Nat := 1834993465691539862502649

theorem tailTrace_3573637 : CollatzResearch.WordTrace tailWord_3573637 prefixEnd_3573637 1834993465691539862502649 := by
  unfold tailWord_3573637
  simp only [CollatzResearch.WordTrace]
  refine ⟨130341249354330952453967165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86894166236220634969311443 130341249354330952453967165)
  ·
    refine ⟨48877968507874107170237687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130341249354330952453967165 48877968507874107170237687)
    ·
      refine ⟨73316952761811160755356531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48877968507874107170237687 73316952761811160755356531)
      ·
        refine ⟨109975429142716741133034797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73316952761811160755356531 109975429142716741133034797)
        ·
          refine ⟨41240785928518777924888049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109975429142716741133034797 41240785928518777924888049)
          ·
            refine ⟨30930589446389083443666037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41240785928518777924888049 30930589446389083443666037)
            ·
              refine ⟨2899742760598976572843691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30930589446389083443666037 2899742760598976572843691)
              ·
                refine ⟨4349614140898464859265537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899742760598976572843691 4349614140898464859265537)
                ·
                  refine ⟨3262210605673848644449153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4349614140898464859265537 3262210605673848644449153)
                  ·
                    refine ⟨2446657954255386483336865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3262210605673848644449153 2446657954255386483336865)
                    ·
                      refine ⟨1834993465691539862502649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446657954255386483336865 1834993465691539862502649)
                      ·
                        rfl

theorem cell23_3573637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_3573637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573637 prefixEnd_3573637 := by exact prefixLift 3573637
  have htrace : WordTrace (prefixWord ++ tailWord_3573637) baseStart_3573637 baseEnd_3573637 := by
    simpa [prefixWord, tailWord_3573637, baseEnd_3573637] using wordTrace_append hprefix tailTrace_3573637
  have hstable : (prefixWord ++ tailWord_3573637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573637).length < 2 ^ (prefixWord ++ tailWord_3573637).sum := by decide
  have hdescent : baseEnd_3573637 < baseStart_3573637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573660 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 5]
def baseStart_3573660 : Nat := 118140960795 + 3573660 * 2 ^ 59
def prefixEnd_3573660 : Nat := 4983230072969 + 3 ^ 40 * 3573660 * 2
def baseEnd_3573660 : Nat := 203889475082954808057227

theorem tailTrace_3573660 : CollatzResearch.WordTrace tailWord_3573660 prefixEnd_3573660 203889475082954808057227 := by
  unfold tailWord_3573660
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171044116623813691027217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86894725488831751588036289 65171044116623813691027217)
  ·
    refine ⟨48878283087467860268270413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65171044116623813691027217 48878283087467860268270413)
    ·
      refine ⟨18329356157800447600601405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48878283087467860268270413 18329356157800447600601405)
      ·
        refine ⟨6873508559175167850225527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18329356157800447600601405 6873508559175167850225527)
        ·
          refine ⟨10310262838762751775338291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873508559175167850225527 10310262838762751775338291)
          ·
            refine ⟨15465394258144127663007437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310262838762751775338291 15465394258144127663007437)
            ·
              refine ⟨5799522846804047873627789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15465394258144127663007437 5799522846804047873627789)
              ·
                refine ⟨2174821067551517952610421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5799522846804047873627789 2174821067551517952610421)
                ·
                  refine ⟨203889475082954808057227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174821067551517952610421 203889475082954808057227)
                  ·
                    rfl

theorem cell23_3573660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_3573660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573660 prefixEnd_3573660 := by exact prefixLift 3573660
  have htrace : WordTrace (prefixWord ++ tailWord_3573660) baseStart_3573660 baseEnd_3573660 := by
    simpa [prefixWord, tailWord_3573660, baseEnd_3573660] using wordTrace_append hprefix tailTrace_3573660
  have hstable : (prefixWord ++ tailWord_3573660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573660).length < 2 ^ (prefixWord ++ tailWord_3573660).sum := by decide
  have hdescent : baseEnd_3573660 < baseStart_3573660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573706 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3573706 : Nat := 118140960795 + 3573706 * 2 ^ 59
def prefixEnd_3573706 : Nat := 4983230072969 + 3 ^ 40 * 3573706 * 2
def baseEnd_3573706 : Nat := 1835028895856700092539831

theorem tailTrace_3573706 : CollatzResearch.WordTrace tailWord_3573706 prefixEnd_3573706 1835028895856700092539831 := by
  unfold tailWord_3573706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32585941497770244309557243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86895843994053984825485981 32585941497770244309557243)
  ·
    refine ⟨48878912246655366464335865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32585941497770244309557243 48878912246655366464335865)
    ·
      refine ⟨36659184184991524848251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48878912246655366464335865 36659184184991524848251899)
      ·
        refine ⟨54988776277487287272377849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36659184184991524848251899 54988776277487287272377849)
        ·
          refine ⟨41241582208115465454283387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54988776277487287272377849 41241582208115465454283387)
          ·
            refine ⟨61862373312173198181425081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41241582208115465454283387 61862373312173198181425081)
            ·
              refine ⟨46396779984129898636068811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61862373312173198181425081 46396779984129898636068811)
              ·
                refine ⟨69595169976194847954103217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46396779984129898636068811 69595169976194847954103217)
                ·
                  refine ⟨52196377482146135965577413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69595169976194847954103217 52196377482146135965577413)
                  ·
                    refine ⟨9786820777902400493545765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52196377482146135965577413 9786820777902400493545765)
                    ·
                      refine ⟨1835028895856700092539831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9786820777902400493545765 1835028895856700092539831)
                      ·
                        rfl

theorem cell23_3573706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3573706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573706 prefixEnd_3573706 := by exact prefixLift 3573706
  have htrace : WordTrace (prefixWord ++ tailWord_3573706) baseStart_3573706 baseEnd_3573706 := by
    simpa [prefixWord, tailWord_3573706, baseEnd_3573706] using wordTrace_append hprefix tailTrace_3573706
  have hstable : (prefixWord ++ tailWord_3573706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573706).length < 2 ^ (prefixWord ++ tailWord_3573706).sum := by decide
  have hdescent : baseEnd_3573706 < baseStart_3573706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573720 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 1, 4]
def baseStart_3573720 : Nat := 118140960795 + 3573720 * 2 ^ 59
def prefixEnd_3573720 : Nat := 4983230072969 + 3 ^ 40 * 3573720 * 2
def baseEnd_3573720 : Nat := 611678694861954345921589

theorem tailTrace_3573720 : CollatzResearch.WordTrace tailWord_3573720 prefixEnd_3573720 611678694861954345921589 := by
  unfold tailWord_3573720
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172138306515128814619307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86896184408686838419492409 65172138306515128814619307)
  ·
    refine ⟨97758207459772693221928961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65172138306515128814619307 97758207459772693221928961)
    ·
      refine ⟨73318655594829519916446721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97758207459772693221928961 73318655594829519916446721)
      ·
        refine ⟨54988991696122139937335041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73318655594829519916446721 54988991696122139937335041)
        ·
          refine ⟨41241743772091604953001281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54988991696122139937335041 41241743772091604953001281)
          ·
            refine ⟨30931307829068703714750961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41241743772091604953001281 30931307829068703714750961)
            ·
              refine ⟨23198480871801527786063221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30931307829068703714750961 23198480871801527786063221)
              ·
                refine ⟨2174857581731393229943427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23198480871801527786063221 2174857581731393229943427)
                ·
                  refine ⟨3262286372597089844915141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174857581731393229943427 3262286372597089844915141)
                  ·
                    refine ⟨611678694861954345921589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3262286372597089844915141 611678694861954345921589)
                    ·
                      rfl

theorem cell23_3573720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_3573720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573720 prefixEnd_3573720 := by exact prefixLift 3573720
  have htrace : WordTrace (prefixWord ++ tailWord_3573720) baseStart_3573720 baseEnd_3573720 := by
    simpa [prefixWord, tailWord_3573720, baseEnd_3573720] using wordTrace_append hprefix tailTrace_3573720
  have hstable : (prefixWord ++ tailWord_3573720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573720).length < 2 ^ (prefixWord ++ tailWord_3573720).sum := by decide
  have hdescent : baseEnd_3573720 < baseStart_3573720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573736 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3573736 : Nat := 118140960795 + 3573736 * 2 ^ 59
def prefixEnd_3573736 : Nat := 4983230072969 + 3 ^ 40 * 3573736 * 2
def baseEnd_3573736 : Nat := 1835044300276334975164693

theorem tailTrace_3573736 : CollatzResearch.WordTrace tailWord_3573736 prefixEnd_3573736 1835044300276334975164693 := by
  unfold tailWord_3573736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172430090486146180910531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86896573453981528241214041 65172430090486146180910531)
  ·
    refine ⟨97758645135729219271365797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65172430090486146180910531 97758645135729219271365797)
    ·
      refine ⟨18329745962949228613381087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97758645135729219271365797 18329745962949228613381087)
      ·
        refine ⟨27494618944423842920071631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329745962949228613381087 27494618944423842920071631)
        ·
          refine ⟨41241928416635764380107447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27494618944423842920071631 41241928416635764380107447)
          ·
            refine ⟨61862892624953646570161171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41241928416635764380107447 61862892624953646570161171)
            ·
              refine ⟨92794338937430469855241757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61862892624953646570161171 92794338937430469855241757)
              ·
                refine ⟨34797877101536426195715659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92794338937430469855241757 34797877101536426195715659)
                ·
                  refine ⟨52196815652304639293573489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34797877101536426195715659 52196815652304639293573489)
                  ·
                    refine ⟨39147611739228479470180117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52196815652304639293573489 39147611739228479470180117)
                    ·
                      refine ⟨1835044300276334975164693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39147611739228479470180117 1835044300276334975164693)
                      ·
                        rfl

theorem cell23_3573736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3573736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573736 prefixEnd_3573736 := by exact prefixLift 3573736
  have htrace : WordTrace (prefixWord ++ tailWord_3573736) baseStart_3573736 baseEnd_3573736 := by
    simpa [prefixWord, tailWord_3573736, baseEnd_3573736] using wordTrace_append hprefix tailTrace_3573736
  have hstable : (prefixWord ++ tailWord_3573736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573736).length < 2 ^ (prefixWord ++ tailWord_3573736).sum := by decide
  have hdescent : baseEnd_3573736 < baseStart_3573736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573756 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3573756 : Nat := 118140960795 + 3573756 * 2 ^ 59
def prefixEnd_3573756 : Nat := 4983230072969 + 3 ^ 40 * 3573756 * 2
def baseEnd_3573756 : Nat := 1835054569889424896914601

theorem tailTrace_3573756 : CollatzResearch.WordTrace tailWord_3573756 prefixEnd_3573756 1835054569889424896914601 := by
  unfold tailWord_3573756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172794820449917888774561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86897059760599890518366081 65172794820449917888774561)
  ·
    refine ⟨48879596115337438416580921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65172794820449917888774561 48879596115337438416580921)
    ·
      refine ⟨36659697086503078812435691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48879596115337438416580921 36659697086503078812435691)
      ·
        refine ⟨54989545629754618218653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36659697086503078812435691 54989545629754618218653537)
        ·
          refine ⟨41242159222315963663990153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54989545629754618218653537 41242159222315963663990153)
          ·
            refine ⟨30931619416736972747992615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41242159222315963663990153 30931619416736972747992615)
            ·
              refine ⟨46397429125105459121988923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30931619416736972747992615 46397429125105459121988923)
              ·
                refine ⟨69596143687658188682983385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46397429125105459121988923 69596143687658188682983385)
                ·
                  refine ⟨52197107765743641512237539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69596143687658188682983385 52197107765743641512237539)
                  ·
                    refine ⟨78295661648615462268356309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52197107765743641512237539 78295661648615462268356309)
                    ·
                      refine ⟨1835054569889424896914601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78295661648615462268356309 1835054569889424896914601)
                      ·
                        rfl

theorem cell23_3573756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3573756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573756 prefixEnd_3573756 := by exact prefixLift 3573756
  have htrace : WordTrace (prefixWord ++ tailWord_3573756) baseStart_3573756 baseEnd_3573756 := by
    simpa [prefixWord, tailWord_3573756, baseEnd_3573756] using wordTrace_append hprefix tailTrace_3573756
  have hstable : (prefixWord ++ tailWord_3573756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573756).length < 2 ^ (prefixWord ++ tailWord_3573756).sum := by decide
  have hdescent : baseEnd_3573756 < baseStart_3573756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573764 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3573764 : Nat := 118140960795 + 3573764 * 2 ^ 59
def prefixEnd_3573764 : Nat := 4983230072969 + 3 ^ 40 * 3573764 * 2
def baseEnd_3573764 : Nat := 1835058677734660865614565

theorem tailTrace_3573764 : CollatzResearch.WordTrace tailWord_3573764 prefixEnd_3573764 1835058677734660865614565 := by
  unfold tailWord_3573764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172940712435426571920173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86897254283247235429226897 65172940712435426571920173)
  ·
    refine ⟨24439852767163284964470065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65172940712435426571920173 24439852767163284964470065)
    ·
      refine ⟨18329889575372463723352549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24439852767163284964470065 18329889575372463723352549)
      ·
        refine ⟨3436854295382336948128603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18329889575372463723352549 3436854295382336948128603)
        ·
          refine ⟨5155281443073505422192905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436854295382336948128603 5155281443073505422192905)
          ·
            refine ⟨3866461082305129066644679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155281443073505422192905 3866461082305129066644679)
            ·
              refine ⟨5799691623457693599967019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866461082305129066644679 5799691623457693599967019)
              ·
                refine ⟨8699537435186540399950529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799691623457693599967019 8699537435186540399950529)
                ·
                  refine ⟨6524653076389905299962897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8699537435186540399950529 6524653076389905299962897)
                  ·
                    refine ⟨4893489807292428974972173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524653076389905299962897 4893489807292428974972173)
                    ·
                      refine ⟨1835058677734660865614565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893489807292428974972173 1835058677734660865614565)
                      ·
                        rfl

theorem cell23_3573764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3573764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573764 prefixEnd_3573764 := by exact prefixLift 3573764
  have htrace : WordTrace (prefixWord ++ tailWord_3573764) baseStart_3573764 baseEnd_3573764 := by
    simpa [prefixWord, tailWord_3573764, baseEnd_3573764] using wordTrace_append hprefix tailTrace_3573764
  have hstable : (prefixWord ++ tailWord_3573764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573764).length < 2 ^ (prefixWord ++ tailWord_3573764).sum := by decide
  have hdescent : baseEnd_3573764 < baseStart_3573764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573803 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3]
def baseStart_3573803 : Nat := 118140960795 + 3573803 * 2 ^ 59
def prefixEnd_3573803 : Nat := 4983230072969 + 3 ^ 40 * 3573803 * 2
def baseEnd_3573803 : Nat := 1835078703480186213026885

theorem tailTrace_3573803 : CollatzResearch.WordTrace tailWord_3573803 prefixEnd_3573803 1835078703480186213026885 := by
  unfold tailWord_3573803
  simp only [CollatzResearch.WordTrace]
  refine ⟨130347303871729562804510063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86898202581153041869673375 130347303871729562804510063)
  ·
    refine ⟨195520955807594344206765095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130347303871729562804510063 195520955807594344206765095)
    ·
      refine ⟨293281433711391516310147643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195520955807594344206765095 293281433711391516310147643)
      ·
        refine ⟨439922150567087274465221465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293281433711391516310147643 439922150567087274465221465)
        ·
          refine ⟨329941612925315455848916099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439922150567087274465221465 329941612925315455848916099)
          ·
            refine ⟨494912419387973183773374149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329941612925315455848916099 494912419387973183773374149)
            ·
              refine ⟨92796078635244971957507653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494912419387973183773374149 92796078635244971957507653)
              ·
                refine ⟨17399264744108432242032685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92796078635244971957507653 17399264744108432242032685)
                ·
                  refine ⟨6524724279040662090762257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17399264744108432242032685 6524724279040662090762257)
                  ·
                    refine ⟨4893543209280496568071693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524724279040662090762257 4893543209280496568071693)
                    ·
                      refine ⟨1835078703480186213026885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893543209280496568071693 1835078703480186213026885)
                      ·
                        rfl

theorem cell23_3573803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].length) (baseStart_3573803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573803 prefixEnd_3573803 := by exact prefixLift 3573803
  have htrace : WordTrace (prefixWord ++ tailWord_3573803) baseStart_3573803 baseEnd_3573803 := by
    simpa [prefixWord, tailWord_3573803, baseEnd_3573803] using wordTrace_append hprefix tailTrace_3573803
  have hstable : (prefixWord ++ tailWord_3573803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573803).length < 2 ^ (prefixWord ++ tailWord_3573803).sum := by decide
  have hdescent : baseEnd_3573803 < baseStart_3573803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573810 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3573810 : Nat := 118140960795 + 3573810 * 2 ^ 59
def prefixEnd_3573810 : Nat := 4983230072969 + 3 ^ 40 * 3573810 * 2
def baseEnd_3573810 : Nat := 611694099281589228546451

theorem tailTrace_3573810 : CollatzResearch.WordTrace tailWord_3573810 prefixEnd_3573810 611694099281589228546451 := by
  unfold tailWord_3573810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32586889795676050750003721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86898372788469468666676589 32586889795676050750003721)
  ·
    refine ⟨24440167346757038062502791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32586889795676050750003721 24440167346757038062502791)
    ·
      refine ⟨36660251020135557093754187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24440167346757038062502791 36660251020135557093754187)
      ·
        refine ⟨54990376530203335640631281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36660251020135557093754187 54990376530203335640631281)
        ·
          refine ⟨41242782397652501730473461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54990376530203335640631281 41242782397652501730473461)
          ·
            refine ⟨3866510849779922037231887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41242782397652501730473461 3866510849779922037231887)
            ·
              refine ⟨5799766274669883055847831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866510849779922037231887 5799766274669883055847831)
              ·
                refine ⟨8699649412004824583771747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799766274669883055847831 8699649412004824583771747)
                ·
                  refine ⟨13049474118007236875657621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699649412004824583771747 13049474118007236875657621)
                  ·
                    refine ⟨611694099281589228546451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13049474118007236875657621 611694099281589228546451)
                    ·
                      rfl

theorem cell23_3573810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3573810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573810 prefixEnd_3573810 := by exact prefixLift 3573810
  have htrace : WordTrace (prefixWord ++ tailWord_3573810) baseStart_3573810 baseEnd_3573810 := by
    simpa [prefixWord, tailWord_3573810, baseEnd_3573810] using wordTrace_append hprefix tailTrace_3573810
  have hstable : (prefixWord ++ tailWord_3573810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573810).length < 2 ^ (prefixWord ++ tailWord_3573810).sum := by decide
  have hdescent : baseEnd_3573810 < baseStart_3573810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573817 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3573817 : Nat := 118140960795 + 3573817 * 2 ^ 59
def prefixEnd_3573817 : Nat := 4983230072969 + 3 ^ 40 * 3573817 * 2
def baseEnd_3573817 : Nat := 1835085892209349158251821

theorem tailTrace_3573817 : CollatzResearch.WordTrace tailWord_3573817 prefixEnd_3573817 1835085892209349158251821 := by
  unfold tailWord_3573817
  simp only [CollatzResearch.WordTrace]
  refine ⟨130347814493678843195519705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86898542995785895463679803 130347814493678843195519705)
  ·
    refine ⟨97760860870259132396639779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130347814493678843195519705 97760860870259132396639779)
    ·
      refine ⟨146641291305388698594959669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97760860870259132396639779 146641291305388698594959669)
      ·
        refine ⟨13747621059880190493277469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146641291305388698594959669 13747621059880190493277469)
        ·
          refine ⟨5155357897455071434979051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13747621059880190493277469 5155357897455071434979051)
          ·
            refine ⟨7733036846182607152468577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155357897455071434979051 7733036846182607152468577)
            ·
              refine ⟨5799777634636955364351433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733036846182607152468577 5799777634636955364351433)
              ·
                refine ⟨4349833225977716523263575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5799777634636955364351433 4349833225977716523263575)
                ·
                  refine ⟨6524749838966574784895363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349833225977716523263575 6524749838966574784895363)
                  ·
                    refine ⟨9787124758449862177343045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6524749838966574784895363 9787124758449862177343045)
                    ·
                      refine ⟨1835085892209349158251821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9787124758449862177343045 1835085892209349158251821)
                      ·
                        rfl

theorem cell23_3573817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3573817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573817 prefixEnd_3573817 := by exact prefixLift 3573817
  have htrace : WordTrace (prefixWord ++ tailWord_3573817) baseStart_3573817 baseEnd_3573817 := by
    simpa [prefixWord, tailWord_3573817, baseEnd_3573817] using wordTrace_append hprefix tailTrace_3573817
  have hstable : (prefixWord ++ tailWord_3573817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573817).length < 2 ^ (prefixWord ++ tailWord_3573817).sum := by decide
  have hdescent : baseEnd_3573817 < baseStart_3573817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573823 : List Nat := [1, 1, 2, 2, 3, 1, 6, 7]
def baseStart_3573823 : Nat := 118140960795 + 3573823 * 2 ^ 59
def prefixEnd_3573823 : Nat := 4983230072969 + 3 ^ 40 * 3573823 * 2
def baseEnd_3573823 : Nat := 67966258262713930917659

theorem tailTrace_3573823 : CollatzResearch.WordTrace tailWord_3573823 prefixEnd_3573823 67966258262713930917659 := by
  unfold tailWord_3573823
  simp only [CollatzResearch.WordTrace]
  refine ⟨130348033331657106220238123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86898688887771404146825415 130348033331657106220238123)
  ·
    refine ⟨195522049997485659330357185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130348033331657106220238123 195522049997485659330357185)
    ·
      refine ⟨146641537498114244497767889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195522049997485659330357185 146641537498114244497767889)
      ·
        refine ⟨109981153123585683373325917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146641537498114244497767889 109981153123585683373325917)
        ·
          refine ⟨41242932421344631264997219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109981153123585683373325917 41242932421344631264997219)
          ·
            refine ⟨61864398632016946897495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41242932421344631264997219 61864398632016946897495829)
            ·
              refine ⟨2899893685875794385820117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61864398632016946897495829 2899893685875794385820117)
              ·
                refine ⟨67966258262713930917659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899893685875794385820117 67966258262713930917659)
                ·
                  rfl

theorem cell23_3573823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 7].length) (baseStart_3573823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573823 prefixEnd_3573823 := by exact prefixLift 3573823
  have htrace : WordTrace (prefixWord ++ tailWord_3573823) baseStart_3573823 baseEnd_3573823 := by
    simpa [prefixWord, tailWord_3573823, baseEnd_3573823] using wordTrace_append hprefix tailTrace_3573823
  have hstable : (prefixWord ++ tailWord_3573823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573823).length < 2 ^ (prefixWord ++ tailWord_3573823).sum := by decide
  have hdescent : baseEnd_3573823 < baseStart_3573823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573833 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_3573833 : Nat := 118140960795 + 3573833 * 2 ^ 59
def prefixEnd_3573833 : Nat := 4983230072969 + 3 ^ 40 * 3573833 * 2
def baseEnd_3573833 : Nat := 1835094107899821095651747

theorem tailTrace_3573833 : CollatzResearch.WordTrace tailWord_3573833 prefixEnd_3573833 1835094107899821095651747 := by
  unfold tailWord_3573833
  simp only [CollatzResearch.WordTrace]
  refine ⟨130348398061620877928102153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86898932041080585285401435 130348398061620877928102153)
  ·
    refine ⟨97761298546215658446076615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130348398061620877928102153 97761298546215658446076615)
    ·
      refine ⟨146641947819323487669114923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97761298546215658446076615 146641947819323487669114923)
      ·
        refine ⟨219962921728985231503672385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146641947819323487669114923 219962921728985231503672385)
        ·
          refine ⟨164972191296738923627754289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219962921728985231503672385 164972191296738923627754289)
          ·
            refine ⟨123729143472554192720815717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164972191296738923627754289 123729143472554192720815717)
            ·
              refine ⟨23199214401103911135152947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123729143472554192720815717 23199214401103911135152947)
              ·
                refine ⟨34798821601655866702729421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23199214401103911135152947 34798821601655866702729421)
                ·
                  refine ⟨13049558100620950013523533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34798821601655866702729421 13049558100620950013523533)
                  ·
                    refine ⟨4893584287732856255071325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13049558100620950013523533 4893584287732856255071325)
                    ·
                      refine ⟨1835094107899821095651747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893584287732856255071325 1835094107899821095651747)
                      ·
                        rfl

theorem cell23_3573833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_3573833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573833 prefixEnd_3573833 := by exact prefixLift 3573833
  have htrace : WordTrace (prefixWord ++ tailWord_3573833) baseStart_3573833 baseEnd_3573833 := by
    simpa [prefixWord, tailWord_3573833, baseEnd_3573833] using wordTrace_append hprefix tailTrace_3573833
  have hstable : (prefixWord ++ tailWord_3573833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573833).length < 2 ^ (prefixWord ++ tailWord_3573833).sum := by decide
  have hdescent : baseEnd_3573833 < baseStart_3573833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573837 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3573837 : Nat := 118140960795 + 3573837 * 2 ^ 59
def prefixEnd_3573837 : Nat := 4983230072969 + 3 ^ 40 * 3573837 * 2
def baseEnd_3573837 : Nat := 1835096161822439080001729

theorem tailTrace_3573837 : CollatzResearch.WordTrace tailWord_3573837 prefixEnd_3573837 1835096161822439080001729 := by
  unfold tailWord_3573837
  simp only [CollatzResearch.WordTrace]
  refine ⟨130348543953606386611247765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86899029302404257740831843 130348543953606386611247765)
  ·
    refine ⟨6110087997825299372402239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130348543953606386611247765 6110087997825299372402239)
    ·
      refine ⟨9165131996737949058603359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110087997825299372402239 9165131996737949058603359)
      ·
        refine ⟨13747697995106923587905039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165131996737949058603359 13747697995106923587905039)
        ·
          refine ⟨20621546992660385381857559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13747697995106923587905039 20621546992660385381857559)
          ·
            refine ⟨30932320488990578072786339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20621546992660385381857559 30932320488990578072786339)
            ·
              refine ⟨46398480733485867109179509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30932320488990578072786339 46398480733485867109179509)
              ·
                refine ⟨4349857568764300041485579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46398480733485867109179509 4349857568764300041485579)
                ·
                  refine ⟨6524786353146450062228369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349857568764300041485579 6524786353146450062228369)
                  ·
                    refine ⟨4893589764859837546671277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524786353146450062228369 4893589764859837546671277)
                    ·
                      refine ⟨1835096161822439080001729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893589764859837546671277 1835096161822439080001729)
                      ·
                        rfl

theorem cell23_3573837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3573837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573837 prefixEnd_3573837 := by exact prefixLift 3573837
  have htrace : WordTrace (prefixWord ++ tailWord_3573837) baseStart_3573837 baseEnd_3573837 := by
    simpa [prefixWord, tailWord_3573837, baseEnd_3573837] using wordTrace_append hprefix tailTrace_3573837
  have hstable : (prefixWord ++ tailWord_3573837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573837).length < 2 ^ (prefixWord ++ tailWord_3573837).sum := by decide
  have hdescent : baseEnd_3573837 < baseStart_3573837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573850 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_3573850 : Nat := 118140960795 + 3573850 * 2 ^ 59
def prefixEnd_3573850 : Nat := 4983230072969 + 3 ^ 40 * 3573850 * 2
def baseEnd_3573850 : Nat := 1835102837070947529139169

theorem tailTrace_3573850 : CollatzResearch.WordTrace tailWord_3573850 prefixEnd_3573850 1835102837070947529139169 := by
  unfold tailWord_3573850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32587254525639822457867751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86899345401706193220980669 32587254525639822457867751)
  ·
    refine ⟨48880881788459733686801627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32587254525639822457867751 48880881788459733686801627)
    ·
      refine ⟨73321322682689600530202441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48880881788459733686801627 73321322682689600530202441)
      ·
        refine ⟨54990992012017200397651831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73321322682689600530202441 54990992012017200397651831)
        ·
          refine ⟨82486488018025800596477747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54990992012017200397651831 82486488018025800596477747)
          ·
            refine ⟨123729732027038700894716621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82486488018025800596477747 123729732027038700894716621)
            ·
              refine ⟨46398649510139512835518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123729732027038700894716621 46398649510139512835518733)
              ·
                refine ⟨17399493566302317313319525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46398649510139512835518733 17399493566302317313319525)
                ·
                  refine ⟨3262405043681684496247411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17399493566302317313319525 3262405043681684496247411)
                  ·
                    refine ⟨4893607565522526744371117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3262405043681684496247411 4893607565522526744371117)
                    ·
                      refine ⟨1835102837070947529139169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893607565522526744371117 1835102837070947529139169)
                      ·
                        rfl

theorem cell23_3573850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_3573850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573850 prefixEnd_3573850 := by exact prefixLift 3573850
  have htrace : WordTrace (prefixWord ++ tailWord_3573850) baseStart_3573850 baseEnd_3573850 := by
    simpa [prefixWord, tailWord_3573850, baseEnd_3573850] using wordTrace_append hprefix tailTrace_3573850
  have hstable : (prefixWord ++ tailWord_3573850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573850).length < 2 ^ (prefixWord ++ tailWord_3573850).sum := by decide
  have hdescent : baseEnd_3573850 < baseStart_3573850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573920 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3573920 : Nat := 118140960795 + 3573920 * 2 ^ 59
def prefixEnd_3573920 : Nat := 4983230072969 + 3 ^ 40 * 3573920 * 2
def baseEnd_3573920 : Nat := 1835138780716762255263847

theorem tailTrace_3573920 : CollatzResearch.WordTrace tailWord_3573920 prefixEnd_3573920 1835138780716762255263847 := by
  unfold tailWord_3573920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65175785606152845893259607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86901047474870461191012809 65175785606152845893259607)
  ·
    refine ⟨97763678409229268839889411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65175785606152845893259607 97763678409229268839889411)
    ·
      refine ⟨146645517613843903259834117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97763678409229268839889411 146645517613843903259834117)
      ·
        refine ⟨27496034552595731861218897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146645517613843903259834117 27496034552595731861218897)
        ·
          refine ⟨20622025914446798895914173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27496034552595731861218897 20622025914446798895914173)
          ·
            refine ⟨7733259717917549585967815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20622025914446798895914173 7733259717917549585967815)
            ·
              refine ⟨11599889576876324378951723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733259717917549585967815 11599889576876324378951723)
              ·
                refine ⟨17399834365314486568427585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11599889576876324378951723 17399834365314486568427585)
                ·
                  refine ⟨13049875773985864926320689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17399834365314486568427585 13049875773985864926320689)
                  ·
                    refine ⟨9787406830489398694740517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13049875773985864926320689 9787406830489398694740517)
                    ·
                      refine ⟨1835138780716762255263847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9787406830489398694740517 1835138780716762255263847)
                      ·
                        rfl

theorem cell23_3573920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3573920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573920 prefixEnd_3573920 := by exact prefixLift 3573920
  have htrace : WordTrace (prefixWord ++ tailWord_3573920) baseStart_3573920 baseEnd_3573920 := by
    simpa [prefixWord, tailWord_3573920, baseEnd_3573920] using wordTrace_append hprefix tailTrace_3573920
  have hstable : (prefixWord ++ tailWord_3573920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573920).length < 2 ^ (prefixWord ++ tailWord_3573920).sum := by decide
  have hdescent : baseEnd_3573920 < baseStart_3573920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573924 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_3573924 : Nat := 118140960795 + 3573924 * 2 ^ 59
def prefixEnd_3573924 : Nat := 4983230072969 + 3 ^ 40 * 3573924 * 2
def baseEnd_3573924 : Nat := 1835140834639380239613829

theorem tailTrace_3573924 : CollatzResearch.WordTrace tailWord_3573924 prefixEnd_3573924 1835140834639380239613829 := by
  unfold tailWord_3573924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65175858552145600234832413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86901144736194133646443217 65175858552145600234832413)
  ·
    refine ⟨24440946957054600088062155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65175858552145600234832413 24440946957054600088062155)
    ·
      refine ⟨36661420435581900132093233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24440946957054600088062155 36661420435581900132093233)
      ·
        refine ⟨27496065326686425099069925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36661420435581900132093233 27496065326686425099069925)
        ·
          refine ⟨5155512248753704706075611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27496065326686425099069925 5155512248753704706075611)
          ·
            refine ⟨7733268373130557059113417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155512248753704706075611 7733268373130557059113417)
            ·
              refine ⟨5799951279847917794335063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733268373130557059113417 5799951279847917794335063)
              ·
                refine ⟨8699926919771876691502595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799951279847917794335063 8699926919771876691502595)
                ·
                  refine ⟨13049890379657815037253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699926919771876691502595 13049890379657815037253893)
                  ·
                    refine ⟨2446854446185840319485105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13049890379657815037253893 2446854446185840319485105)
                    ·
                      refine ⟨1835140834639380239613829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446854446185840319485105 1835140834639380239613829)
                      ·
                        rfl

theorem cell23_3573924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_3573924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573924 prefixEnd_3573924 := by exact prefixLift 3573924
  have htrace : WordTrace (prefixWord ++ tailWord_3573924) baseStart_3573924 baseEnd_3573924 := by
    simpa [prefixWord, tailWord_3573924, baseEnd_3573924] using wordTrace_append hprefix tailTrace_3573924
  have hstable : (prefixWord ++ tailWord_3573924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573924).length < 2 ^ (prefixWord ++ tailWord_3573924).sum := by decide
  have hdescent : baseEnd_3573924 < baseStart_3573924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573954 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3573954 : Nat := 118140960795 + 3573954 * 2 ^ 59
def prefixEnd_3573954 : Nat := 4983230072969 + 3 ^ 40 * 3573954 * 2
def baseEnd_3573954 : Nat := 1835156239059015122238691

theorem tailTrace_3573954 : CollatzResearch.WordTrace tailWord_3573954 prefixEnd_3573954 1835156239059015122238691 := by
  unfold tailWord_3573954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588202823545628898314229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86901874196121677062171277 32588202823545628898314229)
  ·
    refine ⟨3055144014707402709216959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32588202823545628898314229 3055144014707402709216959)
    ·
      refine ⟨4582716022061104063825439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055144014707402709216959 4582716022061104063825439)
      ·
        refine ⟨6874074033091656095738159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582716022061104063825439 6874074033091656095738159)
        ·
          refine ⟨10311111049637484143607239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874074033091656095738159 10311111049637484143607239)
          ·
            refine ⟨15466666574456226215410859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311111049637484143607239 15466666574456226215410859)
            ·
              refine ⟨23199999861684339323116289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15466666574456226215410859 23199999861684339323116289)
              ·
                refine ⟨17399999896263254492337217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23199999861684339323116289 17399999896263254492337217)
                ·
                  refine ⟨13049999922197440869252913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17399999896263254492337217 13049999922197440869252913)
                  ·
                    refine ⟨9787499941648080651939685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13049999922197440869252913 9787499941648080651939685)
                    ·
                      refine ⟨1835156239059015122238691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9787499941648080651939685 1835156239059015122238691)
                      ·
                        rfl

theorem cell23_3573954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3573954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573954 prefixEnd_3573954 := by exact prefixLift 3573954
  have htrace : WordTrace (prefixWord ++ tailWord_3573954) baseStart_3573954 baseEnd_3573954 := by
    simpa [prefixWord, tailWord_3573954, baseEnd_3573954] using wordTrace_append hprefix tailTrace_3573954
  have hstable : (prefixWord ++ tailWord_3573954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573954).length < 2 ^ (prefixWord ++ tailWord_3573954).sum := by decide
  have hdescent : baseEnd_3573954 < baseStart_3573954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573974 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3573974 : Nat := 118140960795 + 3573974 * 2 ^ 59
def prefixEnd_3573974 : Nat := 4983230072969 + 3 ^ 40 * 3573974 * 2
def baseEnd_3573974 : Nat := 1835166508672105043988599

theorem tailTrace_3573974 : CollatzResearch.WordTrace tailWord_3573974 prefixEnd_3573974 1835166508672105043988599 := by
  unfold tailWord_3573974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147096297131878688061561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86902360502740039339323317 8147096297131878688061561)
  ·
    refine ⟨6110322222848909016046171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8147096297131878688061561 6110322222848909016046171)
    ·
      refine ⟨9165483334273363524069257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110322222848909016046171 9165483334273363524069257)
      ·
        refine ⟨6874112500705022643051943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9165483334273363524069257 6874112500705022643051943)
        ·
          refine ⟨10311168751057533964577915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874112500705022643051943 10311168751057533964577915)
          ·
            refine ⟨15466753126586300946866873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311168751057533964577915 15466753126586300946866873)
            ·
              refine ⟨11600064844939725710150155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15466753126586300946866873 11600064844939725710150155)
              ·
                refine ⟨17400097267409588565225233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600064844939725710150155 17400097267409588565225233)
                ·
                  refine ⟨13050072950557191423918925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17400097267409588565225233 13050072950557191423918925)
                  ·
                    refine ⟨4893777356458946783969597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13050072950557191423918925 4893777356458946783969597)
                    ·
                      refine ⟨1835166508672105043988599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893777356458946783969597 1835166508672105043988599)
                      ·
                        rfl

theorem cell23_3573974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3573974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573974 prefixEnd_3573974 := by exact prefixLift 3573974
  have htrace : WordTrace (prefixWord ++ tailWord_3573974) baseStart_3573974 baseEnd_3573974 := by
    simpa [prefixWord, tailWord_3573974, baseEnd_3573974] using wordTrace_append hprefix tailTrace_3573974
  have hstable : (prefixWord ++ tailWord_3573974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573974).length < 2 ^ (prefixWord ++ tailWord_3573974).sum := by decide
  have hdescent : baseEnd_3573974 < baseStart_3573974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573993 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3573993 : Nat := 118140960795 + 3573993 * 2 ^ 59
def prefixEnd_3573993 : Nat := 4983230072969 + 3 ^ 40 * 3573993 * 2
def baseEnd_3573993 : Nat := 1835176264804540469651011

theorem tailTrace_3573993 : CollatzResearch.WordTrace tailWord_3573993 prefixEnd_3573993 1835176264804540469651011 := by
  unfold tailWord_3573993
  simp only [CollatzResearch.WordTrace]
  refine ⟨130354233741041225253926633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86902822494027483502617755 130354233741041225253926633)
  ·
    refine ⟨97765675305780918940444975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130354233741041225253926633 97765675305780918940444975)
    ·
      refine ⟨146648512958671378410667463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97765675305780918940444975 146648512958671378410667463)
      ·
        refine ⟨219972769438007067616001195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146648512958671378410667463 219972769438007067616001195)
        ·
          refine ⟨329959154157010601424001793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219972769438007067616001195 329959154157010601424001793)
          ·
            refine ⟨247469365617757951068001345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329959154157010601424001793 247469365617757951068001345)
            ·
              refine ⟨185602024213318463301001009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247469365617757951068001345 185602024213318463301001009)
              ·
                refine ⟨139201518159988847475750757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185602024213318463301001009 139201518159988847475750757)
                ·
                  refine ⟨26100284654997908901703267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139201518159988847475750757 26100284654997908901703267)
                  ·
                    refine ⟨39150426982496863352554901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26100284654997908901703267 39150426982496863352554901)
                    ·
                      refine ⟨1835176264804540469651011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39150426982496863352554901 1835176264804540469651011)
                      ·
                        rfl

theorem cell23_3573993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3573993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3573993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3573993 prefixEnd_3573993 := by exact prefixLift 3573993
  have htrace : WordTrace (prefixWord ++ tailWord_3573993) baseStart_3573993 baseEnd_3573993 := by
    simpa [prefixWord, tailWord_3573993, baseEnd_3573993] using wordTrace_append hprefix tailTrace_3573993
  have hstable : (prefixWord ++ tailWord_3573993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573993).length < 2 ^ (prefixWord ++ tailWord_3573993).sum := by decide
  have hdescent : baseEnd_3573993 < baseStart_3573993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574000 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_3574000 : Nat := 118140960795 + 3574000 * 2 ^ 59
def prefixEnd_3574000 : Nat := 4983230072969 + 3 ^ 40 * 3574000 * 2
def baseEnd_3574000 : Nat := 1835179859169121942263479

theorem tailTrace_3574000 : CollatzResearch.WordTrace tailWord_3574000 prefixEnd_3574000 1835179859169121942263479 := by
  unfold tailWord_3574000
  simp only [CollatzResearch.WordTrace]
  refine ⟨65177244526007932724715727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86902992701343910299620969 65177244526007932724715727)
  ·
    refine ⟨97765866789011899087073591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65177244526007932724715727 97765866789011899087073591)
    ·
      refine ⟨146648800183517848630610387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97765866789011899087073591 146648800183517848630610387)
      ·
        refine ⟨219973200275276772945915581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146648800183517848630610387 219973200275276772945915581)
        ·
          refine ⟨82489950103228789854718343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219973200275276772945915581 82489950103228789854718343)
          ·
            refine ⟨123734925154843184782077515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82489950103228789854718343 123734925154843184782077515)
            ·
              refine ⟨185602387732264777173116273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123734925154843184782077515 185602387732264777173116273)
              ·
                refine ⟨139201790799198582879837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185602387732264777173116273 139201790799198582879837205)
                ·
                  refine ⟨6525083943712433572492369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139201790799198582879837205 6525083943712433572492369)
                  ·
                    refine ⟨4893812957784325179369277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525083943712433572492369 4893812957784325179369277)
                    ·
                      refine ⟨1835179859169121942263479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893812957784325179369277 1835179859169121942263479)
                      ·
                        rfl

theorem cell23_3574000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_3574000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574000 prefixEnd_3574000 := by exact prefixLift 3574000
  have htrace : WordTrace (prefixWord ++ tailWord_3574000) baseStart_3574000 baseEnd_3574000 := by
    simpa [prefixWord, tailWord_3574000, baseEnd_3574000] using wordTrace_append hprefix tailTrace_3574000
  have hstable : (prefixWord ++ tailWord_3574000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574000).length < 2 ^ (prefixWord ++ tailWord_3574000).sum := by decide
  have hdescent : baseEnd_3574000 < baseStart_3574000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574003 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 10]
def baseStart_3574003 : Nat := 118140960795 + 3574003 * 2 ^ 59
def prefixEnd_3574003 : Nat := 4983230072969 + 3 ^ 40 * 3574003 * 2
def baseEnd_3574003 : Nat := 203909044401231714502885

theorem tailTrace_3574003 : CollatzResearch.WordTrace tailWord_3574003 prefixEnd_3574003 203909044401231714502885 := by
  unfold tailWord_3574003
  simp only [CollatzResearch.WordTrace]
  refine ⟨130354598471004996961790663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86903065647336664641193775 130354598471004996961790663)
  ·
    refine ⟨195531897706507495442685995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130354598471004996961790663 195531897706507495442685995)
    ·
      refine ⟨293297846559761243164028993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195531897706507495442685995 293297846559761243164028993)
      ·
        refine ⟨219973384919820932373021745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293297846559761243164028993 219973384919820932373021745)
        ·
          refine ⟨164980038689865699279766309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219973384919820932373021745 164980038689865699279766309)
          ·
            refine ⟨30933757254349818614956183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164980038689865699279766309 30933757254349818614956183)
            ·
              refine ⟨46400635881524727922434275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30933757254349818614956183 46400635881524727922434275)
              ·
                refine ⟨69600953822287091883651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46400635881524727922434275 69600953822287091883651413)
                ·
                  refine ⟨203909044401231714502885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69600953822287091883651413 203909044401231714502885)
                  ·
                    rfl

theorem cell23_3574003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 10].length) (baseStart_3574003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574003 prefixEnd_3574003 := by exact prefixLift 3574003
  have htrace : WordTrace (prefixWord ++ tailWord_3574003) baseStart_3574003 baseEnd_3574003 := by
    simpa [prefixWord, tailWord_3574003, baseEnd_3574003] using wordTrace_append hprefix tailTrace_3574003
  have hstable : (prefixWord ++ tailWord_3574003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574003).length < 2 ^ (prefixWord ++ tailWord_3574003).sum := by decide
  have hdescent : baseEnd_3574003 < baseStart_3574003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574017 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_3574017 : Nat := 118140960795 + 3574017 * 2 ^ 59
def prefixEnd_3574017 : Nat := 4983230072969 + 3 ^ 40 * 3574017 * 2
def baseEnd_3574017 : Nat := 1835188588340248375750901

theorem tailTrace_3574017 : CollatzResearch.WordTrace tailWord_3574017 prefixEnd_3574017 1835188588340248375750901 := by
  unfold tailWord_3574017
  simp only [CollatzResearch.WordTrace]
  refine ⟨130355109092954277352800305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86903406061969518235200203 130355109092954277352800305)
  ·
    refine ⟨97766331819715708014600229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130355109092954277352800305 97766331819715708014600229)
    ·
      refine ⟨18331187216196695252737543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97766331819715708014600229 18331187216196695252737543)
      ·
        refine ⟨27496780824295042879106315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18331187216196695252737543 27496780824295042879106315)
        ·
          refine ⟨41245171236442564318659473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27496780824295042879106315 41245171236442564318659473)
          ·
            refine ⟨30933878427331923238994605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41245171236442564318659473 30933878427331923238994605)
            ·
              refine ⟨11600204410249471214622977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30933878427331923238994605 11600204410249471214622977)
              ·
                refine ⟨8700153307687103410967233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600204410249471214622977 8700153307687103410967233)
                ·
                  refine ⟨6525114980765327558225425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700153307687103410967233 6525114980765327558225425)
                  ·
                    refine ⟨4893836235573995668669069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525114980765327558225425 4893836235573995668669069)
                    ·
                      refine ⟨1835188588340248375750901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4893836235573995668669069 1835188588340248375750901)
                      ·
                        rfl

theorem cell23_3574017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_3574017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574017 prefixEnd_3574017 := by exact prefixLift 3574017
  have htrace : WordTrace (prefixWord ++ tailWord_3574017) baseStart_3574017 baseEnd_3574017 := by
    simpa [prefixWord, tailWord_3574017, baseEnd_3574017] using wordTrace_append hprefix tailTrace_3574017
  have hstable : (prefixWord ++ tailWord_3574017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574017).length < 2 ^ (prefixWord ++ tailWord_3574017).sum := by decide
  have hdescent : baseEnd_3574017 < baseStart_3574017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574024 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_3574024 : Nat := 118140960795 + 3574024 * 2 ^ 59
def prefixEnd_3574024 : Nat := 4983230072969 + 3 ^ 40 * 3574024 * 2
def baseEnd_3574024 : Nat := 611730727568276616121123

theorem tailTrace_3574024 : CollatzResearch.WordTrace tailWord_3574024 prefixEnd_3574024 611730727568276616121123 := by
  unfold tailWord_3574024
  simp only [CollatzResearch.WordTrace]
  refine ⟨65177682201964458774152563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86903576269285945032203417 65177682201964458774152563)
  ·
    refine ⟨97766523302946688161228845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65177682201964458774152563 97766523302946688161228845)
    ·
      refine ⟨36662446238605008060460817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97766523302946688161228845 36662446238605008060460817)
      ·
        refine ⟨27496834678953756045345613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36662446238605008060460817 27496834678953756045345613)
        ·
          refine ⟨10311313004607658517004605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27496834678953756045345613 10311313004607658517004605)
          ·
            refine ⟨3866742376727871943876727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10311313004607658517004605 3866742376727871943876727)
            ·
              refine ⟨5800113565091807915815091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866742376727871943876727 5800113565091807915815091)
              ·
                refine ⟨8700170347637711873722637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800113565091807915815091 8700170347637711873722637)
                ·
                  refine ⟨3262563880364141952645989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8700170347637711873722637 3262563880364141952645989)
                  ·
                    refine ⟨611730727568276616121123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3262563880364141952645989 611730727568276616121123)
                    ·
                      rfl

theorem cell23_3574024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_3574024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574024 prefixEnd_3574024 := by exact prefixLift 3574024
  have htrace : WordTrace (prefixWord ++ tailWord_3574024) baseStart_3574024 baseEnd_3574024 := by
    simpa [prefixWord, tailWord_3574024, baseEnd_3574024] using wordTrace_append hprefix tailTrace_3574024
  have hstable : (prefixWord ++ tailWord_3574024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574024).length < 2 ^ (prefixWord ++ tailWord_3574024).sum := by decide
  have hdescent : baseEnd_3574024 < baseStart_3574024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574037 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 6]
def baseStart_3574037 : Nat := 118140960795 + 3574037 * 2 ^ 59
def prefixEnd_3574037 : Nat := 4983230072969 + 3 ^ 40 * 3574037 * 2
def baseEnd_3574037 : Nat := 203910984217037588611201

theorem tailTrace_3574037 : CollatzResearch.WordTrace tailWord_3574037 prefixEnd_3574037 203910984217037588611201 := by
  unfold tailWord_3574037
  simp only [CollatzResearch.WordTrace]
  refine ⟨130355838552881820768528365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86903892368587880512352243 130355838552881820768528365)
  ·
    refine ⟨48883439457330682788198137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130355838552881820768528365 48883439457330682788198137)
    ·
      refine ⟨36662579592998012091148603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48883439457330682788198137 36662579592998012091148603)
      ·
        refine ⟨54993869389497018136722905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36662579592998012091148603 54993869389497018136722905)
        ·
          refine ⟨41245402042122763602542179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54993869389497018136722905 41245402042122763602542179)
          ·
            refine ⟨61868103063184145403813269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41245402042122763602542179 61868103063184145403813269)
            ·
              refine ⟨2900067331086756815803747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61868103063184145403813269 2900067331086756815803747)
              ·
                refine ⟨4350100996630135223705621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900067331086756815803747 4350100996630135223705621)
                ·
                  refine ⟨203910984217037588611201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4350100996630135223705621 203910984217037588611201)
                  ·
                    rfl

theorem cell23_3574037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_3574037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574037 prefixEnd_3574037 := by exact prefixLift 3574037
  have htrace : WordTrace (prefixWord ++ tailWord_3574037) baseStart_3574037 baseEnd_3574037 := by
    simpa [prefixWord, tailWord_3574037, baseEnd_3574037] using wordTrace_append hprefix tailTrace_3574037
  have hstable : (prefixWord ++ tailWord_3574037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574037).length < 2 ^ (prefixWord ++ tailWord_3574037).sum := by decide
  have hdescent : baseEnd_3574037 < baseStart_3574037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574074 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_3574074 : Nat := 118140960795 + 3574074 * 2 ^ 59
def prefixEnd_3574074 : Nat := 4983230072969 + 3 ^ 40 * 3574074 * 2
def baseEnd_3574074 : Nat := 1835217856737554652738139

theorem tailTrace_3574074 : CollatzResearch.WordTrace tailWord_3574074 prefixEnd_3574074 1835217856737554652738139 := by
  unfold tailWord_3574074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32589297013436944021906319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86904792035831850725083517 32589297013436944021906319)
  ·
    refine ⟨48883945520155416032859479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32589297013436944021906319 48883945520155416032859479)
    ·
      refine ⟨73325918280233124049289219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48883945520155416032859479 73325918280233124049289219)
      ·
        refine ⟨109988877420349686073933829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73325918280233124049289219 109988877420349686073933829)
        ·
          refine ⟨20622914516315566138862593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109988877420349686073933829 20622914516315566138862593)
          ·
            refine ⟨15467185887236674604146945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20622914516315566138862593 15467185887236674604146945)
            ·
              refine ⟨11600389415427505953110209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467185887236674604146945 11600389415427505953110209)
              ·
                refine ⟨8700292061570629464832657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600389415427505953110209 8700292061570629464832657)
                ·
                  refine ⟨6525219046177972098624493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700292061570629464832657 6525219046177972098624493)
                  ·
                    refine ⟨2446957142316739536984185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6525219046177972098624493 2446957142316739536984185)
                    ·
                      refine ⟨1835217856737554652738139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2446957142316739536984185 1835217856737554652738139)
                      ·
                        rfl

theorem cell23_3574074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_3574074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574074 prefixEnd_3574074 := by exact prefixLift 3574074
  have htrace : WordTrace (prefixWord ++ tailWord_3574074) baseStart_3574074 baseEnd_3574074 := by
    simpa [prefixWord, tailWord_3574074, baseEnd_3574074] using wordTrace_append hprefix tailTrace_3574074
  have hstable : (prefixWord ++ tailWord_3574074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574074).length < 2 ^ (prefixWord ++ tailWord_3574074).sum := by decide
  have hdescent : baseEnd_3574074 < baseStart_3574074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574097 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3574097 : Nat := 118140960795 + 3574097 * 2 ^ 59
def prefixEnd_3574097 : Nat := 4983230072969 + 3 ^ 40 * 3574097 * 2
def baseEnd_3574097 : Nat := 611743222264202687583511

theorem tailTrace_3574097 : CollatzResearch.WordTrace tailWord_3574097 prefixEnd_3574097 611743222264202687583511 := by
  unfold tailWord_3574097
  simp only [CollatzResearch.WordTrace]
  refine ⟨130358026932664451015712545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86905351288442967343808363 130358026932664451015712545)
  ·
    refine ⟨97768520199498338261784409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130358026932664451015712545 97768520199498338261784409)
    ·
      refine ⟨73326390149623753696338307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97768520199498338261784409 73326390149623753696338307)
      ·
        refine ⟨109989585224435630544507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73326390149623753696338307 109989585224435630544507461)
        ·
          refine ⟨20623047229581680727095149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109989585224435630544507461 20623047229581680727095149)
          ·
            refine ⟨7733642711093130272660681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20623047229581680727095149 7733642711093130272660681)
            ·
              refine ⟨5800232033319847704495511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733642711093130272660681 5800232033319847704495511)
              ·
                refine ⟨8700348049979771556743267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800232033319847704495511 8700348049979771556743267)
                ·
                  refine ⟨13050522074969657335114901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8700348049979771556743267 13050522074969657335114901)
                  ·
                    refine ⟨611743222264202687583511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13050522074969657335114901 611743222264202687583511)
                    ·
                      rfl

theorem cell23_3574097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3574097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574097 prefixEnd_3574097 := by exact prefixLift 3574097
  have htrace : WordTrace (prefixWord ++ tailWord_3574097) baseStart_3574097 baseEnd_3574097 := by
    simpa [prefixWord, tailWord_3574097, baseEnd_3574097] using wordTrace_append hprefix tailTrace_3574097
  have hstable : (prefixWord ++ tailWord_3574097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574097).length < 2 ^ (prefixWord ++ tailWord_3574097).sum := by decide
  have hdescent : baseEnd_3574097 < baseStart_3574097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574117 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3574117 : Nat := 118140960795 + 3574117 * 2 ^ 59
def prefixEnd_3574117 : Nat := 4983230072969 + 3 ^ 40 * 3574117 * 2
def baseEnd_3574117 : Nat := 1835239936405697984500441

theorem tailTrace_3574117 : CollatzResearch.WordTrace tailWord_3574117 prefixEnd_3574117 1835239936405697984500441 := by
  unfold tailWord_3574117
  simp only [CollatzResearch.WordTrace]
  refine ⟨130358756392591994431440605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86905837595061329620960403 130358756392591994431440605)
  ·
    refine ⟨48884533647221997911790227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130358756392591994431440605 48884533647221997911790227)
    ·
      refine ⟨73326800470832996867685341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48884533647221997911790227 73326800470832996867685341)
      ·
        refine ⟨27497550176562373825382003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73326800470832996867685341 27497550176562373825382003)
        ·
          refine ⟨41246325264843560738073005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27497550176562373825382003 41246325264843560738073005)
          ·
            refine ⟨15467371974316335276777377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41246325264843560738073005 15467371974316335276777377)
            ·
              refine ⟨11600528980737251457583033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467371974316335276777377 11600528980737251457583033)
              ·
                refine ⟨8700396735552938593187275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600528980737251457583033 8700396735552938593187275)
                ·
                  refine ⟨13050595103329407889780913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8700396735552938593187275 13050595103329407889780913)
                  ·
                    refine ⟨9787946327497055917335685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13050595103329407889780913 9787946327497055917335685)
                    ·
                      refine ⟨1835239936405697984500441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9787946327497055917335685 1835239936405697984500441)
                      ·
                        rfl

theorem cell23_3574117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3574117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574117 prefixEnd_3574117 := by exact prefixLift 3574117
  have htrace : WordTrace (prefixWord ++ tailWord_3574117) baseStart_3574117 baseEnd_3574117 := by
    simpa [prefixWord, tailWord_3574117, baseEnd_3574117] using wordTrace_append hprefix tailTrace_3574117
  have hstable : (prefixWord ++ tailWord_3574117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574117).length < 2 ^ (prefixWord ++ tailWord_3574117).sum := by decide
  have hdescent : baseEnd_3574117 < baseStart_3574117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574140 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_3574140 : Nat := 118140960795 + 3574140 * 2 ^ 59
def prefixEnd_3574140 : Nat := 4983230072969 + 3 ^ 40 * 3574140 * 2
def baseEnd_3574140 : Nat := 611750582153583798170945

theorem tailTrace_3574140 : CollatzResearch.WordTrace tailWord_3574140 prefixEnd_3574140 611750582153583798170945 := by
  unfold tailWord_3574140
  simp only [CollatzResearch.WordTrace]
  refine ⟨65179797635754334679763937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86906396847672446239685249 65179797635754334679763937)
  ·
    refine ⟨48884848226815751009822953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65179797635754334679763937 48884848226815751009822953)
    ·
      refine ⟨36663636170111813257367215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48884848226815751009822953 36663636170111813257367215)
      ·
        refine ⟨54995454255167719886050823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663636170111813257367215 54995454255167719886050823)
        ·
          refine ⟨82493181382751579829076235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54995454255167719886050823 82493181382751579829076235)
          ·
            refine ⟨123739772074127369743614353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82493181382751579829076235 123739772074127369743614353)
            ·
              refine ⟨92804829055595527307710765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123739772074127369743614353 92804829055595527307710765)
              ·
                refine ⟨34801810895848322740391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92804829055595527307710765 34801810895848322740391537)
                ·
                  refine ⟨26101358171886242055293653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34801810895848322740391537 26101358171886242055293653)
                  ·
                    refine ⟨611750582153583798170945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26101358171886242055293653 611750582153583798170945)
                    ·
                      rfl

theorem cell23_3574140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_3574140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574140 prefixEnd_3574140 := by exact prefixLift 3574140
  have htrace : WordTrace (prefixWord ++ tailWord_3574140) baseStart_3574140 baseEnd_3574140 := by
    simpa [prefixWord, tailWord_3574140, baseEnd_3574140] using wordTrace_append hprefix tailTrace_3574140
  have hstable : (prefixWord ++ tailWord_3574140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574140).length < 2 ^ (prefixWord ++ tailWord_3574140).sum := by decide
  have hdescent : baseEnd_3574140 < baseStart_3574140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574166 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3574166 : Nat := 118140960795 + 3574166 * 2 ^ 59
def prefixEnd_3574166 : Nat := 4983230072969 + 3 ^ 40 * 3574166 * 2
def baseEnd_3574166 : Nat := 1835265096957768292787717

theorem tailTrace_3574166 : CollatzResearch.WordTrace tailWord_3574166 prefixEnd_3574166 1835265096957768292787717 := by
  unfold tailWord_3574166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147533973088404737498397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86907029046276317199982901 8147533973088404737498397)
  ·
    refine ⟨3055325239908151776561899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8147533973088404737498397 3055325239908151776561899)
    ·
      refine ⟨4582987859862227664842849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055325239908151776561899 4582987859862227664842849)
      ·
        refine ⟨3437240894896670748632137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4582987859862227664842849 3437240894896670748632137)
        ·
          refine ⟨2577930671172503061474103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437240894896670748632137 2577930671172503061474103)
          ·
            refine ⟨3866896006758754592211155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577930671172503061474103 3866896006758754592211155)
            ·
              refine ⟨5800344010138131888316733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866896006758754592211155 5800344010138131888316733)
              ·
                refine ⟨2175129003801799458118775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800344010138131888316733 2175129003801799458118775)
                ·
                  refine ⟨3262693505702699187178163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175129003801799458118775 3262693505702699187178163)
                  ·
                    refine ⟨4894040258554048780767245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3262693505702699187178163 4894040258554048780767245)
                    ·
                      refine ⟨1835265096957768292787717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894040258554048780767245 1835265096957768292787717)
                      ·
                        rfl

theorem cell23_3574166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3574166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574166 prefixEnd_3574166 := by exact prefixLift 3574166
  have htrace : WordTrace (prefixWord ++ tailWord_3574166) baseStart_3574166 baseEnd_3574166 := by
    simpa [prefixWord, tailWord_3574166, baseEnd_3574166] using wordTrace_append hprefix tailTrace_3574166
  have hstable : (prefixWord ++ tailWord_3574166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574166).length < 2 ^ (prefixWord ++ tailWord_3574166).sum := by decide
  have hdescent : baseEnd_3574166 < baseStart_3574166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574234 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_3574234 : Nat := 118140960795 + 3574234 * 2 ^ 59
def prefixEnd_3574234 : Nat := 4983230072969 + 3 ^ 40 * 3574234 * 2
def baseEnd_3574234 : Nat := 203922223738030447415267

theorem tailTrace_3574234 : CollatzResearch.WordTrace tailWord_3574234 prefixEnd_3574234 203922223738030447415267 := by
  unfold tailWord_3574234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32590755933292030853362439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86908682488778748942299837 32590755933292030853362439)
  ·
    refine ⟨48886133899938046280043659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32590755933292030853362439 48886133899938046280043659)
    ·
      refine ⟨73329200849907069420065489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886133899938046280043659 73329200849907069420065489)
      ·
        refine ⟨54996900637430302065049117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73329200849907069420065489 54996900637430302065049117)
        ·
          refine ⟨20623837739036363274393419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54996900637430302065049117 20623837739036363274393419)
          ·
            refine ⟨30935756608554544911590129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623837739036363274393419 30935756608554544911590129)
            ·
              refine ⟨23201817456415908683692597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30935756608554544911590129 23201817456415908683692597)
              ·
                refine ⟨2175170386538991439096181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23201817456415908683692597 2175170386538991439096181)
                ·
                  refine ⟨203922223738030447415267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175170386538991439096181 203922223738030447415267)
                  ·
                    rfl

theorem cell23_3574234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_3574234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574234 prefixEnd_3574234 := by exact prefixLift 3574234
  have htrace : WordTrace (prefixWord ++ tailWord_3574234) baseStart_3574234 baseEnd_3574234 := by
    simpa [prefixWord, tailWord_3574234, baseEnd_3574234] using wordTrace_append hprefix tailTrace_3574234
  have hstable : (prefixWord ++ tailWord_3574234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574234).length < 2 ^ (prefixWord ++ tailWord_3574234).sum := by decide
  have hdescent : baseEnd_3574234 < baseStart_3574234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574245 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3574245 : Nat := 118140960795 + 3574245 * 2 ^ 59
def prefixEnd_3574245 : Nat := 4983230072969 + 3 ^ 40 * 3574245 * 2
def baseEnd_3574245 : Nat := 1835305661929473483699853

theorem tailTrace_3574245 : CollatzResearch.WordTrace tailWord_3574245 prefixEnd_3574245 1835305661929473483699853 := by
  unfold tailWord_3574245
  simp only [CollatzResearch.WordTrace]
  refine ⟨130363424936128272292100189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86908949957418848194733459 130363424936128272292100189)
  ·
    refine ⟨48886284351048102109537571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130363424936128272292100189 48886284351048102109537571)
    ·
      refine ⟨73329426526572153164306357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886284351048102109537571 73329426526572153164306357)
      ·
        refine ⟨6874633736866139359153721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73329426526572153164306357 6874633736866139359153721)
        ·
          refine ⟨5155975302649604519365291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6874633736866139359153721 5155975302649604519365291)
          ·
            refine ⟨7733962953974406779047937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155975302649604519365291 7733962953974406779047937)
            ·
              refine ⟨5800472215480805084285953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733962953974406779047937 5800472215480805084285953)
              ·
                refine ⟨4350354161610603813214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5800472215480805084285953 4350354161610603813214465)
                ·
                  refine ⟨3262765621207952859910849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350354161610603813214465 3262765621207952859910849)
                  ·
                    refine ⟨2447074215905964644933137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3262765621207952859910849 2447074215905964644933137)
                    ·
                      refine ⟨1835305661929473483699853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447074215905964644933137 1835305661929473483699853)
                      ·
                        rfl

theorem cell23_3574245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3574245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574245 prefixEnd_3574245 := by exact prefixLift 3574245
  have htrace : WordTrace (prefixWord ++ tailWord_3574245) baseStart_3574245 baseEnd_3574245 := by
    simpa [prefixWord, tailWord_3574245, baseEnd_3574245] using wordTrace_append hprefix tailTrace_3574245
  have hstable : (prefixWord ++ tailWord_3574245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574245).length < 2 ^ (prefixWord ++ tailWord_3574245).sum := by decide
  have hdescent : baseEnd_3574245 < baseStart_3574245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574257 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3574257 : Nat := 118140960795 + 3574257 * 2 ^ 59
def prefixEnd_3574257 : Nat := 4983230072969 + 3 ^ 40 * 3574257 * 2
def baseEnd_3574257 : Nat := 1835311823697327436749797

theorem tailTrace_3574257 : CollatzResearch.WordTrace tailWord_3574257 prefixEnd_3574257 1835311823697327436749797 := by
  unfold tailWord_3574257
  simp only [CollatzResearch.WordTrace]
  refine ⟨130363862612084798341537025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86909241741389865561024683 130363862612084798341537025)
  ·
    refine ⟨97772896959063598756152769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130363862612084798341537025 97772896959063598756152769)
    ·
      refine ⟨73329672719297699067114577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97772896959063598756152769 73329672719297699067114577)
      ·
        refine ⟨54997254539473274300335933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73329672719297699067114577 54997254539473274300335933)
        ·
          refine ⟨20623970452302477862625975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54997254539473274300335933 20623970452302477862625975)
          ·
            refine ⟨30935955678453716793938963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623970452302477862625975 30935955678453716793938963)
            ·
              refine ⟨46403933517680575190908445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30935955678453716793938963 46403933517680575190908445)
              ·
                refine ⟨17401475069130215696590667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46403933517680575190908445 17401475069130215696590667)
                ·
                  refine ⟨26102212603695323544886001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17401475069130215696590667 26102212603695323544886001)
                  ·
                    refine ⟨19576659452771492658664501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26102212603695323544886001 19576659452771492658664501)
                    ·
                      refine ⟨1835311823697327436749797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19576659452771492658664501 1835311823697327436749797)
                      ·
                        rfl

theorem cell23_3574257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3574257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574257 prefixEnd_3574257 := by exact prefixLift 3574257
  have htrace : WordTrace (prefixWord ++ tailWord_3574257) baseStart_3574257 baseEnd_3574257 := by
    simpa [prefixWord, tailWord_3574257, baseEnd_3574257] using wordTrace_append hprefix tailTrace_3574257
  have hstable : (prefixWord ++ tailWord_3574257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574257).length < 2 ^ (prefixWord ++ tailWord_3574257).sum := by decide
  have hdescent : baseEnd_3574257 < baseStart_3574257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574284 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3574284 : Nat := 118140960795 + 3574284 * 2 ^ 59
def prefixEnd_3574284 : Nat := 4983230072969 + 3 ^ 40 * 3574284 * 2
def baseEnd_3574284 : Nat := 1835325687674998831112173

theorem tailTrace_3574284 : CollatzResearch.WordTrace tailWord_3574284 prefixEnd_3574284 1835325687674998831112173 := by
  unfold tailWord_3574284
  simp only [CollatzResearch.WordTrace]
  refine ⟨65182423691493490976384953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86909898255324654635179937 65182423691493490976384953)
  ·
    refine ⟨48886817768620118232288715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65182423691493490976384953 48886817768620118232288715)
    ·
      refine ⟨73330226652930177348433073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886817768620118232288715 73330226652930177348433073)
      ·
        refine ⟨54997669989697633011324805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73330226652930177348433073 54997669989697633011324805)
        ·
          refine ⟨10312063123068306189623401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54997669989697633011324805 10312063123068306189623401)
          ·
            refine ⟨7734047342301229642217551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312063123068306189623401 7734047342301229642217551)
            ·
              refine ⟨11601071013451844463326327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734047342301229642217551 11601071013451844463326327)
              ·
                refine ⟨17401606520177766694989491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11601071013451844463326327 17401606520177766694989491)
                ·
                  refine ⟨26102409780266650042484237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17401606520177766694989491 26102409780266650042484237)
                  ·
                    refine ⟨9788403667599993765931589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26102409780266650042484237 9788403667599993765931589)
                    ·
                      refine ⟨1835325687674998831112173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9788403667599993765931589 1835325687674998831112173)
                      ·
                        rfl

theorem cell23_3574284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3574284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574284 prefixEnd_3574284 := by exact prefixLift 3574284
  have htrace : WordTrace (prefixWord ++ tailWord_3574284) baseStart_3574284 baseEnd_3574284 := by
    simpa [prefixWord, tailWord_3574284, baseEnd_3574284] using wordTrace_append hprefix tailTrace_3574284
  have hstable : (prefixWord ++ tailWord_3574284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574284).length < 2 ^ (prefixWord ++ tailWord_3574284).sum := by decide
  have hdescent : baseEnd_3574284 < baseStart_3574284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574285 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3574285 : Nat := 118140960795 + 3574285 * 2 ^ 59
def prefixEnd_3574285 : Nat := 4983230072969 + 3 ^ 40 * 3574285 * 2
def baseEnd_3574285 : Nat := 203925133461739258577741

theorem tailTrace_3574285 : CollatzResearch.WordTrace tailWord_3574285 prefixEnd_3574285 203925133461739258577741 := by
  unfold tailWord_3574285
  simp only [CollatzResearch.WordTrace]
  refine ⟨130364883855983359123556309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86909922570655572749037539 130364883855983359123556309)
  ·
    refine ⟨3055426965374609979458351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130364883855983359123556309 3055426965374609979458351)
    ·
      refine ⟨4583140448061914969187527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055426965374609979458351 4583140448061914969187527)
      ·
        refine ⟨6874710672092872453781291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583140448061914969187527 6874710672092872453781291)
        ·
          refine ⟨10312066008139308680671937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874710672092872453781291 10312066008139308680671937)
          ·
            refine ⟨7734049506104481510503953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312066008139308680671937 7734049506104481510503953)
            ·
              refine ⟨5800537129578361132877965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734049506104481510503953 5800537129578361132877965)
              ·
                refine ⟨2175201423591885424829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800537129578361132877965 2175201423591885424829237)
                ·
                  refine ⟨203925133461739258577741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175201423591885424829237 203925133461739258577741)
                  ·
                    rfl

theorem cell23_3574285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3574285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574285 prefixEnd_3574285 := by exact prefixLift 3574285
  have htrace : WordTrace (prefixWord ++ tailWord_3574285) baseStart_3574285 baseEnd_3574285 := by
    simpa [prefixWord, tailWord_3574285, baseEnd_3574285] using wordTrace_append hprefix tailTrace_3574285
  have hstable : (prefixWord ++ tailWord_3574285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574285).length < 2 ^ (prefixWord ++ tailWord_3574285).sum := by decide
  have hdescent : baseEnd_3574285 < baseStart_3574285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574301 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_3574301 : Nat := 118140960795 + 3574301 * 2 ^ 59
def prefixEnd_3574301 : Nat := 4983230072969 + 3 ^ 40 * 3574301 * 2
def baseEnd_3574301 : Nat := 1835334416846125264599595

theorem tailTrace_3574301 : CollatzResearch.WordTrace tailWord_3574301 prefixEnd_3574301 1835334416846125264599595 := by
  unfold tailWord_3574301
  simp only [CollatzResearch.WordTrace]
  refine ⟨130365467423925393856138757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86910311615950262570759171 130365467423925393856138757)
  ·
    refine ⟨24443525141986011348026017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130365467423925393856138757 24443525141986011348026017)
    ·
      refine ⟨18332643856489508511019513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24443525141986011348026017 18332643856489508511019513)
      ·
        refine ⟨13749482892367131383264635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18332643856489508511019513 13749482892367131383264635)
        ·
          refine ⟨20624224338550697074896953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13749482892367131383264635 20624224338550697074896953)
          ·
            refine ⟨15468168253913022806172715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20624224338550697074896953 15468168253913022806172715)
            ·
              refine ⟨23202252380869534209259073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468168253913022806172715 23202252380869534209259073)
              ·
                refine ⟨17401689285652150656944305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23202252380869534209259073 17401689285652150656944305)
                ·
                  refine ⟨13051266964239112992708229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17401689285652150656944305 13051266964239112992708229)
                  ·
                    refine ⟨2447112555794833686132793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13051266964239112992708229 2447112555794833686132793)
                    ·
                      refine ⟨1835334416846125264599595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447112555794833686132793 1835334416846125264599595)
                      ·
                        rfl

theorem cell23_3574301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_3574301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574301 prefixEnd_3574301 := by exact prefixLift 3574301
  have htrace : WordTrace (prefixWord ++ tailWord_3574301) baseStart_3574301 baseEnd_3574301 := by
    simpa [prefixWord, tailWord_3574301, baseEnd_3574301] using wordTrace_append hprefix tailTrace_3574301
  have hstable : (prefixWord ++ tailWord_3574301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574301).length < 2 ^ (prefixWord ++ tailWord_3574301).sum := by decide
  have hdescent : baseEnd_3574301 < baseStart_3574301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574327 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3574327 : Nat := 118140960795 + 3574327 * 2 ^ 59
def prefixEnd_3574327 : Nat := 4983230072969 + 3 ^ 40 * 3574327 * 2
def baseEnd_3574327 : Nat := 1835347767343142162874475

theorem tailTrace_3574327 : CollatzResearch.WordTrace tailWord_3574327 prefixEnd_3574327 1835347767343142162874475 := by
  unfold tailWord_3574327
  simp only [CollatzResearch.WordTrace]
  refine ⟨130366415721831200296585235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86910943814554133531056823 130366415721831200296585235)
  ·
    refine ⟨195549623582746800444877853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130366415721831200296585235 195549623582746800444877853)
    ·
      refine ⟨73331108843530050166829195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195549623582746800444877853 73331108843530050166829195)
      ·
        refine ⟨109996663265295075250243793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73331108843530050166829195 109996663265295075250243793)
        ·
          refine ⟨82497497448971306437682845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109996663265295075250243793 82497497448971306437682845)
          ·
            refine ⟨30936561543364239914131067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82497497448971306437682845 30936561543364239914131067)
            ·
              refine ⟨46404842315046359871196601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30936561543364239914131067 46404842315046359871196601)
              ·
                refine ⟨34803631736284769903397451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46404842315046359871196601 34803631736284769903397451)
                ·
                  refine ⟨52205447604427154855096177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34803631736284769903397451 52205447604427154855096177)
                  ·
                    refine ⟨39154085703320366141322133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52205447604427154855096177 39154085703320366141322133)
                    ·
                      refine ⟨1835347767343142162874475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39154085703320366141322133 1835347767343142162874475)
                      ·
                        rfl

theorem cell23_3574327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3574327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574327 prefixEnd_3574327 := by exact prefixLift 3574327
  have htrace : WordTrace (prefixWord ++ tailWord_3574327) baseStart_3574327 baseEnd_3574327 := by
    simpa [prefixWord, tailWord_3574327, baseEnd_3574327] using wordTrace_append hprefix tailTrace_3574327
  have hstable : (prefixWord ++ tailWord_3574327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574327).length < 2 ^ (prefixWord ++ tailWord_3574327).sum := by decide
  have hdescent : baseEnd_3574327 < baseStart_3574327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574368 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 1, 1, 3]
def baseStart_3574368 : Nat := 118140960795 + 3574368 * 2 ^ 59
def prefixEnd_3574368 : Nat := 4983230072969 + 3 ^ 40 * 3574368 * 2
def baseEnd_3574368 : Nat := 1835368820049976502461787

theorem tailTrace_3574368 : CollatzResearch.WordTrace tailWord_3574368 prefixEnd_3574368 1835368820049976502461787 := by
  unfold tailWord_3574368
  simp only [CollatzResearch.WordTrace]
  refine ⟨65183955557341332149413879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86911940743121776199218505 65183955557341332149413879)
  ·
    refine ⟨97775933336011998224120819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65183955557341332149413879 97775933336011998224120819)
    ·
      refine ⟨146663900004017997336181229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97775933336011998224120819 146663900004017997336181229)
      ·
        refine ⟨54998962501506749001067961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146663900004017997336181229 54998962501506749001067961)
        ·
          refine ⟨41249221876130061750800971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54998962501506749001067961 41249221876130061750800971)
          ·
            refine ⟨61873832814195092626201457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41249221876130061750800971 61873832814195092626201457)
            ·
              refine ⟨46405374610646319469651093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61873832814195092626201457 46405374610646319469651093)
              ·
                refine ⟨2175251934874046225139895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46405374610646319469651093 2175251934874046225139895)
                ·
                  refine ⟨3262877902311069337709843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175251934874046225139895 3262877902311069337709843)
                  ·
                    refine ⟨4894316853466604006564765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3262877902311069337709843 4894316853466604006564765)
                    ·
                      refine ⟨1835368820049976502461787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894316853466604006564765 1835368820049976502461787)
                      ·
                        rfl

theorem cell23_3574368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_3574368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574368 prefixEnd_3574368 := by exact prefixLift 3574368
  have htrace : WordTrace (prefixWord ++ tailWord_3574368) baseStart_3574368 baseEnd_3574368 := by
    simpa [prefixWord, tailWord_3574368, baseEnd_3574368] using wordTrace_append hprefix tailTrace_3574368
  have hstable : (prefixWord ++ tailWord_3574368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574368).length < 2 ^ (prefixWord ++ tailWord_3574368).sum := by decide
  have hdescent : baseEnd_3574368 < baseStart_3574368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574391 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_3574391 : Nat := 118140960795 + 3574391 * 2 ^ 59
def prefixEnd_3574391 : Nat := 4983230072969 + 3 ^ 40 * 3574391 * 2
def baseEnd_3574391 : Nat := 1835380630105029912474181

theorem tailTrace_3574391 : CollatzResearch.WordTrace tailWord_3574391 prefixEnd_3574391 1835380630105029912474181 := by
  unfold tailWord_3574391
  simp only [CollatzResearch.WordTrace]
  refine ⟨130368749993599339226915027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86912499995732892817943351 130368749993599339226915027)
  ·
    refine ⟨195553124990399008840372541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130368749993599339226915027 195553124990399008840372541)
    ·
      refine ⟨73332421871399628315139703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195553124990399008840372541 73332421871399628315139703)
      ·
        refine ⟨109998632807099442472709555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73332421871399628315139703 109998632807099442472709555)
        ·
          refine ⟨164997949210649163709064333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109998632807099442472709555 164997949210649163709064333)
          ·
            refine ⟨61874230953993436390899125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164997949210649163709064333 61874230953993436390899125)
            ·
              refine ⟨5800709151936884661646793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61874230953993436390899125 5800709151936884661646793)
              ·
                refine ⟨4350531863952663496235095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5800709151936884661646793 4350531863952663496235095)
                ·
                  refine ⟨6525797795928995244352643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350531863952663496235095 6525797795928995244352643)
                  ·
                    refine ⟨9788696693893492866528965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525797795928995244352643 9788696693893492866528965)
                    ·
                      refine ⟨1835380630105029912474181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9788696693893492866528965 1835380630105029912474181)
                      ·
                        rfl

theorem cell23_3574391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_3574391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574391 prefixEnd_3574391 := by exact prefixLift 3574391
  have htrace : WordTrace (prefixWord ++ tailWord_3574391) baseStart_3574391 baseEnd_3574391 := by
    simpa [prefixWord, tailWord_3574391, baseEnd_3574391] using wordTrace_append hprefix tailTrace_3574391
  have hstable : (prefixWord ++ tailWord_3574391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574391).length < 2 ^ (prefixWord ++ tailWord_3574391).sum := by decide
  have hdescent : baseEnd_3574391 < baseStart_3574391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574418 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3574418 : Nat := 118140960795 + 3574418 * 2 ^ 59
def prefixEnd_3574418 : Nat := 4983230072969 + 3 ^ 40 * 3574418 * 2
def baseEnd_3574418 : Nat := 611798164694233768945519

theorem tailTrace_3574418 : CollatzResearch.WordTrace tailWord_3574418 prefixEnd_3574418 611798164694233768945519 := by
  unfold tailWord_3574418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592433691125380709536977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86913156509667681892098605 32592433691125380709536977)
  ·
    refine ⟨24444325268344035532152733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32592433691125380709536977 24444325268344035532152733)
    ·
      refine ⟨9166621975629013324557275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24444325268344035532152733 9166621975629013324557275)
      ·
        refine ⟨13749932963443519986835913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9166621975629013324557275 13749932963443519986835913)
        ·
          refine ⟨10312449722582639990126935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13749932963443519986835913 10312449722582639990126935)
          ·
            refine ⟨15468674583873959985190403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10312449722582639990126935 15468674583873959985190403)
            ·
              refine ⟨23203011875810939977785605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468674583873959985190403 23203011875810939977785605)
              ·
                refine ⟨4350564726714551245834801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23203011875810939977785605 4350564726714551245834801)
                ·
                  refine ⟨3262923545035913434376101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350564726714551245834801 3262923545035913434376101)
                  ·
                    refine ⟨611798164694233768945519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3262923545035913434376101 611798164694233768945519)
                    ·
                      rfl

theorem cell23_3574418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3574418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574418 prefixEnd_3574418 := by exact prefixLift 3574418
  have htrace : WordTrace (prefixWord ++ tailWord_3574418) baseStart_3574418 baseEnd_3574418 := by
    simpa [prefixWord, tailWord_3574418, baseEnd_3574418] using wordTrace_append hprefix tailTrace_3574418
  have hstable : (prefixWord ++ tailWord_3574418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574418).length < 2 ^ (prefixWord ++ tailWord_3574418).sum := by decide
  have hdescent : baseEnd_3574418 < baseStart_3574418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574425 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 1, 2, 2]
def baseStart_3574425 : Nat := 118140960795 + 3574425 * 2 ^ 59
def prefixEnd_3574425 : Nat := 4983230072969 + 3 ^ 40 * 3574425 * 2
def baseEnd_3574425 : Nat := 1835398088447282779449025

theorem tailTrace_3574425 : CollatzResearch.WordTrace tailWord_3574425 prefixEnd_3574425 1835398088447282779449025 := by
  unfold tailWord_3574425
  simp only [CollatzResearch.WordTrace]
  refine ⟨130369990075476163033652729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86913326716984108689101819 130369990075476163033652729)
  ·
    refine ⟨97777492556607122275239547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130369990075476163033652729 97777492556607122275239547)
    ·
      refine ⟨146666238834910683412859321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97777492556607122275239547 146666238834910683412859321)
      ·
        refine ⟨109999679126183012559644491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146666238834910683412859321 109999679126183012559644491)
        ·
          refine ⟨164999518689274518839466737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109999679126183012559644491 164999518689274518839466737)
          ·
            refine ⟨123749639016955889129600053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164999518689274518839466737 123749639016955889129600053)
            ·
              refine ⟨11601528657839614605900005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123749639016955889129600053 11601528657839614605900005)
              ·
                refine ⟨2175286623344927738606251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11601528657839614605900005 2175286623344927738606251)
                ·
                  refine ⟨3262929935017391607909377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175286623344927738606251 3262929935017391607909377)
                  ·
                    refine ⟨2447197451263043705932033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3262929935017391607909377 2447197451263043705932033)
                    ·
                      refine ⟨1835398088447282779449025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447197451263043705932033 1835398088447282779449025)
                      ·
                        rfl

theorem cell23_3574425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_3574425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574425 prefixEnd_3574425 := by exact prefixLift 3574425
  have htrace : WordTrace (prefixWord ++ tailWord_3574425) baseStart_3574425 baseEnd_3574425 := by
    simpa [prefixWord, tailWord_3574425, baseEnd_3574425] using wordTrace_append hprefix tailTrace_3574425
  have hstable : (prefixWord ++ tailWord_3574425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574425).length < 2 ^ (prefixWord ++ tailWord_3574425).sum := by decide
  have hdescent : baseEnd_3574425 < baseStart_3574425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574568 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3574568 : Nat := 118140960795 + 3574568 * 2 ^ 59
def prefixEnd_3574568 : Nat := 4983230072969 + 3 ^ 40 * 3574568 * 2
def baseEnd_3574568 : Nat := 611823838726958573320289

theorem tailTrace_3574568 : CollatzResearch.WordTrace tailWord_3574568 prefixEnd_3574568 611823838726958573320289 := by
  unfold tailWord_3574568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65187602856979049228054179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86916803809305398970738905 65187602856979049228054179)
  ·
    refine ⟨97781404285468573842081269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65187602856979049228054179 97781404285468573842081269)
    ·
      refine ⟨9167006651762678797695119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97781404285468573842081269 9167006651762678797695119)
      ·
        refine ⟨13750509977644018196542679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9167006651762678797695119 13750509977644018196542679)
        ·
          refine ⟨20625764966466027294814019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750509977644018196542679 20625764966466027294814019)
          ·
            refine ⟨30938647449699040942221029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20625764966466027294814019 30938647449699040942221029)
            ·
              refine ⟨5800996396818570176666443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30938647449699040942221029 5800996396818570176666443)
              ·
                refine ⟨8701494595227855264999665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800996396818570176666443 8701494595227855264999665)
                ·
                  refine ⟨6526120946420891448749749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701494595227855264999665 6526120946420891448749749)
                  ·
                    refine ⟨611823838726958573320289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526120946420891448749749 611823838726958573320289)
                    ·
                      rfl

theorem cell23_3574568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3574568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574568 prefixEnd_3574568 := by exact prefixLift 3574568
  have htrace : WordTrace (prefixWord ++ tailWord_3574568) baseStart_3574568 baseEnd_3574568 := by
    simpa [prefixWord, tailWord_3574568, baseEnd_3574568] using wordTrace_append hprefix tailTrace_3574568
  have hstable : (prefixWord ++ tailWord_3574568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574568).length < 2 ^ (prefixWord ++ tailWord_3574568).sum := by decide
  have hdescent : baseEnd_3574568 < baseStart_3574568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574571 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4]
def baseStart_3574571 : Nat := 118140960795 + 3574571 * 2 ^ 59
def prefixEnd_3574571 : Nat := 4983230072969 + 3 ^ 40 * 3574571 * 2
def baseEnd_3574571 : Nat := 1835473056622839208223353

theorem tailTrace_3574571 : CollatzResearch.WordTrace tailWord_3574571 prefixEnd_3574571 1835473056622839208223353 := by
  unfold tailWord_3574571
  simp only [CollatzResearch.WordTrace]
  refine ⟨130375315132947229968467567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86916876755298153312311711 130375315132947229968467567)
  ·
    refine ⟨195562972699420844952701351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130375315132947229968467567 195562972699420844952701351)
    ·
      refine ⟨293344459049131267429052027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195562972699420844952701351 293344459049131267429052027)
      ·
        refine ⟨440016688573696901143578041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293344459049131267429052027 440016688573696901143578041)
        ·
          refine ⟨330012516430272675857683531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440016688573696901143578041 330012516430272675857683531)
          ·
            refine ⟨495018774645409013786525297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330012516430272675857683531 495018774645409013786525297)
            ·
              refine ⟨371264080984056760339893973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495018774645409013786525297 371264080984056760339893973)
              ·
                refine ⟨8701501898063830320466265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 371264080984056760339893973 8701501898063830320466265)
                ·
                  refine ⟨6526126423547872740349699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701501898063830320466265 6526126423547872740349699)
                  ·
                    refine ⟨9789189635321809110524549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526126423547872740349699 9789189635321809110524549)
                    ·
                      refine ⟨1835473056622839208223353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9789189635321809110524549 1835473056622839208223353)
                      ·
                        rfl

theorem cell23_3574571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_3574571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574571 prefixEnd_3574571 := by exact prefixLift 3574571
  have htrace : WordTrace (prefixWord ++ tailWord_3574571) baseStart_3574571 baseEnd_3574571 := by
    simpa [prefixWord, tailWord_3574571, baseEnd_3574571] using wordTrace_append hprefix tailTrace_3574571
  have hstable : (prefixWord ++ tailWord_3574571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574571).length < 2 ^ (prefixWord ++ tailWord_3574571).sum := by decide
  have hdescent : baseEnd_3574571 < baseStart_3574571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574588 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_3574588 : Nat := 118140960795 + 3574588 * 2 ^ 59
def prefixEnd_3574588 : Nat := 4983230072969 + 3 ^ 40 * 3574588 * 2
def baseEnd_3574588 : Nat := 1835481785793965641710775

theorem tailTrace_3574588 : CollatzResearch.WordTrace tailWord_3574588 prefixEnd_3574588 1835481785793965641710775 := by
  unfold tailWord_3574588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65187967586942820935918209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86917290115923761247890945 65187967586942820935918209)
  ·
    refine ⟨48890975690207115701938657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65187967586942820935918209 48890975690207115701938657)
    ·
      refine ⟨36668231767655336776453993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48890975690207115701938657 36668231767655336776453993)
      ·
        refine ⟨27501173825741502582340495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36668231767655336776453993 27501173825741502582340495)
        ·
          refine ⟨41251760738612253873510743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27501173825741502582340495 41251760738612253873510743)
          ·
            refine ⟨61877641107918380810266115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41251760738612253873510743 61877641107918380810266115)
            ·
              refine ⟨92816461661877571215399173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61877641107918380810266115 92816461661877571215399173)
              ·
                refine ⟨17403086561602044602887345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92816461661877571215399173 17403086561602044602887345)
                ·
                  refine ⟨13052314921201533452165509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17403086561602044602887345 13052314921201533452165509)
                  ·
                    refine ⟨2447309047725287522281033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13052314921201533452165509 2447309047725287522281033)
                    ·
                      refine ⟨1835481785793965641710775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447309047725287522281033 1835481785793965641710775)
                      ·
                        rfl

theorem cell23_3574588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_3574588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574588 prefixEnd_3574588 := by exact prefixLift 3574588
  have htrace : WordTrace (prefixWord ++ tailWord_3574588) baseStart_3574588 baseEnd_3574588 := by
    simpa [prefixWord, tailWord_3574588, baseEnd_3574588] using wordTrace_append hprefix tailTrace_3574588
  have hstable : (prefixWord ++ tailWord_3574588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574588).length < 2 ^ (prefixWord ++ tailWord_3574588).sum := by decide
  have hdescent : baseEnd_3574588 < baseStart_3574588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574589 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 5]
def baseStart_3574589 : Nat := 118140960795 + 3574589 * 2 ^ 59
def prefixEnd_3574589 : Nat := 4983230072969 + 3 ^ 40 * 3574589 * 2
def baseEnd_3574589 : Nat := 203942477697180015310919

theorem tailTrace_3574589 : CollatzResearch.WordTrace tailWord_3574589 prefixEnd_3574589 203942477697180015310919 := by
  unfold tailWord_3574589
  simp only [CollatzResearch.WordTrace]
  refine ⟨130375971646882019042622821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86917314431254679361748547 130375971646882019042622821)
  ·
    refine ⟨24445494683790378570491779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130375971646882019042622821 24445494683790378570491779)
    ·
      refine ⟨36668242025685567855737669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24445494683790378570491779 36668242025685567855737669)
      ·
        refine ⟨6875295379816043972950813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36668242025685567855737669 6875295379816043972950813)
        ·
          refine ⟨2578235767431016489856555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6875295379816043972950813 2578235767431016489856555)
          ·
            refine ⟨3867353651146524734784833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578235767431016489856555 3867353651146524734784833)
            ·
              refine ⟨2900515238359893551088625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867353651146524734784833 2900515238359893551088625)
              ·
                refine ⟨2175386428769920163316469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900515238359893551088625 2175386428769920163316469)
                ·
                  refine ⟨203942477697180015310919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175386428769920163316469 203942477697180015310919)
                  ·
                    rfl

theorem cell23_3574589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_3574589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574589 prefixEnd_3574589 := by exact prefixLift 3574589
  have htrace : WordTrace (prefixWord ++ tailWord_3574589) baseStart_3574589 baseEnd_3574589 := by
    simpa [prefixWord, tailWord_3574589, baseEnd_3574589] using wordTrace_append hprefix tailTrace_3574589
  have hstable : (prefixWord ++ tailWord_3574589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574589).length < 2 ^ (prefixWord ++ tailWord_3574589).sum := by decide
  have hdescent : baseEnd_3574589 < baseStart_3574589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574632 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 1, 4]
def baseStart_3574632 : Nat := 118140960795 + 3574632 * 2 ^ 59
def prefixEnd_3574632 : Nat := 4983230072969 + 3 ^ 40 * 3574632 * 2
def baseEnd_3574632 : Nat := 611834792980921156520191

theorem tailTrace_3574632 : CollatzResearch.WordTrace tailWord_3574632 prefixEnd_3574632 611834792980921156520191 := by
  unfold tailWord_3574632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65188769992863118693219075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86918359990484158257625433 65188769992863118693219075)
  ·
    refine ⟨97783154989294678039828613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65188769992863118693219075 97783154989294678039828613)
    ·
      refine ⟨18334341560492752132467865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97783154989294678039828613 18334341560492752132467865)
      ·
        refine ⟨13750756170369564099350899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18334341560492752132467865 13750756170369564099350899)
        ·
          refine ⟨20626134255554346149026349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750756170369564099350899 20626134255554346149026349)
          ·
            refine ⟨7734800345832879805884881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20626134255554346149026349 7734800345832879805884881)
            ·
              refine ⟨5801100259374659854413661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734800345832879805884881 5801100259374659854413661)
              ·
                refine ⟨2175412597265497445405123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5801100259374659854413661 2175412597265497445405123)
                ·
                  refine ⟨3263118895898246168107685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175412597265497445405123 3263118895898246168107685)
                  ·
                    refine ⟨611834792980921156520191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263118895898246168107685 611834792980921156520191)
                    ·
                      rfl

theorem cell23_3574632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_3574632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574632 prefixEnd_3574632 := by exact prefixLift 3574632
  have htrace : WordTrace (prefixWord ++ tailWord_3574632) baseStart_3574632 baseEnd_3574632 := by
    simpa [prefixWord, tailWord_3574632, baseEnd_3574632] using wordTrace_append hprefix tailTrace_3574632
  have hstable : (prefixWord ++ tailWord_3574632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574632).length < 2 ^ (prefixWord ++ tailWord_3574632).sum := by decide
  have hdescent : baseEnd_3574632 < baseStart_3574632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574645 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 6]
def baseStart_3574645 : Nat := 118140960795 + 3574645 * 2 ^ 59
def prefixEnd_3574645 : Nat := 4983230072969 + 3 ^ 40 * 3574645 * 2
def baseEnd_3574645 : Nat := 203945672687919102077557

theorem tailTrace_3574645 : CollatzResearch.WordTrace tailWord_3574645 prefixEnd_3574645 203945672687919102077557 := by
  unfold tailWord_3574645
  simp only [CollatzResearch.WordTrace]
  refine ⟨130378014134679140606661389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86918676089786093737774259 130378014134679140606661389)
  ·
    refine ⟨48891755300504677727498021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130378014134679140606661389 48891755300504677727498021)
    ·
      refine ⟨9167204118844627073905879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48891755300504677727498021 9167204118844627073905879)
      ·
        refine ⟨13750806178266940610858819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9167204118844627073905879 13750806178266940610858819)
        ·
          refine ⟨20626209267400410916288229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750806178266940610858819 20626209267400410916288229)
          ·
            refine ⟨3867414237637577046804043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20626209267400410916288229 3867414237637577046804043)
            ·
              refine ⟨5801121356456365570206065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867414237637577046804043 5801121356456365570206065)
              ·
                refine ⟨4350841017342274177654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801121356456365570206065 4350841017342274177654549)
                ·
                  refine ⟨203945672687919102077557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4350841017342274177654549 203945672687919102077557)
                  ·
                    rfl

theorem cell23_3574645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_3574645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574645 prefixEnd_3574645 := by exact prefixLift 3574645
  have htrace : WordTrace (prefixWord ++ tailWord_3574645) baseStart_3574645 baseEnd_3574645 := by
    simpa [prefixWord, tailWord_3574645, baseEnd_3574645] using wordTrace_append hprefix tailTrace_3574645
  have hstable : (prefixWord ++ tailWord_3574645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574645).length < 2 ^ (prefixWord ++ tailWord_3574645).sum := by decide
  have hdescent : baseEnd_3574645 < baseStart_3574645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574681 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3574681 : Nat := 118140960795 + 3574681 * 2 ^ 59
def prefixEnd_3574681 : Nat := 4983230072969 + 3 ^ 40 * 3574681 * 2
def baseEnd_3574681 : Nat := 1835529539494833777847847

theorem tailTrace_3574681 : CollatzResearch.WordTrace tailWord_3574681 prefixEnd_3574681 1835529539494833777847847 := by
  unfold tailWord_3574681
  simp only [CollatzResearch.WordTrace]
  refine ⟨130379327162548718754971897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86919551441699145836647931 130379327162548718754971897)
  ·
    refine ⟨97784495371911539066228923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130379327162548718754971897 97784495371911539066228923)
    ·
      refine ⟨146676743057867308599343385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97784495371911539066228923 146676743057867308599343385)
      ·
        refine ⟨110007557293400481449507539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146676743057867308599343385 110007557293400481449507539)
        ·
          refine ⟨165011335940100722174261309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110007557293400481449507539 165011335940100722174261309)
          ·
            refine ⟨61879250977537770815347991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165011335940100722174261309 61879250977537770815347991)
            ·
              refine ⟨92818876466306656223021987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61879250977537770815347991 92818876466306656223021987)
              ·
                refine ⟨139228314699459984334532981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92818876466306656223021987 139228314699459984334532981)
                ·
                  refine ⟨13052654503074373531362467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139228314699459984334532981 13052654503074373531362467)
                  ·
                    refine ⟨19578981754611560297043701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052654503074373531362467 19578981754611560297043701)
                    ·
                      refine ⟨1835529539494833777847847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19578981754611560297043701 1835529539494833777847847)
                      ·
                        rfl

theorem cell23_3574681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3574681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574681 prefixEnd_3574681 := by exact prefixLift 3574681
  have htrace : WordTrace (prefixWord ++ tailWord_3574681) baseStart_3574681 baseEnd_3574681 := by
    simpa [prefixWord, tailWord_3574681, baseEnd_3574681] using wordTrace_append hprefix tailTrace_3574681
  have hstable : (prefixWord ++ tailWord_3574681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574681).length < 2 ^ (prefixWord ++ tailWord_3574681).sum := by decide
  have hdescent : baseEnd_3574681 < baseStart_3574681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574688 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_3574688 : Nat := 118140960795 + 3574688 * 2 ^ 59
def prefixEnd_3574688 : Nat := 4983230072969 + 3 ^ 40 * 3574688 * 2
def baseEnd_3574688 : Nat := 611844377953138416820105

theorem tailTrace_3574688 : CollatzResearch.WordTrace tailWord_3574688 prefixEnd_3574688 611844377953138416820105 := by
  unfold tailWord_3574688
  simp only [CollatzResearch.WordTrace]
  refine ⟨65189791236761679475238359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86919721649015572633651145 65189791236761679475238359)
  ·
    refine ⟨97784686855142519212857539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65189791236761679475238359 97784686855142519212857539)
    ·
      refine ⟨146677030282713778819286309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97784686855142519212857539 146677030282713778819286309)
      ·
        refine ⟨27501943178008833528616183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146677030282713778819286309 27501943178008833528616183)
        ·
          refine ⟨41252914767013250292924275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27501943178008833528616183 41252914767013250292924275)
          ·
            refine ⟨61879372150519875439386413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41252914767013250292924275 61879372150519875439386413)
            ·
              refine ⟨23204764556444953289769905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61879372150519875439386413 23204764556444953289769905)
              ·
                refine ⟨17403573417333714967327429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23204764556444953289769905 17403573417333714967327429)
                ·
                  refine ⟨3263170015750071556373893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17403573417333714967327429 3263170015750071556373893)
                  ·
                    refine ⟨611844377953138416820105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263170015750071556373893 611844377953138416820105)
                    ·
                      rfl

theorem cell23_3574688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_3574688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574688 prefixEnd_3574688 := by exact prefixLift 3574688
  have htrace : WordTrace (prefixWord ++ tailWord_3574688) baseStart_3574688 baseEnd_3574688 := by
    simpa [prefixWord, tailWord_3574688, baseEnd_3574688] using wordTrace_append hprefix tailTrace_3574688
  have hstable : (prefixWord ++ tailWord_3574688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574688).length < 2 ^ (prefixWord ++ tailWord_3574688).sum := by decide
  have hdescent : baseEnd_3574688 < baseStart_3574688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574689 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3574689 : Nat := 118140960795 + 3574689 * 2 ^ 59
def prefixEnd_3574689 : Nat := 4983230072969 + 3 ^ 40 * 3574689 * 2
def baseEnd_3574689 : Nat := 1835533647340069746547811

theorem tailTrace_3574689 : CollatzResearch.WordTrace tailWord_3574689 prefixEnd_3574689 1835533647340069746547811 := by
  unfold tailWord_3574689
  simp only [CollatzResearch.WordTrace]
  refine ⟨130379618946519736121263121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86919745964346490747508747 130379618946519736121263121)
  ·
    refine ⟨97784714209889802090947341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130379618946519736121263121 97784714209889802090947341)
    ·
      refine ⟨36669267828708675784105253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97784714209889802090947341 36669267828708675784105253)
      ·
        refine ⟨6875487717882876709519735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36669267828708675784105253 6875487717882876709519735)
        ·
          refine ⟨10313231576824315064279603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875487717882876709519735 10313231576824315064279603)
          ·
            refine ⟨15469847365236472596419405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313231576824315064279603 15469847365236472596419405)
            ·
              refine ⟨5801192761963677223657277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15469847365236472596419405 5801192761963677223657277)
              ·
                refine ⟨2175447285736378958871479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5801192761963677223657277 2175447285736378958871479)
                ·
                  refine ⟨3263170928604568438307219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175447285736378958871479 3263170928604568438307219)
                  ·
                    refine ⟨4894756392906852657460829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263170928604568438307219 4894756392906852657460829)
                    ·
                      refine ⟨1835533647340069746547811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894756392906852657460829 1835533647340069746547811)
                      ·
                        rfl

theorem cell23_3574689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3574689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574689 prefixEnd_3574689 := by exact prefixLift 3574689
  have htrace : WordTrace (prefixWord ++ tailWord_3574689) baseStart_3574689 baseEnd_3574689 := by
    simpa [prefixWord, tailWord_3574689, baseEnd_3574689] using wordTrace_append hprefix tailTrace_3574689
  have hstable : (prefixWord ++ tailWord_3574689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574689).length < 2 ^ (prefixWord ++ tailWord_3574689).sum := by decide
  have hdescent : baseEnd_3574689 < baseStart_3574689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574712 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_3574712 : Nat := 118140960795 + 3574712 * 2 ^ 59
def prefixEnd_3574712 : Nat := 4983230072969 + 3 ^ 40 * 3574712 * 2
def baseEnd_3574712 : Nat := 1835545457395123156560205

theorem tailTrace_3574712 : CollatzResearch.WordTrace tailWord_3574712 prefixEnd_3574712 1835545457395123156560205 := by
  unfold tailWord_3574712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190228912718205524675195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86920305216957607366233593 65190228912718205524675195)
  ·
    refine ⟨97785343369077308287012793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65190228912718205524675195 97785343369077308287012793)
    ·
      refine ⟨73339007526807981215259595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97785343369077308287012793 73339007526807981215259595)
      ·
        refine ⟨110008511290211971822889393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73339007526807981215259595 110008511290211971822889393)
        ·
          refine ⟨82506383467658978867167045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110008511290211971822889393 82506383467658978867167045)
          ·
            refine ⟨15469946900186058537593821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82506383467658978867167045 15469946900186058537593821)
            ·
              refine ⟨5801230087569771951597683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15469946900186058537593821 5801230087569771951597683)
              ·
                refine ⟨8701845131354657927396525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801230087569771951597683 8701845131354657927396525)
                ·
                  refine ⟨3263191924257996722773697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8701845131354657927396525 3263191924257996722773697)
                  ·
                    refine ⟨2447393943193497542080273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263191924257996722773697 2447393943193497542080273)
                    ·
                      refine ⟨1835545457395123156560205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447393943193497542080273 1835545457395123156560205)
                      ·
                        rfl

theorem cell23_3574712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_3574712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574712 prefixEnd_3574712 := by exact prefixLift 3574712
  have htrace : WordTrace (prefixWord ++ tailWord_3574712) baseStart_3574712 baseEnd_3574712 := by
    simpa [prefixWord, tailWord_3574712, baseEnd_3574712] using wordTrace_append hprefix tailTrace_3574712
  have hstable : (prefixWord ++ tailWord_3574712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574712).length < 2 ^ (prefixWord ++ tailWord_3574712).sum := by decide
  have hdescent : baseEnd_3574712 < baseStart_3574712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574718 : List Nat := [4, 2, 1, 1, 1, 2, 4, 8]
def baseStart_3574718 : Nat := 118140960795 + 3574718 * 2 ^ 59
def prefixEnd_3574718 : Nat := 4983230072969 + 3 ^ 40 * 3574718 * 2
def baseEnd_3574718 : Nat := 67983279195520375299451

theorem tailTrace_3574718 : CollatzResearch.WordTrace tailWord_3574718 prefixEnd_3574718 67983279195520375299451 := by
  unfold tailWord_3574718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297584582926834259258601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86920451108943116049379205 16297584582926834259258601)
  ·
    refine ⟨12223188437195125694443951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16297584582926834259258601 12223188437195125694443951)
    ·
      refine ⟨18334782655792688541665927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223188437195125694443951 18334782655792688541665927)
      ·
        refine ⟨27502173983689032812498891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18334782655792688541665927 27502173983689032812498891)
        ·
          refine ⟨41253260975533549218748337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27502173983689032812498891 41253260975533549218748337)
          ·
            refine ⟨30939945731650161914061253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41253260975533549218748337 30939945731650161914061253)
            ·
              refine ⟨5801239824684405358886485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30939945731650161914061253 5801239824684405358886485)
              ·
                refine ⟨67983279195520375299451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5801239824684405358886485 67983279195520375299451)
                ·
                  rfl

theorem cell23_3574718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_3574718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574718 prefixEnd_3574718 := by exact prefixLift 3574718
  have htrace : WordTrace (prefixWord ++ tailWord_3574718) baseStart_3574718 baseEnd_3574718 := by
    simpa [prefixWord, tailWord_3574718, baseEnd_3574718] using wordTrace_append hprefix tailTrace_3574718
  have hstable : (prefixWord ++ tailWord_3574718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574718).length < 2 ^ (prefixWord ++ tailWord_3574718).sum := by decide
  have hdescent : baseEnd_3574718 < baseStart_3574718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574726 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3574726 : Nat := 118140960795 + 3574726 * 2 ^ 59
def prefixEnd_3574726 : Nat := 4983230072969 + 3 ^ 40 * 3574726 * 2
def baseEnd_3574726 : Nat := 611850882041428700595047

theorem tailTrace_3574726 : CollatzResearch.WordTrace tailWord_3574726 prefixEnd_3574726 611850882041428700595047 := by
  unfold tailWord_3574726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074405263980802857511251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86920645631590460960240021 4074405263980802857511251)
  ·
    refine ⟨6111607895971204286266877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074405263980802857511251 6111607895971204286266877)
    ·
      refine ⟨2291852960989201607350079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6111607895971204286266877 2291852960989201607350079)
      ·
        refine ⟨3437779441483802411025119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291852960989201607350079 3437779441483802411025119)
        ·
          refine ⟨5156669162225703616537679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437779441483802411025119 5156669162225703616537679)
          ·
            refine ⟨7735003743338555424806519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156669162225703616537679 7735003743338555424806519)
            ·
              refine ⟨11602505615007833137209779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735003743338555424806519 11602505615007833137209779)
              ·
                refine ⟨17403758422511749705814669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602505615007833137209779 17403758422511749705814669)
                ·
                  refine ⟨6526409408441906139680501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17403758422511749705814669 6526409408441906139680501)
                  ·
                    refine ⟨611850882041428700595047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526409408441906139680501 611850882041428700595047)
                    ·
                      rfl

theorem cell23_3574726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3574726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574726 prefixEnd_3574726 := by exact prefixLift 3574726
  have htrace : WordTrace (prefixWord ++ tailWord_3574726) baseStart_3574726 baseEnd_3574726 := by
    simpa [prefixWord, tailWord_3574726, baseEnd_3574726] using wordTrace_append hprefix tailTrace_3574726
  have hstable : (prefixWord ++ tailWord_3574726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574726).length < 2 ^ (prefixWord ++ tailWord_3574726).sum := by decide
  have hdescent : baseEnd_3574726 < baseStart_3574726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574733 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3574733 : Nat := 118140960795 + 3574733 * 2 ^ 59
def prefixEnd_3574733 : Nat := 4983230072969 + 3 ^ 40 * 3574733 * 2
def baseEnd_3574733 : Nat := 1835556240488867574397609

theorem tailTrace_3574733 : CollatzResearch.WordTrace tailWord_3574733 prefixEnd_3574733 1835556240488867574397609 := by
  unfold tailWord_3574733
  simp only [CollatzResearch.WordTrace]
  refine ⟨130381223758360331635864853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86920815838906887757243235 130381223758360331635864853)
  ·
    refine ⟨6111619863673140545431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130381223758360331635864853 6111619863673140545431165)
    ·
      refine ⟨2291857448877427704536687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6111619863673140545431165 2291857448877427704536687)
      ·
        refine ⟨3437786173316141556805031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291857448877427704536687 3437786173316141556805031)
        ·
          refine ⟨5156679259974212335207547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437786173316141556805031 5156679259974212335207547)
          ·
            refine ⟨7735018889961318502811321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156679259974212335207547 7735018889961318502811321)
            ·
              refine ⟨5801264167470988877108491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735018889961318502811321 5801264167470988877108491)
              ·
                refine ⟨8701896251206483315662737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801264167470988877108491 8701896251206483315662737)
                ·
                  refine ⟨6526422188404862486747053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701896251206483315662737 6526422188404862486747053)
                  ·
                    refine ⟨2447408320651823432530145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6526422188404862486747053 2447408320651823432530145)
                    ·
                      refine ⟨1835556240488867574397609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447408320651823432530145 1835556240488867574397609)
                      ·
                        rfl

theorem cell23_3574733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3574733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574733 prefixEnd_3574733 := by exact prefixLift 3574733
  have htrace : WordTrace (prefixWord ++ tailWord_3574733) baseStart_3574733 baseEnd_3574733 := by
    simpa [prefixWord, tailWord_3574733, baseEnd_3574733] using wordTrace_append hprefix tailTrace_3574733
  have hstable : (prefixWord ++ tailWord_3574733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574733).length < 2 ^ (prefixWord ++ tailWord_3574733).sum := by decide
  have hdescent : baseEnd_3574733 < baseStart_3574733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574742 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3574742 : Nat := 118140960795 + 3574742 * 2 ^ 59
def prefixEnd_3574742 : Nat := 4983230072969 + 3 ^ 40 * 3574742 * 2
def baseEnd_3574742 : Nat := 1835560861814758039185067

theorem tailTrace_3574742 : CollatzResearch.WordTrace tailWord_3574742 prefixEnd_3574742 1835560861814758039185067 := by
  unfold tailWord_3574742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148847000957982885808905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86921034676885150781961653 8148847000957982885808905)
  ·
    refine ⟨6111635250718487164356679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8148847000957982885808905 6111635250718487164356679)
    ·
      refine ⟨9167452876077730746535019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6111635250718487164356679 9167452876077730746535019)
      ·
        refine ⟨13751179314116596119802529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9167452876077730746535019 13751179314116596119802529)
        ·
          refine ⟨10313384485587447089851897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13751179314116596119802529 10313384485587447089851897)
          ·
            refine ⟨7735038364190585317388923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313384485587447089851897 7735038364190585317388923)
            ·
              refine ⟨11602557546285877976083385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735038364190585317388923 11602557546285877976083385)
              ·
                refine ⟨8701918159714408482062539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602557546285877976083385 8701918159714408482062539)
                ·
                  refine ⟨13052877239571612723093809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701918159714408482062539 13052877239571612723093809)
                  ·
                    refine ⟨9789657929678709542320357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13052877239571612723093809 9789657929678709542320357)
                    ·
                      refine ⟨1835560861814758039185067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9789657929678709542320357 1835560861814758039185067)
                      ·
                        rfl

theorem cell23_3574742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3574742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574742 prefixEnd_3574742 := by exact prefixLift 3574742
  have htrace : WordTrace (prefixWord ++ tailWord_3574742) baseStart_3574742 baseEnd_3574742 := by
    simpa [prefixWord, tailWord_3574742, baseEnd_3574742] using wordTrace_append hprefix tailTrace_3574742
  have hstable : (prefixWord ++ tailWord_3574742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574742).length < 2 ^ (prefixWord ++ tailWord_3574742).sum := by decide
  have hdescent : baseEnd_3574742 < baseStart_3574742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574745 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3574745 : Nat := 118140960795 + 3574745 * 2 ^ 59
def prefixEnd_3574745 : Nat := 4983230072969 + 3 ^ 40 * 3574745 * 2
def baseEnd_3574745 : Nat := 1835562402256721527447553

theorem tailTrace_3574745 : CollatzResearch.WordTrace tailWord_3574745 prefixEnd_3574745 1835562402256721527447553 := by
  unfold tailWord_3574745
  simp only [CollatzResearch.WordTrace]
  refine ⟨130381661434316857685301689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86921107622877905123534459 130381661434316857685301689)
  ·
    refine ⟨97786246075737643263976267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130381661434316857685301689 97786246075737643263976267)
    ·
      refine ⟨146679369113606464895964401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97786246075737643263976267 146679369113606464895964401)
      ·
        refine ⟨110009526835204848671973301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146679369113606464895964401 110009526835204848671973301)
        ·
          refine ⟨10313393140800454562997497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110009526835204848671973301 10313393140800454562997497)
          ·
            refine ⟨7735044855600340922248123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313393140800454562997497 7735044855600340922248123)
            ·
              refine ⟨11602567283400511383372185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735044855600340922248123 11602567283400511383372185)
              ·
                refine ⟨8701925462550383537529139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602567283400511383372185 8701925462550383537529139)
                ·
                  refine ⟨13052888193825575306293709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701925462550383537529139 13052888193825575306293709)
                  ·
                    refine ⟨4894833072684590739860141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13052888193825575306293709 4894833072684590739860141)
                    ·
                      refine ⟨1835562402256721527447553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894833072684590739860141 1835562402256721527447553)
                      ·
                        rfl

theorem cell23_3574745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3574745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574745 prefixEnd_3574745 := by exact prefixLift 3574745
  have htrace : WordTrace (prefixWord ++ tailWord_3574745) baseStart_3574745 baseEnd_3574745 := by
    simpa [prefixWord, tailWord_3574745, baseEnd_3574745] using wordTrace_append hprefix tailTrace_3574745
  have hstable : (prefixWord ++ tailWord_3574745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574745).length < 2 ^ (prefixWord ++ tailWord_3574745).sum := by decide
  have hdescent : baseEnd_3574745 < baseStart_3574745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574749 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3574749 : Nat := 118140960795 + 3574749 * 2 ^ 59
def prefixEnd_3574749 : Nat := 4983230072969 + 3 ^ 40 * 3574749 * 2
def baseEnd_3574749 : Nat := 1835564456179339511797535

theorem tailTrace_3574749 : CollatzResearch.WordTrace tailWord_3574749 prefixEnd_3574749 1835564456179339511797535 := by
  unfold tailWord_3574749
  simp only [CollatzResearch.WordTrace]
  refine ⟨130381807326302366368447301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86921204884201577578964867 130381807326302366368447301)
  ·
    refine ⟨24446588873681693694083869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130381807326302366368447301 24446588873681693694083869)
    ·
      refine ⟨9167470827630635135281451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24446588873681693694083869 9167470827630635135281451)
      ·
        refine ⟨13751206241445952702922177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9167470827630635135281451 13751206241445952702922177)
        ·
          refine ⟨10313404681084464527191633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13751206241445952702922177 10313404681084464527191633)
          ·
            refine ⟨7735053510813348395393725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313404681084464527191633 7735053510813348395393725)
            ·
              refine ⟨2900645066555005648272647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735053510813348395393725 2900645066555005648272647)
              ·
                refine ⟨4350967599832508472408971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900645066555005648272647 4350967599832508472408971)
                ·
                  refine ⟨6526451399748762708613457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350967599832508472408971 6526451399748762708613457)
                  ·
                    refine ⟨4894838549811572031460093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526451399748762708613457 4894838549811572031460093)
                    ·
                      refine ⟨1835564456179339511797535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894838549811572031460093 1835564456179339511797535)
                      ·
                        rfl

theorem cell23_3574749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3574749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574749 prefixEnd_3574749 := by exact prefixLift 3574749
  have htrace : WordTrace (prefixWord ++ tailWord_3574749) baseStart_3574749 baseEnd_3574749 := by
    simpa [prefixWord, tailWord_3574749, baseEnd_3574749] using wordTrace_append hprefix tailTrace_3574749
  have hstable : (prefixWord ++ tailWord_3574749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574749).length < 2 ^ (prefixWord ++ tailWord_3574749).sum := by decide
  have hdescent : baseEnd_3574749 < baseStart_3574749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_3574761 : Nat := 118140960795 + 3574761 * 2 ^ 59
def prefixEnd_3574761 : Nat := 4983230072969 + 3 ^ 40 * 3574761 * 2
def baseEnd_3574761 : Nat := 611856872649064488282493

theorem tailTrace_3574761 : CollatzResearch.WordTrace tailWord_3574761 prefixEnd_3574761 611856872649064488282493 := by
  unfold tailWord_3574761
  simp only [CollatzResearch.WordTrace]
  refine ⟨130382245002258892417884137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86921496668172594945256091 130382245002258892417884137)
  ·
    refine ⟨97786683751694169313413103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130382245002258892417884137 97786683751694169313413103)
    ·
      refine ⟨146680025627541253970119655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97786683751694169313413103 146680025627541253970119655)
      ·
        refine ⟨220020038441311880955179483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146680025627541253970119655 220020038441311880955179483)
        ·
          refine ⟨330030057661967821432769225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220020038441311880955179483 330030057661967821432769225)
          ·
            refine ⟨247522543246475866074576919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330030057661967821432769225 247522543246475866074576919)
            ·
              refine ⟨371283814869713799111865379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247522543246475866074576919 371283814869713799111865379)
              ·
                refine ⟨556925722304570698667798069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371283814869713799111865379 556925722304570698667798069)
                ·
                  refine ⟨52211786466053503000106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556925722304570698667798069 52211786466053503000106069)
                  ·
                    refine ⟨611856872649064488282493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52211786466053503000106069 611856872649064488282493)
                    ·
                      rfl

theorem cell23_3574761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_3574761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574761 prefixEnd_3574761 := by exact prefixLift 3574761
  have htrace : WordTrace (prefixWord ++ tailWord_3574761) baseStart_3574761 baseEnd_3574761 := by
    simpa [prefixWord, tailWord_3574761, baseEnd_3574761] using wordTrace_append hprefix tailTrace_3574761
  have hstable : (prefixWord ++ tailWord_3574761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574761).length < 2 ^ (prefixWord ++ tailWord_3574761).sum := by decide
  have hdescent : baseEnd_3574761 < baseStart_3574761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574762 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_3574762 : Nat := 118140960795 + 3574762 * 2 ^ 59
def prefixEnd_3574762 : Nat := 4983230072969 + 3 ^ 40 * 3574762 * 2
def baseEnd_3574762 : Nat := 1835571131427847960934975

theorem tailTrace_3574762 : CollatzResearch.WordTrace tailWord_3574762 prefixEnd_3574762 1835571131427847960934975 := by
  unfold tailWord_3574762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595570368813817397167635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86921520983503513059113693 32595570368813817397167635)
  ·
    refine ⟨48893355553220726095751453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595570368813817397167635 48893355553220726095751453)
    ·
      refine ⟨18335008332457772285906795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48893355553220726095751453 18335008332457772285906795)
      ·
        refine ⟨27502512498686658428860193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335008332457772285906795 27502512498686658428860193)
        ·
          refine ⟨20626884374014993821645145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27502512498686658428860193 20626884374014993821645145)
          ·
            refine ⟨15470163280511245366233859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20626884374014993821645145 15470163280511245366233859)
            ·
              refine ⟨23205244920766868049350789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470163280511245366233859 23205244920766868049350789)
              ·
                refine ⟨4350983422643787759253273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23205244920766868049350789 4350983422643787759253273)
                ·
                  refine ⟨3263237566982840819439955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350983422643787759253273 3263237566982840819439955)
                  ·
                    refine ⟨4894856350474261229159933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263237566982840819439955 4894856350474261229159933)
                    ·
                      refine ⟨1835571131427847960934975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4894856350474261229159933 1835571131427847960934975)
                      ·
                        rfl

theorem cell23_3574762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_3574762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574762 prefixEnd_3574762 := by exact prefixLift 3574762
  have htrace : WordTrace (prefixWord ++ tailWord_3574762) baseStart_3574762 baseEnd_3574762 := by
    simpa [prefixWord, tailWord_3574762, baseEnd_3574762] using wordTrace_append hprefix tailTrace_3574762
  have hstable : (prefixWord ++ tailWord_3574762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574762).length < 2 ^ (prefixWord ++ tailWord_3574762).sum := by decide
  have hdescent : baseEnd_3574762 < baseStart_3574762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574819 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 2, 2, 2]
def baseStart_3574819 : Nat := 118140960795 + 3574819 * 2 ^ 59
def prefixEnd_3574819 : Nat := 4983230072969 + 3 ^ 40 * 3574819 * 2
def baseEnd_3574819 : Nat := 1835600399825154237922213

theorem tailTrace_3574819 : CollatzResearch.WordTrace tailWord_3574819 prefixEnd_3574819 1835600399825154237922213 := by
  unfold tailWord_3574819
  simp only [CollatzResearch.WordTrace]
  refine ⟨130384360436048768323495511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86922906957365845548997007 130384360436048768323495511)
  ·
    refine ⟨195576540654073152485243267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130384360436048768323495511 195576540654073152485243267)
    ·
      refine ⟨293364810981109728727864901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195576540654073152485243267 293364810981109728727864901)
      ·
        refine ⟨55005902058958074136474669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293364810981109728727864901 55005902058958074136474669)
        ·
          refine ⟨20627213272109277801178001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55005902058958074136474669 20627213272109277801178001)
          ·
            refine ⟨15470409954081958350883501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20627213272109277801178001 15470409954081958350883501)
            ·
              refine ⟨5801403732780734381581313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15470409954081958350883501 5801403732780734381581313)
              ·
                refine ⟨4351052799585550786185985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801403732780734381581313 4351052799585550786185985)
                ·
                  refine ⟨3263289599689163089639489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351052799585550786185985 3263289599689163089639489)
                  ·
                    refine ⟨2447467199766872317229617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263289599689163089639489 2447467199766872317229617)
                    ·
                      refine ⟨1835600399825154237922213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447467199766872317229617 1835600399825154237922213)
                      ·
                        rfl

theorem cell23_3574819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_3574819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574819 prefixEnd_3574819 := by exact prefixLift 3574819
  have htrace : WordTrace (prefixWord ++ tailWord_3574819) baseStart_3574819 baseEnd_3574819 := by
    simpa [prefixWord, tailWord_3574819, baseEnd_3574819] using wordTrace_append hprefix tailTrace_3574819
  have hstable : (prefixWord ++ tailWord_3574819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574819).length < 2 ^ (prefixWord ++ tailWord_3574819).sum := by decide
  have hdescent : baseEnd_3574819 < baseStart_3574819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574836 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3574836 : Nat := 118140960795 + 3574836 * 2 ^ 59
def prefixEnd_3574836 : Nat := 4983230072969 + 3 ^ 40 * 3574836 * 2
def baseEnd_3574836 : Nat := 1835609128996280671409635

theorem tailTrace_3574836 : CollatzResearch.WordTrace tailWord_3574836 prefixEnd_3574836 1835609128996280671409635 := by
  unfold tailWord_3574836
  simp only [CollatzResearch.WordTrace]
  refine ⟨65192490238493590113432181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86923320317991453484576241 65192490238493590113432181)
  ·
    refine ⟨6111795959858774073134267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65192490238493590113432181 6111795959858774073134267)
    ·
      refine ⟨9167693939788161109701401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6111795959858774073134267 9167693939788161109701401)
      ·
        refine ⟨6875770454841120832276051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167693939788161109701401 6875770454841120832276051)
        ·
          refine ⟨10313655682261681248414077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875770454841120832276051 10313655682261681248414077)
          ·
            refine ⟨3867620880848130468155279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10313655682261681248414077 3867620880848130468155279)
            ·
              refine ⟨5801431321272195702232919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867620880848130468155279 5801431321272195702232919)
              ·
                refine ⟨8702146981908293553349379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801431321272195702232919 8702146981908293553349379)
                ·
                  refine ⟨13053220472862440330024069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702146981908293553349379 13053220472862440330024069)
                  ·
                    refine ⟨2447478838661707561879513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13053220472862440330024069 2447478838661707561879513)
                    ·
                      refine ⟨1835609128996280671409635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447478838661707561879513 1835609128996280671409635)
                      ·
                        rfl

theorem cell23_3574836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3574836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574836 prefixEnd_3574836 := by exact prefixLift 3574836
  have htrace : WordTrace (prefixWord ++ tailWord_3574836) baseStart_3574836 baseEnd_3574836 := by
    simpa [prefixWord, tailWord_3574836, baseEnd_3574836] using wordTrace_append hprefix tailTrace_3574836
  have hstable : (prefixWord ++ tailWord_3574836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574836).length < 2 ^ (prefixWord ++ tailWord_3574836).sum := by decide
  have hdescent : baseEnd_3574836 < baseStart_3574836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574882 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3574882 : Nat := 118140960795 + 3574882 * 2 ^ 59
def prefixEnd_3574882 : Nat := 4983230072969 + 3 ^ 40 * 3574882 * 2
def baseEnd_3574882 : Nat := 1835632749106387491434423

theorem tailTrace_3574882 : CollatzResearch.WordTrace tailWord_3574882 prefixEnd_3574882 1835632749106387491434423 := by
  unfold tailWord_3574882
  simp only [CollatzResearch.WordTrace]
  refine ⟨32596664558705132520759725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86924438823213686722025933 32596664558705132520759725)
  ·
    refine ⟨12223749209514424695284897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32596664558705132520759725 12223749209514424695284897)
    ·
      refine ⟨9167811907135818521463673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12223749209514424695284897 9167811907135818521463673)
      ·
        refine ⟨6875858930351863891097755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167811907135818521463673 6875858930351863891097755)
        ·
          refine ⟨10313788395527795836646633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875858930351863891097755 10313788395527795836646633)
          ·
            refine ⟨7735341296645846877484975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313788395527795836646633 7735341296645846877484975)
            ·
              refine ⟨11603011944968770316227463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735341296645846877484975 11603011944968770316227463)
              ·
                refine ⟨17404517917453155474341195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11603011944968770316227463 17404517917453155474341195)
                ·
                  refine ⟨26106776876179733211511793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17404517917453155474341195 26106776876179733211511793)
                  ·
                    refine ⟨19580082657134799908633845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26106776876179733211511793 19580082657134799908633845)
                    ·
                      refine ⟨1835632749106387491434423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19580082657134799908633845 1835632749106387491434423)
                      ·
                        rfl

theorem cell23_3574882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3574882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574882 prefixEnd_3574882 := by exact prefixLift 3574882
  have htrace : WordTrace (prefixWord ++ tailWord_3574882) baseStart_3574882 baseEnd_3574882 := by
    simpa [prefixWord, tailWord_3574882, baseEnd_3574882] using wordTrace_append hprefix tailTrace_3574882
  have hstable : (prefixWord ++ tailWord_3574882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574882).length < 2 ^ (prefixWord ++ tailWord_3574882).sum := by decide
  have hdescent : baseEnd_3574882 < baseStart_3574882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574895 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_3574895 : Nat := 118140960795 + 3574895 * 2 ^ 59
def prefixEnd_3574895 : Nat := 4983230072969 + 3 ^ 40 * 3574895 * 2
def baseEnd_3574895 : Nat := 1835639424354895940571863

theorem tailTrace_3574895 : CollatzResearch.WordTrace tailWord_3574895 prefixEnd_3574895 1835639424354895940571863 := by
  unfold tailWord_3574895
  simp only [CollatzResearch.WordTrace]
  refine ⟨130387132383773433303262139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86924754922515622202174759 130387132383773433303262139)
  ·
    refine ⟨195580698575660149954893209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130387132383773433303262139 195580698575660149954893209)
    ·
      refine ⟨146685523931745112466169907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195580698575660149954893209 146685523931745112466169907)
      ·
        refine ⟨220028285897617668699254861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146685523931745112466169907 220028285897617668699254861)
        ·
          refine ⟨82510607211606625762220573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220028285897617668699254861 82510607211606625762220573)
          ·
            refine ⟨30941477704352484660832715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82510607211606625762220573 30941477704352484660832715)
            ·
              refine ⟨46412216556528726991249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30941477704352484660832715 46412216556528726991249073)
              ·
                refine ⟨34809162417396545243436805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46412216556528726991249073 34809162417396545243436805)
                ·
                  refine ⟨6526717953261852233144401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34809162417396545243436805 6526717953261852233144401)
                  ·
                    refine ⟨4895038464946389174858301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526717953261852233144401 4895038464946389174858301)
                    ·
                      refine ⟨1835639424354895940571863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895038464946389174858301 1835639424354895940571863)
                      ·
                        rfl

theorem cell23_3574895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_3574895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574895 prefixEnd_3574895 := by exact prefixLift 3574895
  have htrace : WordTrace (prefixWord ++ tailWord_3574895) baseStart_3574895 baseEnd_3574895 := by
    simpa [prefixWord, tailWord_3574895, baseEnd_3574895] using wordTrace_append hprefix tailTrace_3574895
  have hstable : (prefixWord ++ tailWord_3574895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574895).length < 2 ^ (prefixWord ++ tailWord_3574895).sum := by decide
  have hdescent : baseEnd_3574895 < baseStart_3574895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574902 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3574902 : Nat := 118140960795 + 3574902 * 2 ^ 59
def prefixEnd_3574902 : Nat := 4983230072969 + 3 ^ 40 * 3574902 * 2
def baseEnd_3574902 : Nat := 611881006239825804394777

theorem tailTrace_3574902 : CollatzResearch.WordTrace tailWord_3574902 prefixEnd_3574902 611881006239825804394777 := by
  unfold tailWord_3574902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149211730921754593672935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86924925129832048999177973 8149211730921754593672935)
  ·
    refine ⟨12223817596382631890509403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149211730921754593672935 12223817596382631890509403)
    ·
      refine ⟨18335726394573947835764105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223817596382631890509403 18335726394573947835764105)
      ·
        refine ⟨13751794795930460876823079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18335726394573947835764105 13751794795930460876823079)
        ·
          refine ⟨20627692193895691315234619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751794795930460876823079 20627692193895691315234619)
          ·
            refine ⟨30941538290843536972851929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20627692193895691315234619 30941538290843536972851929)
            ·
              refine ⟨23206153718132652729638947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30941538290843536972851929 23206153718132652729638947)
              ·
                refine ⟨34809230577198979094458421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23206153718132652729638947 34809230577198979094458421)
                ·
                  refine ⟨3263365366612404290105477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34809230577198979094458421 3263365366612404290105477)
                  ·
                    refine ⟨611881006239825804394777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263365366612404290105477 611881006239825804394777)
                    ·
                      rfl

theorem cell23_3574902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3574902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574902 prefixEnd_3574902 := by exact prefixLift 3574902
  have htrace : WordTrace (prefixWord ++ tailWord_3574902) baseStart_3574902 baseEnd_3574902 := by
    simpa [prefixWord, tailWord_3574902, baseEnd_3574902] using wordTrace_append hprefix tailTrace_3574902
  have hstable : (prefixWord ++ tailWord_3574902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574902).length < 2 ^ (prefixWord ++ tailWord_3574902).sum := by decide
  have hdescent : baseEnd_3574902 < baseStart_3574902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574936 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 1, 4]
def baseStart_3574936 : Nat := 118140960795 + 3574936 * 2 ^ 59
def prefixEnd_3574936 : Nat := 4983230072969 + 3 ^ 40 * 3574936 * 2
def baseEnd_3574936 : Nat := 611886825687243426719725

theorem tailTrace_3574936 : CollatzResearch.WordTrace tailWord_3574936 prefixEnd_3574936 611886825687243426719725 := by
  unfold tailWord_3574936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65194313888312448652752331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86925751851083264870336441 65194313888312448652752331)
  ·
    refine ⟨97791470832468672979128497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65194313888312448652752331 97791470832468672979128497)
    ·
      refine ⟨73343603124351504734346373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97791470832468672979128497 73343603124351504734346373)
      ·
        refine ⟨13751925585815907137689945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73343603124351504734346373 13751925585815907137689945)
        ·
          refine ⟨10313944189361930353267459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13751925585815907137689945 10313944189361930353267459)
          ·
            refine ⟨15470916284042895529901189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313944189361930353267459 15470916284042895529901189)
            ·
              refine ⟨2900796803258042911856473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15470916284042895529901189 2900796803258042911856473)
              ·
                refine ⟨2175597602443532183892355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900796803258042911856473 2175597602443532183892355)
                ·
                  refine ⟨3263396403665298275838533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175597602443532183892355 3263396403665298275838533)
                  ·
                    refine ⟨611886825687243426719725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263396403665298275838533 611886825687243426719725)
                    ·
                      rfl

theorem cell23_3574936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_3574936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574936 prefixEnd_3574936 := by exact prefixLift 3574936
  have htrace : WordTrace (prefixWord ++ tailWord_3574936) baseStart_3574936 baseEnd_3574936 := by
    simpa [prefixWord, tailWord_3574936, baseEnd_3574936] using wordTrace_append hprefix tailTrace_3574936
  have hstable : (prefixWord ++ tailWord_3574936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574936).length < 2 ^ (prefixWord ++ tailWord_3574936).sum := by decide
  have hdescent : baseEnd_3574936 < baseStart_3574936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574945 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3574945 : Nat := 118140960795 + 3574945 * 2 ^ 59
def prefixEnd_3574945 : Nat := 4983230072969 + 3 ^ 40 * 3574945 * 2
def baseEnd_3574945 : Nat := 611888366129206914982211

theorem tailTrace_3574945 : CollatzResearch.WordTrace tailWord_3574945 prefixEnd_3574945 611888366129206914982211 := by
  unfold tailWord_3574945
  simp only [CollatzResearch.WordTrace]
  refine ⟨130388956033592291842582289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86925970689061527895054859 130388956033592291842582289)
  ·
    refine ⟨97791717025194218881936717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130388956033592291842582289 97791717025194218881936717)
    ·
      refine ⟨36671893884447832080726269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97791717025194218881936717 36671893884447832080726269)
      ·
        refine ⟨13751960206667937030272351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36671893884447832080726269 13751960206667937030272351)
        ·
          refine ⟨20627940310001905545408527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751960206667937030272351 20627940310001905545408527)
          ·
            refine ⟨30941910465002858318112791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20627940310001905545408527 30941910465002858318112791)
            ·
              refine ⟨46412865697504287477169187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30941910465002858318112791 46412865697504287477169187)
              ·
                refine ⟨69619298546256431215753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46412865697504287477169187 69619298546256431215753781)
                ·
                  refine ⟨6526809238711540426476917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69619298546256431215753781 6526809238711540426476917)
                  ·
                    refine ⟨611888366129206914982211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526809238711540426476917 611888366129206914982211)
                    ·
                      rfl

theorem cell23_3574945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3574945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574945 prefixEnd_3574945 := by exact prefixLift 3574945
  have htrace : WordTrace (prefixWord ++ tailWord_3574945) baseStart_3574945 baseEnd_3574945 := by
    simpa [prefixWord, tailWord_3574945, baseEnd_3574945] using wordTrace_append hprefix tailTrace_3574945
  have hstable : (prefixWord ++ tailWord_3574945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574945).length < 2 ^ (prefixWord ++ tailWord_3574945).sum := by decide
  have hdescent : baseEnd_3574945 < baseStart_3574945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574969 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3574969 : Nat := 118140960795 + 3574969 * 2 ^ 59
def prefixEnd_3574969 : Nat := 4983230072969 + 3 ^ 40 * 3574969 * 2
def baseEnd_3574969 : Nat := 1835677421923328651046523

theorem tailTrace_3574969 : CollatzResearch.WordTrace tailWord_3574969 prefixEnd_3574969 1835677421923328651046523 := by
  unfold tailWord_3574969
  simp only [CollatzResearch.WordTrace]
  refine ⟨130389831385505343941455961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86926554257003562627637307 130389831385505343941455961)
  ·
    refine ⟨97792373539129007956091971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130389831385505343941455961 97792373539129007956091971)
    ·
      refine ⟨146688560308693511934137957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97792373539129007956091971 146688560308693511934137957)
      ·
        refine ⟨27504105057880033487650867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146688560308693511934137957 27504105057880033487650867)
        ·
          refine ⟨41256157586820050231476301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27504105057880033487650867 41256157586820050231476301)
          ·
            refine ⟨15471059095057518836803613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41256157586820050231476301 15471059095057518836803613)
            ·
              refine ⟨5801647160646569563801355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15471059095057518836803613 5801647160646569563801355)
              ·
                refine ⟨8702470740969854345702033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801647160646569563801355 8702470740969854345702033)
                ·
                  refine ⟨6526853055727390759276525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702470740969854345702033 6526853055727390759276525)
                  ·
                    refine ⟨2447569895897771534728697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6526853055727390759276525 2447569895897771534728697)
                    ·
                      refine ⟨1835677421923328651046523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447569895897771534728697 1835677421923328651046523)
                      ·
                        rfl

theorem cell23_3574969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3574969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574969 prefixEnd_3574969 := by exact prefixLift 3574969
  have htrace : WordTrace (prefixWord ++ tailWord_3574969) baseStart_3574969 baseEnd_3574969 := by
    simpa [prefixWord, tailWord_3574969, baseEnd_3574969] using wordTrace_append hprefix tailTrace_3574969
  have hstable : (prefixWord ++ tailWord_3574969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574969).length < 2 ^ (prefixWord ++ tailWord_3574969).sum := by decide
  have hdescent : baseEnd_3574969 < baseStart_3574969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574975 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 6]
def baseStart_3574975 : Nat := 118140960795 + 3574975 * 2 ^ 59
def prefixEnd_3574975 : Nat := 4983230072969 + 3 ^ 40 * 3574975 * 2
def baseEnd_3574975 : Nat := 611893500935751875857165

theorem tailTrace_3574975 : CollatzResearch.WordTrace tailWord_3574975 prefixEnd_3574975 611893500935751875857165 := by
  unfold tailWord_3574975
  simp only [CollatzResearch.WordTrace]
  refine ⟨130390050223483606966174379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86926700148989071310782919 130390050223483606966174379)
  ·
    refine ⟨195585075335225410449261569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130390050223483606966174379 195585075335225410449261569)
    ·
      refine ⟨146688806501419057836946177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195585075335225410449261569 146688806501419057836946177)
      ·
        refine ⟨110016604876064293377709633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146688806501419057836946177 110016604876064293377709633)
        ·
          refine ⟨82512453657048220033282225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110016604876064293377709633 82512453657048220033282225)
          ·
            refine ⟨61884340242786165024961669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82512453657048220033282225 61884340242786165024961669)
            ·
              refine ⟨11603313795522405942180313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61884340242786165024961669 11603313795522405942180313)
              ·
                refine ⟨8702485346641804456635235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11603313795522405942180313 8702485346641804456635235)
                ·
                  refine ⟨13053728019962706684952853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702485346641804456635235 13053728019962706684952853)
                  ·
                    refine ⟨611893500935751875857165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13053728019962706684952853 611893500935751875857165)
                    ·
                      rfl

theorem cell23_3574975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_3574975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574975 prefixEnd_3574975 := by exact prefixLift 3574975
  have htrace : WordTrace (prefixWord ++ tailWord_3574975) baseStart_3574975 baseEnd_3574975 := by
    simpa [prefixWord, tailWord_3574975, baseEnd_3574975] using wordTrace_append hprefix tailTrace_3574975
  have hstable : (prefixWord ++ tailWord_3574975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574975).length < 2 ^ (prefixWord ++ tailWord_3574975).sum := by decide
  have hdescent : baseEnd_3574975 < baseStart_3574975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574999 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_3574999 : Nat := 118140960795 + 3574999 * 2 ^ 59
def prefixEnd_3574999 : Nat := 4983230072969 + 3 ^ 40 * 3574999 * 2
def baseEnd_3574999 : Nat := 1835692826342963533671385

theorem tailTrace_3574999 : CollatzResearch.WordTrace tailWord_3574999 prefixEnd_3574999 1835692826342963533671385 := by
  unfold tailWord_3574999
  simp only [CollatzResearch.WordTrace]
  refine ⟨130390925575396659065048051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86927283716931106043365367 130390925575396659065048051)
  ·
    refine ⟨195586388363094988597572077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130390925575396659065048051 195586388363094988597572077)
    ·
      refine ⟨73344895636160620724089529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195586388363094988597572077 73344895636160620724089529)
      ·
        refine ⟨55008671727120465543067147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73344895636160620724089529 55008671727120465543067147)
        ·
          refine ⟨82513007590680698314600721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55008671727120465543067147 82513007590680698314600721)
          ·
            refine ⟨61884755693010523735950541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82513007590680698314600721 61884755693010523735950541)
            ·
              refine ⟨23206783384878946400981453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61884755693010523735950541 23206783384878946400981453)
              ·
                refine ⟨8702543769329604900368045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23206783384878946400981453 8702543769329604900368045)
                ·
                  refine ⟨3263453913498601837638017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8702543769329604900368045 3263453913498601837638017)
                  ·
                    refine ⟨2447590435123951378228513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263453913498601837638017 2447590435123951378228513)
                    ·
                      refine ⟨1835692826342963533671385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447590435123951378228513 1835692826342963533671385)
                      ·
                        rfl

theorem cell23_3574999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_3574999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3574999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3574999 prefixEnd_3574999 := by exact prefixLift 3574999
  have htrace : WordTrace (prefixWord ++ tailWord_3574999) baseStart_3574999 baseEnd_3574999 := by
    simpa [prefixWord, tailWord_3574999, baseEnd_3574999] using wordTrace_append hprefix tailTrace_3574999
  have hstable : (prefixWord ++ tailWord_3574999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574999).length < 2 ^ (prefixWord ++ tailWord_3574999).sum := by decide
  have hdescent : baseEnd_3574999 < baseStart_3574999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575012 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_3575012 : Nat := 118140960795 + 3575012 * 2 ^ 59
def prefixEnd_3575012 : Nat := 4983230072969 + 3 ^ 40 * 3575012 * 2
def baseEnd_3575012 : Nat := 1835699501591471982808825

theorem tailTrace_3575012 : CollatzResearch.WordTrace tailWord_3575012 prefixEnd_3575012 1835699501591471982808825 := by
  unfold tailWord_3575012
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195699862174781142635645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86927599816233041523514193 65195699862174781142635645)
  ·
    refine ⟨24448387448315542928488367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65195699862174781142635645 24448387448315542928488367)
    ·
      refine ⟨36672581172473314392732551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24448387448315542928488367 36672581172473314392732551)
      ·
        refine ⟨55008871758709971589098827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36672581172473314392732551 55008871758709971589098827)
        ·
          refine ⟨82513307638064957383648241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55008871758709971589098827 82513307638064957383648241)
          ·
            refine ⟨61884980728548718037736181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82513307638064957383648241 61884980728548718037736181)
            ·
              refine ⟨5801716943301442316037767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61884980728548718037736181 5801716943301442316037767)
              ·
                refine ⟨8702575414952163474056651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801716943301442316037767 8702575414952163474056651)
                ·
                  refine ⟨13053863122428245211084977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702575414952163474056651 13053863122428245211084977)
                  ·
                    refine ⟨9790397341821183908313733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13053863122428245211084977 9790397341821183908313733)
                    ·
                      refine ⟨1835699501591471982808825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9790397341821183908313733 1835699501591471982808825)
                      ·
                        rfl

theorem cell23_3575012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_3575012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575012 prefixEnd_3575012 := by exact prefixLift 3575012
  have htrace : WordTrace (prefixWord ++ tailWord_3575012) baseStart_3575012 baseEnd_3575012 := by
    simpa [prefixWord, tailWord_3575012, baseEnd_3575012] using wordTrace_append hprefix tailTrace_3575012
  have hstable : (prefixWord ++ tailWord_3575012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575012).length < 2 ^ (prefixWord ++ tailWord_3575012).sum := by decide
  have hdescent : baseEnd_3575012 < baseStart_3575012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575019 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 3]
def baseStart_3575019 : Nat := 118140960795 + 3575019 * 2 ^ 59
def prefixEnd_3575019 : Nat := 4983230072969 + 3 ^ 40 * 3575019 * 2
def baseEnd_3575019 : Nat := 1835703095956053455421293

theorem tailTrace_3575019 : CollatzResearch.WordTrace tailWord_3575019 prefixEnd_3575019 1835703095956053455421293 := by
  unfold tailWord_3575019
  simp only [CollatzResearch.WordTrace]
  refine ⟨130391655035324202480776111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86927770023549468320517407 130391655035324202480776111)
  ·
    refine ⟨195587482552986303721164167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130391655035324202480776111 195587482552986303721164167)
    ·
      refine ⟨293381223829479455581746251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195587482552986303721164167 293381223829479455581746251)
      ·
        refine ⟨440071835744219183372619377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293381223829479455581746251 440071835744219183372619377)
        ·
          refine ⟨330053876808164387529464533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440071835744219183372619377 330053876808164387529464533)
          ·
            refine ⟨7735637737691352832721825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 330053876808164387529464533 7735637737691352832721825)
            ·
              refine ⟨5801728303268514624541369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735637737691352832721825 5801728303268514624541369)
              ·
                refine ⟨4351296227451385968406027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801728303268514624541369 4351296227451385968406027)
                ·
                  refine ⟨6526944341177078952609041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351296227451385968406027 6526944341177078952609041)
                  ·
                    refine ⟨4895208255882809214456781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526944341177078952609041 4895208255882809214456781)
                    ·
                      refine ⟨1835703095956053455421293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895208255882809214456781 1835703095956053455421293)
                      ·
                        rfl

theorem cell23_3575019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 3].length) (baseStart_3575019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575019 prefixEnd_3575019 := by exact prefixLift 3575019
  have htrace : WordTrace (prefixWord ++ tailWord_3575019) baseStart_3575019 baseEnd_3575019 := by
    simpa [prefixWord, tailWord_3575019, baseEnd_3575019] using wordTrace_append hprefix tailTrace_3575019
  have hstable : (prefixWord ++ tailWord_3575019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575019).length < 2 ^ (prefixWord ++ tailWord_3575019).sum := by decide
  have hdescent : baseEnd_3575019 < baseStart_3575019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575022 : List Nat := [4, 1, 2, 1, 1, 1, 6, 7]
def baseStart_3575022 : Nat := 118140960795 + 3575022 * 2 ^ 59
def prefixEnd_3575022 : Nat := 4983230072969 + 3 ^ 40 * 3575022 * 2
def baseEnd_3575022 : Nat := 67989060607333960877177

theorem tailTrace_3575022 : CollatzResearch.WordTrace tailWord_3575022 prefixEnd_3575022 67989060607333960877177 := by
  unfold tailWord_3575022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16298970556789166749141915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86927842969542222662090213 16298970556789166749141915)
  ·
    refine ⟨24448455835183750123712873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16298970556789166749141915 24448455835183750123712873)
    ·
      refine ⟨18336341876387812592784655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24448455835183750123712873 18336341876387812592784655)
      ·
        refine ⟨27504512814581718889176983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18336341876387812592784655 27504512814581718889176983)
        ·
          refine ⟨41256769221872578333765475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27504512814581718889176983 41256769221872578333765475)
          ·
            refine ⟨61885153832808867500648213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41256769221872578333765475 61885153832808867500648213)
            ·
              refine ⟨2900866585912915664092885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61885153832808867500648213 2900866585912915664092885)
              ·
                refine ⟨67989060607333960877177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2900866585912915664092885 67989060607333960877177)
                ·
                  rfl

theorem cell23_3575022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_3575022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575022 prefixEnd_3575022 := by exact prefixLift 3575022
  have htrace : WordTrace (prefixWord ++ tailWord_3575022) baseStart_3575022 baseEnd_3575022 := by
    simpa [prefixWord, tailWord_3575022, baseEnd_3575022] using wordTrace_append hprefix tailTrace_3575022
  have hstable : (prefixWord ++ tailWord_3575022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575022).length < 2 ^ (prefixWord ++ tailWord_3575022).sum := by decide
  have hdescent : baseEnd_3575022 < baseStart_3575022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575045 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3575045 : Nat := 118140960795 + 3575045 * 2 ^ 59
def prefixEnd_3575045 : Nat := 4983230072969 + 3 ^ 40 * 3575045 * 2
def baseEnd_3575045 : Nat := 1835716446453070353696173

theorem tailTrace_3575045 : CollatzResearch.WordTrace tailWord_3575045 prefixEnd_3575045 1835716446453070353696173 := by
  unfold tailWord_3575045
  simp only [CollatzResearch.WordTrace]
  refine ⟨130392603333230008921222589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86928402222153339280815059 130392603333230008921222589)
  ·
    refine ⟨48897226249961253345458471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130392603333230008921222589 48897226249961253345458471)
    ·
      refine ⟨73345839374941880018187707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48897226249961253345458471 73345839374941880018187707)
      ·
        refine ⟨110018759062412820027281561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73345839374941880018187707 110018759062412820027281561)
        ·
          refine ⟨82514069296809615020461171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110018759062412820027281561 82514069296809615020461171)
          ·
            refine ⟨123771103945214422530691757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82514069296809615020461171 123771103945214422530691757)
            ·
              refine ⟨46414163979455408449009409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123771103945214422530691757 46414163979455408449009409)
              ·
                refine ⟨34810622984591556336757057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46414163979455408449009409 34810622984591556336757057)
                ·
                  refine ⟨26107967238443667252567793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34810622984591556336757057 26107967238443667252567793)
                  ·
                    refine ⟨19580975428832750439425845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26107967238443667252567793 19580975428832750439425845)
                    ·
                      refine ⟨1835716446453070353696173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19580975428832750439425845 1835716446453070353696173)
                      ·
                        rfl

theorem cell23_3575045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3575045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575045 prefixEnd_3575045 := by exact prefixLift 3575045
  have htrace : WordTrace (prefixWord ++ tailWord_3575045) baseStart_3575045 baseEnd_3575045 := by
    simpa [prefixWord, tailWord_3575045, baseEnd_3575045] using wordTrace_append hprefix tailTrace_3575045
  have hstable : (prefixWord ++ tailWord_3575045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575045).length < 2 ^ (prefixWord ++ tailWord_3575045).sum := by decide
  have hdescent : baseEnd_3575045 < baseStart_3575045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575049 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_3575049 : Nat := 118140960795 + 3575049 * 2 ^ 59
def prefixEnd_3575049 : Nat := 4983230072969 + 3 ^ 40 * 3575049 * 2
def baseEnd_3575049 : Nat := 1835718500375688338046155

theorem tailTrace_3575049 : CollatzResearch.WordTrace tailWord_3575049 prefixEnd_3575049 1835718500375688338046155 := by
  unfold tailWord_3575049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130392749225215517604368201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86928499483477011736245467 130392749225215517604368201)
  ·
    refine ⟨97794561918911638203276151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130392749225215517604368201 97794561918911638203276151)
    ·
      refine ⟨146691842878367457304914227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97794561918911638203276151 146691842878367457304914227)
      ·
        refine ⟨220037764317551185957371341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146691842878367457304914227 220037764317551185957371341)
        ·
          refine ⟨82514161619081694734014253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220037764317551185957371341 82514161619081694734014253)
          ·
            refine ⟨30942810607155635525255345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82514161619081694734014253 30942810607155635525255345)
            ·
              refine ⟨23207107955366726643941509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30942810607155635525255345 23207107955366726643941509)
              ·
                refine ⟨4351332741631261245739033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23207107955366726643941509 4351332741631261245739033)
                ·
                  refine ⟨3263499556223445934304275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351332741631261245739033 3263499556223445934304275)
                  ·
                    refine ⟨4895249334335168901456413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263499556223445934304275 4895249334335168901456413)
                    ·
                      refine ⟨1835718500375688338046155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895249334335168901456413 1835718500375688338046155)
                      ·
                        rfl

theorem cell23_3575049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_3575049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575049 prefixEnd_3575049 := by exact prefixLift 3575049
  have htrace : WordTrace (prefixWord ++ tailWord_3575049) baseStart_3575049 baseEnd_3575049 := by
    simpa [prefixWord, tailWord_3575049, baseEnd_3575049] using wordTrace_append hprefix tailTrace_3575049
  have hstable : (prefixWord ++ tailWord_3575049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575049).length < 2 ^ (prefixWord ++ tailWord_3575049).sum := by decide
  have hdescent : baseEnd_3575049 < baseStart_3575049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575066 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3575066 : Nat := 118140960795 + 3575066 * 2 ^ 59
def prefixEnd_3575066 : Nat := 4983230072969 + 3 ^ 40 * 3575066 * 2
def baseEnd_3575066 : Nat := 1835727229546814771533577

theorem tailTrace_3575066 : CollatzResearch.WordTrace tailWord_3575066 prefixEnd_3575066 1835727229546814771533577 := by
  unfold tailWord_3575066
  simp only [CollatzResearch.WordTrace]
  refine ⟨32598342316538482376934263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86928912844102619671824701 32598342316538482376934263)
  ·
    refine ⟨48897513474807723565401395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32598342316538482376934263 48897513474807723565401395)
    ·
      refine ⟨73346270212211585348102093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48897513474807723565401395 73346270212211585348102093)
      ·
        refine ⟨27504851329579344505538285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73346270212211585348102093 27504851329579344505538285)
        ·
          refine ⟨10314319248592254189576857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27504851329579344505538285 10314319248592254189576857)
          ·
            refine ⟨7735739436444190642182643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314319248592254189576857 7735739436444190642182643)
            ·
              refine ⟨11603609154666285963273965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735739436444190642182643 11603609154666285963273965)
              ·
                refine ⟨4351353432999857236227737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11603609154666285963273965 4351353432999857236227737)
                ·
                  refine ⟨3263515074749892927170803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351353432999857236227737 3263515074749892927170803)
                  ·
                    refine ⟨4895272612124839390756205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263515074749892927170803 4895272612124839390756205)
                    ·
                      refine ⟨1835727229546814771533577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895272612124839390756205 1835727229546814771533577)
                      ·
                        rfl

theorem cell23_3575066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3575066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575066 prefixEnd_3575066 := by exact prefixLift 3575066
  have htrace : WordTrace (prefixWord ++ tailWord_3575066) baseStart_3575066 baseEnd_3575066 := by
    simpa [prefixWord, tailWord_3575066, baseEnd_3575066] using wordTrace_append hprefix tailTrace_3575066
  have hstable : (prefixWord ++ tailWord_3575066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575066).length < 2 ^ (prefixWord ++ tailWord_3575066).sum := by decide
  have hdescent : baseEnd_3575066 < baseStart_3575066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575070 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3575070 : Nat := 118140960795 + 3575070 * 2 ^ 59
def prefixEnd_3575070 : Nat := 4983230072969 + 3 ^ 40 * 3575070 * 2
def baseEnd_3575070 : Nat := 1835729283469432755883559

theorem tailTrace_3575070 : CollatzResearch.WordTrace tailWord_3575070 prefixEnd_3575070 1835729283469432755883559 := by
  unfold tailWord_3575070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299189394767429773860333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86929010105426292127255109 16299189394767429773860333)
  ·
    refine ⟨6112196023037786165197625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16299189394767429773860333 6112196023037786165197625)
    ·
      refine ⟨4584147017278339623898219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6112196023037786165197625 4584147017278339623898219)
      ·
        refine ⟨6876220525917509435847329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584147017278339623898219 6876220525917509435847329)
        ·
          refine ⟨5157165394438132076885497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6876220525917509435847329 5157165394438132076885497)
          ·
            refine ⟨3867874045828599057664123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5157165394438132076885497 3867874045828599057664123)
            ·
              refine ⟨5801811068742898586496185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867874045828599057664123 5801811068742898586496185)
              ·
                refine ⟨4351358301557173939872139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801811068742898586496185 4351358301557173939872139)
                ·
                  refine ⟨6527037452335760909808209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351358301557173939872139 6527037452335760909808209)
                  ·
                    refine ⟨4895278089251820682356157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6527037452335760909808209 4895278089251820682356157)
                    ·
                      refine ⟨1835729283469432755883559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895278089251820682356157 1835729283469432755883559)
                      ·
                        rfl

theorem cell23_3575070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3575070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575070 prefixEnd_3575070 := by exact prefixLift 3575070
  have htrace : WordTrace (prefixWord ++ tailWord_3575070) baseStart_3575070 baseEnd_3575070 := by
    simpa [prefixWord, tailWord_3575070, baseEnd_3575070] using wordTrace_append hprefix tailTrace_3575070
  have hstable : (prefixWord ++ tailWord_3575070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575070).length < 2 ^ (prefixWord ++ tailWord_3575070).sum := by decide
  have hdescent : baseEnd_3575070 < baseStart_3575070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575089 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_3575089 : Nat := 118140960795 + 3575089 * 2 ^ 59
def prefixEnd_3575089 : Nat := 4983230072969 + 3 ^ 40 * 3575089 * 2
def baseEnd_3575089 : Nat := 1835739039601868181545971

theorem tailTrace_3575089 : CollatzResearch.WordTrace tailWord_3575089 prefixEnd_3575089 1835739039601868181545971 := by
  unfold tailWord_3575089
  simp only [CollatzResearch.WordTrace]
  refine ⟨130394208145070604435824321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86929472096713736290549547 130394208145070604435824321)
  ·
    refine ⟨97795656108802953326868241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130394208145070604435824321 97795656108802953326868241)
    ·
      refine ⟨73346742081602214995151181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97795656108802953326868241 73346742081602214995151181)
      ·
        refine ⟨27505028280600830623181693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73346742081602214995151181 27505028280600830623181693)
        ·
          refine ⟨10314385605225311483693135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27505028280600830623181693 10314385605225311483693135)
          ·
            refine ⟨15471578407837967225539703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314385605225311483693135 15471578407837967225539703)
            ·
              refine ⟨23207367611756950838309555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15471578407837967225539703 23207367611756950838309555)
              ·
                refine ⟨34811051417635426257464333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23207367611756950838309555 34811051417635426257464333)
                ·
                  refine ⟨13054144281613284846549125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34811051417635426257464333 13054144281613284846549125)
                  ·
                    refine ⟨2447652052802490908727961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13054144281613284846549125 2447652052802490908727961)
                    ·
                      refine ⟨1835739039601868181545971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447652052802490908727961 1835739039601868181545971)
                      ·
                        rfl

theorem cell23_3575089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_3575089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575089 prefixEnd_3575089 := by exact prefixLift 3575089
  have htrace : WordTrace (prefixWord ++ tailWord_3575089) baseStart_3575089 baseEnd_3575089 := by
    simpa [prefixWord, tailWord_3575089, baseEnd_3575089] using wordTrace_append hprefix tailTrace_3575089
  have hstable : (prefixWord ++ tailWord_3575089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575089).length < 2 ^ (prefixWord ++ tailWord_3575089).sum := by decide
  have hdescent : baseEnd_3575089 < baseStart_3575089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575093 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_3575093 : Nat := 118140960795 + 3575093 * 2 ^ 59
def prefixEnd_3575093 : Nat := 4983230072969 + 3 ^ 40 * 3575093 * 2
def baseEnd_3575093 : Nat := 1835741093524486165895953

theorem tailTrace_3575093 : CollatzResearch.WordTrace tailWord_3575093 prefixEnd_3575093 1835741093524486165895953 := by
  unfold tailWord_3575093
  simp only [CollatzResearch.WordTrace]
  refine ⟨130394354037056113118969933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86929569358037408745979955 130394354037056113118969933)
  ·
    refine ⟨48897882763896042419613725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130394354037056113118969933 48897882763896042419613725)
    ·
      refine ⟨18336706036461015907355147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48897882763896042419613725 18336706036461015907355147)
      ·
        refine ⟨27505059054691523861032721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18336706036461015907355147 27505059054691523861032721)
        ·
          refine ⟨20628794291018642895774541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27505059054691523861032721 20628794291018642895774541)
          ·
            refine ⟨7735797859131991085915453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20628794291018642895774541 7735797859131991085915453)
            ·
              refine ⟨2900924197174496657218295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735797859131991085915453 2900924197174496657218295)
              ·
                refine ⟨4351386295761744985827443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900924197174496657218295 4351386295761744985827443)
                ·
                  refine ⟨6527079443642617478741165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351386295761744985827443 6527079443642617478741165)
                  ·
                    refine ⟨2447654791365981554527937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6527079443642617478741165 2447654791365981554527937)
                    ·
                      refine ⟨1835741093524486165895953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447654791365981554527937 1835741093524486165895953)
                      ·
                        rfl

theorem cell23_3575093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_3575093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575093 prefixEnd_3575093 := by exact prefixLift 3575093
  have htrace : WordTrace (prefixWord ++ tailWord_3575093) baseStart_3575093 baseEnd_3575093 := by
    simpa [prefixWord, tailWord_3575093, baseEnd_3575093] using wordTrace_append hprefix tailTrace_3575093
  have hstable : (prefixWord ++ tailWord_3575093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575093).length < 2 ^ (prefixWord ++ tailWord_3575093).sum := by decide
  have hdescent : baseEnd_3575093 < baseStart_3575093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575157 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3575157 : Nat := 118140960795 + 3575157 * 2 ^ 59
def prefixEnd_3575157 : Nat := 4983230072969 + 3 ^ 40 * 3575157 * 2
def baseEnd_3575157 : Nat := 1835773956286373915495659

theorem tailTrace_3575157 : CollatzResearch.WordTrace tailWord_3575157 prefixEnd_3575157 1835773956286373915495659 := by
  unfold tailWord_3575157
  simp only [CollatzResearch.WordTrace]
  refine ⟨130396688308824252049299725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86931125539216168032866483 130396688308824252049299725)
  ·
    refine ⟨48898758115809094518487397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130396688308824252049299725 48898758115809094518487397)
    ·
      refine ⟨9168517146714205222216387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48898758115809094518487397 9168517146714205222216387)
      ·
        refine ⟨13752775720071307833324581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9168517146714205222216387 13752775720071307833324581)
        ·
          refine ⟨2578645447513370218748359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13752775720071307833324581 2578645447513370218748359)
          ·
            refine ⟨3867968171270055328122539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578645447513370218748359 3867968171270055328122539)
            ·
              refine ⟨5801952256905082992183809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867968171270055328122539 5801952256905082992183809)
              ·
                refine ⟨4351464192678812244137857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801952256905082992183809 4351464192678812244137857)
                ·
                  refine ⟨3263598144509109183103393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351464192678812244137857 3263598144509109183103393)
                  ·
                    refine ⟨2447698608381831887327545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263598144509109183103393 2447698608381831887327545)
                    ·
                      refine ⟨1835773956286373915495659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447698608381831887327545 1835773956286373915495659)
                      ·
                        rfl

theorem cell23_3575157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3575157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575157 prefixEnd_3575157 := by exact prefixLift 3575157
  have htrace : WordTrace (prefixWord ++ tailWord_3575157) baseStart_3575157 baseEnd_3575157 := by
    simpa [prefixWord, tailWord_3575157, baseEnd_3575157] using wordTrace_append hprefix tailTrace_3575157
  have hstable : (prefixWord ++ tailWord_3575157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575157).length < 2 ^ (prefixWord ++ tailWord_3575157).sum := by decide
  have hdescent : baseEnd_3575157 < baseStart_3575157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575179 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 4, 2]
def baseStart_3575179 : Nat := 118140960795 + 3575179 * 2 ^ 59
def prefixEnd_3575179 : Nat := 4983230072969 + 3 ^ 40 * 3575179 * 2
def baseEnd_3575179 : Nat := 1835785252860772829420557

theorem tailTrace_3575179 : CollatzResearch.WordTrace tailWord_3575179 prefixEnd_3575179 1835785252860772829420557 := by
  unfold tailWord_3575179
  simp only [CollatzResearch.WordTrace]
  refine ⟨130397490714744549806600591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86931660476496366537733727 130397490714744549806600591)
  ·
    refine ⟨195596236072116824709900887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130397490714744549806600591 195596236072116824709900887)
    ·
      refine ⟨293394354108175237064851331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195596236072116824709900887 293394354108175237064851331)
      ·
        refine ⟨440091531162262855597276997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293394354108175237064851331 440091531162262855597276997)
        ·
          refine ⟨82517162092924285424489437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440091531162262855597276997 82517162092924285424489437)
          ·
            refine ⟨30943935784846607034183539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82517162092924285424489437 30943935784846607034183539)
            ·
              refine ⟨46415903677269910551275309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30943935784846607034183539 46415903677269910551275309)
              ·
                refine ⟨17405963878976216456728241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46415903677269910551275309 17405963878976216456728241)
                ·
                  refine ⟨13054472909232162342546181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17405963878976216456728241 13054472909232162342546181)
                  ·
                    refine ⟨2447713670481030439227409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13054472909232162342546181 2447713670481030439227409)
                    ·
                      refine ⟨1835785252860772829420557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447713670481030439227409 1835785252860772829420557)
                      ·
                        rfl

theorem cell23_3575179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4, 2].length) (baseStart_3575179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575179 prefixEnd_3575179 := by exact prefixLift 3575179
  have htrace : WordTrace (prefixWord ++ tailWord_3575179) baseStart_3575179 baseEnd_3575179 := by
    simpa [prefixWord, tailWord_3575179, baseEnd_3575179] using wordTrace_append hprefix tailTrace_3575179
  have hstable : (prefixWord ++ tailWord_3575179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575179).length < 2 ^ (prefixWord ++ tailWord_3575179).sum := by decide
  have hdescent : baseEnd_3575179 < baseStart_3575179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575189 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3575189 : Nat := 118140960795 + 3575189 * 2 ^ 59
def prefixEnd_3575189 : Nat := 4983230072969 + 3 ^ 40 * 3575189 * 2
def baseEnd_3575189 : Nat := 611930129222439263431837

theorem tailTrace_3575189 : CollatzResearch.WordTrace tailWord_3575189 prefixEnd_3575189 611930129222439263431837 := by
  unfold tailWord_3575189
  simp only [CollatzResearch.WordTrace]
  refine ⟨130397855444708321514464621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86931903629805547676309747 130397855444708321514464621)
  ·
    refine ⟨48899195791765620567924233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130397855444708321514464621 48899195791765620567924233)
    ·
      refine ⟨36674396843824215425943175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48899195791765620567924233 36674396843824215425943175)
      ·
        refine ⟨55011595265736323138914763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36674396843824215425943175 55011595265736323138914763)
        ·
          refine ⟨82517392898604484708372145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55011595265736323138914763 82517392898604484708372145)
          ·
            refine ⟨61888044673953363531279109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82517392898604484708372145 61888044673953363531279109)
            ·
              refine ⟨11604008376366255662114833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61888044673953363531279109 11604008376366255662114833)
              ·
                refine ⟨8703006282274691746586125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604008376366255662114833 8703006282274691746586125)
                ·
                  refine ⟨3263627355853009404969797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8703006282274691746586125 3263627355853009404969797)
                  ·
                    refine ⟨611930129222439263431837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263627355853009404969797 611930129222439263431837)
                    ·
                      rfl

theorem cell23_3575189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3575189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575189 prefixEnd_3575189 := by exact prefixLift 3575189
  have htrace : WordTrace (prefixWord ++ tailWord_3575189) baseStart_3575189 baseEnd_3575189 := by
    simpa [prefixWord, tailWord_3575189, baseEnd_3575189] using wordTrace_append hprefix tailTrace_3575189
  have hstable : (prefixWord ++ tailWord_3575189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575189).length < 2 ^ (prefixWord ++ tailWord_3575189).sum := by decide
  have hdescent : baseEnd_3575189 < baseStart_3575189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575199 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3575199 : Nat := 118140960795 + 3575199 * 2 ^ 59
def prefixEnd_3575199 : Nat := 4983230072969 + 3 ^ 40 * 3575199 * 2
def baseEnd_3575199 : Nat := 1835795522473862751170465

theorem tailTrace_3575199 : CollatzResearch.WordTrace tailWord_3575199 prefixEnd_3575199 1835795522473862751170465 := by
  unfold tailWord_3575199
  simp only [CollatzResearch.WordTrace]
  refine ⟨130398220174672093222328651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86932146783114728814885767 130398220174672093222328651)
  ·
    refine ⟨195597330262008139833492977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130398220174672093222328651 195597330262008139833492977)
    ·
      refine ⟨146697997696506104875119733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195597330262008139833492977 146697997696506104875119733)
      ·
        refine ⟨13752937284047447332042475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146697997696506104875119733 13752937284047447332042475)
        ·
          refine ⟨20629405926071170998063713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13752937284047447332042475 20629405926071170998063713)
          ·
            refine ⟨15472054444553378248547785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20629405926071170998063713 15472054444553378248547785)
            ·
              refine ⟨11604040833415033686410839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15472054444553378248547785 11604040833415033686410839)
              ·
                refine ⟨17406061250122550529616259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604040833415033686410839 17406061250122550529616259)
                ·
                  refine ⟨26109091875183825794424389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17406061250122550529616259 26109091875183825794424389)
                  ·
                    refine ⟨4895454726596967336454573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26109091875183825794424389 4895454726596967336454573)
                    ·
                      refine ⟨1835795522473862751170465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895454726596967336454573 1835795522473862751170465)
                      ·
                        rfl

theorem cell23_3575199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3575199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575199 prefixEnd_3575199 := by exact prefixLift 3575199
  have htrace : WordTrace (prefixWord ++ tailWord_3575199) baseStart_3575199 baseEnd_3575199 := by
    simpa [prefixWord, tailWord_3575199, baseEnd_3575199] using wordTrace_append hprefix tailTrace_3575199
  have hstable : (prefixWord ++ tailWord_3575199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575199).length < 2 ^ (prefixWord ++ tailWord_3575199).sum := by decide
  have hdescent : baseEnd_3575199 < baseStart_3575199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575223 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 1, 4]
def baseStart_3575223 : Nat := 118140960795 + 3575223 * 2 ^ 59
def prefixEnd_3575223 : Nat := 4983230072969 + 3 ^ 40 * 3575223 * 2
def baseEnd_3575223 : Nat := 611935948669856885756785

theorem tailTrace_3575223 : CollatzResearch.WordTrace tailWord_3575223 prefixEnd_3575223 611935948669856885756785 := by
  unfold tailWord_3575223
  simp only [CollatzResearch.WordTrace]
  refine ⟨130399095526585145321202323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86932730351056763547468215 130399095526585145321202323)
  ·
    refine ⟨195598643289877717981803485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130399095526585145321202323 195598643289877717981803485)
    ·
      refine ⟨73349491233704144243176307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195598643289877717981803485 73349491233704144243176307)
      ·
        refine ⟨110024236850556216364764461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73349491233704144243176307 110024236850556216364764461)
        ·
          refine ⟨41259088818958581136786673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110024236850556216364764461 41259088818958581136786673)
          ·
            refine ⟨30944316614218935852590005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41259088818958581136786673 30944316614218935852590005)
            ·
              refine ⟨2901029682583025236180313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30944316614218935852590005 2901029682583025236180313)
              ·
                refine ⟨2175772261937268927135235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901029682583025236180313 2175772261937268927135235)
                ·
                  refine ⟨3263658392905903390702853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175772261937268927135235 3263658392905903390702853)
                  ·
                    refine ⟨611935948669856885756785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263658392905903390702853 611935948669856885756785)
                    ·
                      rfl

theorem cell23_3575223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_3575223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575223 prefixEnd_3575223 := by exact prefixLift 3575223
  have htrace : WordTrace (prefixWord ++ tailWord_3575223) baseStart_3575223 baseEnd_3575223 := by
    simpa [prefixWord, tailWord_3575223, baseEnd_3575223] using wordTrace_append hprefix tailTrace_3575223
  have hstable : (prefixWord ++ tailWord_3575223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575223).length < 2 ^ (prefixWord ++ tailWord_3575223).sum := by decide
  have hdescent : baseEnd_3575223 < baseStart_3575223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575236 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 6]
def baseStart_3575236 : Nat := 118140960795 + 3575236 * 2 ^ 59
def prefixEnd_3575236 : Nat := 4983230072969 + 3 ^ 40 * 3575236 * 2
def baseEnd_3575236 : Nat := 203979391250897678489755

theorem tailTrace_3575236 : CollatzResearch.WordTrace tailWord_3575236 prefixEnd_3575236 203979391250897678489755 := by
  unfold tailWord_3575236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65199784837769024270712781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86933046450358699027617041 65199784837769024270712781)
  ·
    refine ⟨24449919314163384101517293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65199784837769024270712781 24449919314163384101517293)
    ·
      refine ⟨9168719742811269038068985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24449919314163384101517293 9168719742811269038068985)
      ·
        refine ⟨6876539807108451778551739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168719742811269038068985 6876539807108451778551739)
        ·
          refine ⟨10314809710662677667827609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876539807108451778551739 10314809710662677667827609)
          ·
            refine ⟨7736107282997008250870707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314809710662677667827609 7736107282997008250870707)
            ·
              refine ⟨11604160924495512376306061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736107282997008250870707 11604160924495512376306061)
              ·
                refine ⟨4351560346685817141114773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11604160924495512376306061 4351560346685817141114773)
                ·
                  refine ⟨203979391250897678489755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4351560346685817141114773 203979391250897678489755)
                  ·
                    rfl

theorem cell23_3575236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_3575236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575236 prefixEnd_3575236 := by exact prefixLift 3575236
  have htrace : WordTrace (prefixWord ++ tailWord_3575236) baseStart_3575236 baseEnd_3575236 := by
    simpa [prefixWord, tailWord_3575236, baseEnd_3575236] using wordTrace_append hprefix tailTrace_3575236
  have hstable : (prefixWord ++ tailWord_3575236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575236).length < 2 ^ (prefixWord ++ tailWord_3575236).sum := by decide
  have hdescent : baseEnd_3575236 < baseStart_3575236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575246 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3575246 : Nat := 118140960795 + 3575246 * 2 ^ 59
def prefixEnd_3575246 : Nat := 4983230072969 + 3 ^ 40 * 3575246 * 2
def baseEnd_3575246 : Nat := 1835819656064624067282749

theorem tailTrace_3575246 : CollatzResearch.WordTrace tailWord_3575246 prefixEnd_3575246 1835819656064624067282749 := by
  unfold tailWord_3575246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299991800687727531161199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86933289603667880166193061 16299991800687727531161199)
  ·
    refine ⟨24449987701031591296741799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16299991800687727531161199 24449987701031591296741799)
    ·
      refine ⟨36674981551547386945112699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24449987701031591296741799 36674981551547386945112699)
      ·
        refine ⟨55012472327321080417669049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36674981551547386945112699 55012472327321080417669049)
        ·
          refine ⟨41259354245490810313251787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55012472327321080417669049 41259354245490810313251787)
          ·
            refine ⟨61889031368236215469877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41259354245490810313251787 61889031368236215469877681)
            ·
              refine ⟨46416773526177161602408261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61889031368236215469877681 46416773526177161602408261)
              ·
                refine ⟨8703145036158217800451549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46416773526177161602408261 8703145036158217800451549)
                ·
                  refine ⟨3263679388559331675169331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8703145036158217800451549 3263679388559331675169331)
                  ·
                    refine ⟨4895519082838997512753997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263679388559331675169331 4895519082838997512753997)
                    ·
                      refine ⟨1835819656064624067282749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895519082838997512753997 1835819656064624067282749)
                      ·
                        rfl

theorem cell23_3575246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3575246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575246 prefixEnd_3575246 := by exact prefixLift 3575246
  have htrace : WordTrace (prefixWord ++ tailWord_3575246) baseStart_3575246 baseEnd_3575246 := by
    simpa [prefixWord, tailWord_3575246, baseEnd_3575246] using wordTrace_append hprefix tailTrace_3575246
  have hstable : (prefixWord ++ tailWord_3575246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575246).length < 2 ^ (prefixWord ++ tailWord_3575246).sum := by decide
  have hdescent : baseEnd_3575246 < baseStart_3575246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575256 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_3575256 : Nat := 118140960795 + 3575256 * 2 ^ 59
def prefixEnd_3575256 : Nat := 4983230072969 + 3 ^ 40 * 3575256 * 2
def baseEnd_3575256 : Nat := 1835824790871169028157703

theorem tailTrace_3575256 : CollatzResearch.WordTrace tailWord_3575256 prefixEnd_3575256 1835824790871169028157703 := by
  unfold tailWord_3575256
  simp only [CollatzResearch.WordTrace]
  refine ⟨65200149567732795978576811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86933532756977061304769081 65200149567732795978576811)
  ·
    refine ⟨97800224351599193967865217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65200149567732795978576811 97800224351599193967865217)
    ·
      refine ⟨73350168263699395475898913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97800224351599193967865217 73350168263699395475898913)
      ·
        refine ⟨55012626197774546606924185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73350168263699395475898913 55012626197774546606924185)
        ·
          refine ⟨41259469648330909955193139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55012626197774546606924185 41259469648330909955193139)
          ·
            refine ⟨61889204472496364932789709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41259469648330909955193139 61889204472496364932789709)
            ·
              refine ⟨23208451677186136849796141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61889204472496364932789709 23208451677186136849796141)
              ·
                refine ⟨8703169378944801318673553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23208451677186136849796141 8703169378944801318673553)
                ·
                  refine ⟨6527377034208600989005165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703169378944801318673553 6527377034208600989005165)
                  ·
                    refine ⟨2447766387828225370876937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6527377034208600989005165 2447766387828225370876937)
                    ·
                      refine ⟨1835824790871169028157703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447766387828225370876937 1835824790871169028157703)
                      ·
                        rfl

theorem cell23_3575256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_3575256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575256 prefixEnd_3575256 := by exact prefixLift 3575256
  have htrace : WordTrace (prefixWord ++ tailWord_3575256) baseStart_3575256 baseEnd_3575256 := by
    simpa [prefixWord, tailWord_3575256, baseEnd_3575256] using wordTrace_append hprefix tailTrace_3575256
  have hstable : (prefixWord ++ tailWord_3575256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575256).length < 2 ^ (prefixWord ++ tailWord_3575256).sum := by decide
  have hdescent : baseEnd_3575256 < baseStart_3575256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575263 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 1, 1, 3]
def baseStart_3575263 : Nat := 118140960795 + 3575263 * 2 ^ 59
def prefixEnd_3575263 : Nat := 4983230072969 + 3 ^ 40 * 3575263 * 2
def baseEnd_3575263 : Nat := 1835828385235750500770171

theorem tailTrace_3575263 : CollatzResearch.WordTrace tailWord_3575263 prefixEnd_3575263 1835828385235750500770171 := by
  unfold tailWord_3575263
  simp only [CollatzResearch.WordTrace]
  refine ⟨130400554446440232152658443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86933702964293488101772295 130400554446440232152658443)
  ·
    refine ⟨195600831669660348228987665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130400554446440232152658443 195600831669660348228987665)
    ·
      refine ⟨146700623752245261171740749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195600831669660348228987665 146700623752245261171740749)
      ·
        refine ⟨55012733907091972939402781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146700623752245261171740749 55012733907091972939402781)
        ·
          refine ⟨20629775215159489852276043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55012733907091972939402781 20629775215159489852276043)
          ·
            refine ⟨30944662822739234778414065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20629775215159489852276043 30944662822739234778414065)
            ·
              refine ⟨23208497117054426083810549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30944662822739234778414065 23208497117054426083810549)
              ·
                refine ⟨2175796604723852445357239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23208497117054426083810549 2175796604723852445357239)
                ·
                  refine ⟨3263694907085778668035859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175796604723852445357239 3263694907085778668035859)
                  ·
                    refine ⟨4895542360628668002053789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263694907085778668035859 4895542360628668002053789)
                    ·
                      refine ⟨1835828385235750500770171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895542360628668002053789 1835828385235750500770171)
                      ·
                        rfl

theorem cell23_3575263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_3575263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575263 prefixEnd_3575263 := by exact prefixLift 3575263
  have htrace : WordTrace (prefixWord ++ tailWord_3575263) baseStart_3575263 baseEnd_3575263 := by
    simpa [prefixWord, tailWord_3575263, baseEnd_3575263] using wordTrace_append hprefix tailTrace_3575263
  have hstable : (prefixWord ++ tailWord_3575263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575263).length < 2 ^ (prefixWord ++ tailWord_3575263).sum := by decide
  have hdescent : baseEnd_3575263 < baseStart_3575263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575279 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 4, 4]
def baseStart_3575279 : Nat := 118140960795 + 3575279 * 2 ^ 59
def prefixEnd_3575279 : Nat := 4983230072969 + 3 ^ 40 * 3575279 * 2
def baseEnd_3575279 : Nat := 611945533642074146056699

theorem tailTrace_3575279 : CollatzResearch.WordTrace tailWord_3575279 prefixEnd_3575279 611945533642074146056699 := by
  unfold tailWord_3575279
  simp only [CollatzResearch.WordTrace]
  refine ⟨130401138014382266885240891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86934092009588177923493927 130401138014382266885240891)
  ·
    refine ⟨195601707021573400327861337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130401138014382266885240891 195601707021573400327861337)
    ·
      refine ⟨146701280266180050245896003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195601707021573400327861337 146701280266180050245896003)
      ·
        refine ⟨220051920399270075368844005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146701280266180050245896003 220051920399270075368844005)
        ·
          refine ⟨41259735074863139131658251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220051920399270075368844005 41259735074863139131658251)
          ·
            refine ⟨61889602612294708697487377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41259735074863139131658251 61889602612294708697487377)
            ·
              refine ⟨46417201959221031523115533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61889602612294708697487377 46417201959221031523115533)
              ·
                refine ⟨17406450734707886821168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46417201959221031523115533 17406450734707886821168325)
                ·
                  refine ⟨3263709512757728778969061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17406450734707886821168325 3263709512757728778969061)
                  ·
                    refine ⟨611945533642074146056699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263709512757728778969061 611945533642074146056699)
                    ·
                      rfl

theorem cell23_3575279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_3575279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575279 prefixEnd_3575279 := by exact prefixLift 3575279
  have htrace : WordTrace (prefixWord ++ tailWord_3575279) baseStart_3575279 baseEnd_3575279 := by
    simpa [prefixWord, tailWord_3575279, baseEnd_3575279] using wordTrace_append hprefix tailTrace_3575279
  have hstable : (prefixWord ++ tailWord_3575279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575279).length < 2 ^ (prefixWord ++ tailWord_3575279).sum := by decide
  have hdescent : baseEnd_3575279 < baseStart_3575279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575280 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 1, 1, 3]
def baseStart_3575280 : Nat := 118140960795 + 3575280 * 2 ^ 59
def prefixEnd_3575280 : Nat := 4983230072969 + 3 ^ 40 * 3575280 * 2
def baseEnd_3575280 : Nat := 1835837114406876934257593

theorem tailTrace_3575280 : CollatzResearch.WordTrace tailWord_3575280 prefixEnd_3575280 1835837114406876934257593 := by
  unfold tailWord_3575280
  simp only [CollatzResearch.WordTrace]
  refine ⟨65200587243689322028013647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86934116324919096037351529 65200587243689322028013647)
  ·
    refine ⟨97800880865533983042020471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65200587243689322028013647 97800880865533983042020471)
    ·
      refine ⟨146701321298300974563030707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97800880865533983042020471 146701321298300974563030707)
      ·
        refine ⟨220051981947451461844546061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146701321298300974563030707 220051981947451461844546061)
        ·
          refine ⟨82519493230294298191704773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220051981947451461844546061 82519493230294298191704773)
          ·
            refine ⟨15472404980680180910944645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82519493230294298191704773 15472404980680180910944645)
            ·
              refine ⟨2901075933877533920802121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15472404980680180910944645 2901075933877533920802121)
              ·
                refine ⟨2175806950408150440601591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901075933877533920802121 2175806950408150440601591)
                ·
                  refine ⟨3263710425612225660902387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175806950408150440601591 3263710425612225660902387)
                  ·
                    refine ⟨4895565638418338491353581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3263710425612225660902387 4895565638418338491353581)
                    ·
                      refine ⟨1835837114406876934257593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895565638418338491353581 1835837114406876934257593)
                      ·
                        rfl

theorem cell23_3575280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 1, 3].length) (baseStart_3575280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575280 prefixEnd_3575280 := by exact prefixLift 3575280
  have htrace : WordTrace (prefixWord ++ tailWord_3575280) baseStart_3575280 baseEnd_3575280 := by
    simpa [prefixWord, tailWord_3575280, baseEnd_3575280] using wordTrace_append hprefix tailTrace_3575280
  have hstable : (prefixWord ++ tailWord_3575280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575280).length < 2 ^ (prefixWord ++ tailWord_3575280).sum := by decide
  have hdescent : baseEnd_3575280 < baseStart_3575280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575286 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3575286 : Nat := 118140960795 + 3575286 * 2 ^ 59
def prefixEnd_3575286 : Nat := 4983230072969 + 3 ^ 40 * 3575286 * 2
def baseEnd_3575286 : Nat := 1835840195290803910782565

theorem tailTrace_3575286 : CollatzResearch.WordTrace tailWord_3575286 prefixEnd_3575286 1835840195290803910782565 := by
  unfold tailWord_3575286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150087082834806692546607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86934262216904604720497141 8150087082834806692546607)
  ·
    refine ⟨12225130624252210038819911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150087082834806692546607 12225130624252210038819911)
    ·
      refine ⟨18337695936378315058229867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225130624252210038819911 18337695936378315058229867)
      ·
        refine ⟨27506543904567472587344801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18337695936378315058229867 27506543904567472587344801)
        ·
          refine ⟨20629907928425604440508601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27506543904567472587344801 20629907928425604440508601)
          ·
            refine ⟨15472430946319203330381451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20629907928425604440508601 15472430946319203330381451)
            ·
              refine ⟨23208646419478804995572177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472430946319203330381451 23208646419478804995572177)
              ·
                refine ⟨17406484814609103746679133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23208646419478804995572177 17406484814609103746679133)
                ·
                  refine ⟨6527431805478413905004675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17406484814609103746679133 6527431805478413905004675)
                  ·
                    refine ⟨9791147708217620857507013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6527431805478413905004675 9791147708217620857507013)
                    ·
                      refine ⟨1835840195290803910782565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9791147708217620857507013 1835840195290803910782565)
                      ·
                        rfl

theorem cell23_3575286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3575286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575286 prefixEnd_3575286 := by exact prefixLift 3575286
  have htrace : WordTrace (prefixWord ++ tailWord_3575286) baseStart_3575286 baseEnd_3575286 := by
    simpa [prefixWord, tailWord_3575286, baseEnd_3575286] using wordTrace_append hprefix tailTrace_3575286
  have hstable : (prefixWord ++ tailWord_3575286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575286).length < 2 ^ (prefixWord ++ tailWord_3575286).sum := by decide
  have hdescent : baseEnd_3575286 < baseStart_3575286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575303 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3575303 : Nat := 118140960795 + 3575303 * 2 ^ 59
def prefixEnd_3575303 : Nat := 4983230072969 + 3 ^ 40 * 3575303 * 2
def baseEnd_3575303 : Nat := 1835848924461930344269987

theorem tailTrace_3575303 : CollatzResearch.WordTrace tailWord_3575303 prefixEnd_3575303 1835848924461930344269987 := by
  unfold tailWord_3575303
  simp only [CollatzResearch.WordTrace]
  refine ⟨130402013366295318984114563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86934675577530212656076375 130402013366295318984114563)
  ·
    refine ⟨195603020049442978476171845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130402013366295318984114563 195603020049442978476171845)
    ·
      refine ⟨36675566259270558464282221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195603020049442978476171845 36675566259270558464282221)
      ·
        refine ⟨13753337347226459424105833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36675566259270558464282221 13753337347226459424105833)
        ·
          refine ⟨10315003010419844568079375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13753337347226459424105833 10315003010419844568079375)
          ·
            refine ⟨15472504515629766852119063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315003010419844568079375 15472504515629766852119063)
            ·
              refine ⟨23208756773444650278178595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472504515629766852119063 23208756773444650278178595)
              ·
                refine ⟨34813135160166975417267893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23208756773444650278178595 34813135160166975417267893)
                ·
                  refine ⟨3263731421265653945368865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34813135160166975417267893 3263731421265653945368865)
                  ·
                    refine ⟨2447798565949240459026649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263731421265653945368865 2447798565949240459026649)
                    ·
                      refine ⟨1835848924461930344269987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447798565949240459026649 1835848924461930344269987)
                      ·
                        rfl

theorem cell23_3575303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3575303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575303 prefixEnd_3575303 := by exact prefixLift 3575303
  have htrace : WordTrace (prefixWord ++ tailWord_3575303) baseStart_3575303 baseEnd_3575303 := by
    simpa [prefixWord, tailWord_3575303, baseEnd_3575303] using wordTrace_append hprefix tailTrace_3575303
  have hstable : (prefixWord ++ tailWord_3575303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575303).length < 2 ^ (prefixWord ++ tailWord_3575303).sum := by decide
  have hdescent : baseEnd_3575303 < baseStart_3575303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575306 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3575306 : Nat := 118140960795 + 3575306 * 2 ^ 59
def prefixEnd_3575306 : Nat := 4983230072969 + 3 ^ 40 * 3575306 * 2
def baseEnd_3575306 : Nat := 1835850464903893832532473

theorem tailTrace_3575306 : CollatzResearch.WordTrace tailWord_3575306 prefixEnd_3575306 1835850464903893832532473 := by
  unfold tailWord_3575306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32600530696321112624118443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86934748523522966997649181 32600530696321112624118443)
  ·
    refine ⟨48900796044481668936177665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32600530696321112624118443 48900796044481668936177665)
    ·
      refine ⟨36675597033361251702133249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48900796044481668936177665 36675597033361251702133249)
      ·
        refine ⟨27506697775020938776599937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36675597033361251702133249 27506697775020938776599937)
        ·
          refine ⟨20630023331265704082449953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27506697775020938776599937 20630023331265704082449953)
          ·
            refine ⟨15472517498449278061837465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20630023331265704082449953 15472517498449278061837465)
            ·
              refine ⟨11604388123836958546378099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15472517498449278061837465 11604388123836958546378099)
              ·
                refine ⟨17406582185755437819567149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604388123836958546378099 17406582185755437819567149)
                ·
                  refine ⟨6527468319658289182337681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17406582185755437819567149 6527468319658289182337681)
                  ·
                    refine ⟨4895601239743716886753261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6527468319658289182337681 4895601239743716886753261)
                    ·
                      refine ⟨1835850464903893832532473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895601239743716886753261 1835850464903893832532473)
                      ·
                        rfl

theorem cell23_3575306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3575306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575306 prefixEnd_3575306 := by exact prefixLift 3575306
  have htrace : WordTrace (prefixWord ++ tailWord_3575306) baseStart_3575306 baseEnd_3575306 := by
    simpa [prefixWord, tailWord_3575306, baseEnd_3575306] using wordTrace_append hprefix tailTrace_3575306
  have hstable : (prefixWord ++ tailWord_3575306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575306).length < 2 ^ (prefixWord ++ tailWord_3575306).sum := by decide
  have hdescent : baseEnd_3575306 < baseStart_3575306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575320 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3575320 : Nat := 118140960795 + 3575320 * 2 ^ 59
def prefixEnd_3575320 : Nat := 4983230072969 + 3 ^ 40 * 3575320 * 2
def baseEnd_3575320 : Nat := 1835857653633056777757409

theorem tailTrace_3575320 : CollatzResearch.WordTrace tailWord_3575320 prefixEnd_3575320 1835857653633056777757409 := by
  unfold tailWord_3575320
  simp only [CollatzResearch.WordTrace]
  refine ⟨65201316703616865443741707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86935088938155820591655609 65201316703616865443741707)
  ·
    refine ⟨97801975055425298165612561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65201316703616865443741707 97801975055425298165612561)
    ·
      refine ⟨73351481291568973624209421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97801975055425298165612561 73351481291568973624209421)
      ·
        refine ⟨27506805484338365109078533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73351481291568973624209421 27506805484338365109078533)
        ·
          refine ⟨5157526028313443457952225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27506805484338365109078533 5157526028313443457952225)
          ·
            refine ⟨3868144521235082593464169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5157526028313443457952225 3868144521235082593464169)
            ·
              refine ⟨2901108390926311945098127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868144521235082593464169 2901108390926311945098127)
              ·
                refine ⟨4351662586389467917647191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901108390926311945098127 4351662586389467917647191)
                ·
                  refine ⟨6527493879584201876470787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351662586389467917647191 6527493879584201876470787)
                  ·
                    refine ⟨9791240819376302814706181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6527493879584201876470787 9791240819376302814706181)
                    ·
                      refine ⟨1835857653633056777757409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9791240819376302814706181 1835857653633056777757409)
                      ·
                        rfl

theorem cell23_3575320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3575320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575320 prefixEnd_3575320 := by exact prefixLift 3575320
  have htrace : WordTrace (prefixWord ++ tailWord_3575320) baseStart_3575320 baseEnd_3575320 := by
    simpa [prefixWord, tailWord_3575320, baseEnd_3575320] using wordTrace_append hprefix tailTrace_3575320
  have hstable : (prefixWord ++ tailWord_3575320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575320).length < 2 ^ (prefixWord ++ tailWord_3575320).sum := by decide
  have hdescent : baseEnd_3575320 < baseStart_3575320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575350 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3575350 : Nat := 118140960795 + 3575350 * 2 ^ 59
def prefixEnd_3575350 : Nat := 4983230072969 + 3 ^ 40 * 3575350 * 2
def baseEnd_3575350 : Nat := 1835873058052691660382271

theorem tailTrace_3575350 : CollatzResearch.WordTrace tailWord_3575350 prefixEnd_3575350 1835873058052691660382271 := by
  unfold tailWord_3575350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150232974820315375692219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86935818398083364007383669 8150232974820315375692219)
  ·
    refine ⟨12225349462230473063538329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150232974820315375692219 12225349462230473063538329)
    ·
      refine ⟨9169012096672854797653747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12225349462230473063538329 9169012096672854797653747)
      ·
        refine ⟨13753518145009282196480621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9169012096672854797653747 13753518145009282196480621)
        ·
          refine ⟨5157569304378480823680233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13753518145009282196480621 5157569304378480823680233)
          ·
            refine ⟨3868176978283860617760175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5157569304378480823680233 3868176978283860617760175)
            ·
              refine ⟨5802265467425790926640263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868176978283860617760175 5802265467425790926640263)
              ·
                refine ⟨8703398201138686389960395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802265467425790926640263 8703398201138686389960395)
                ·
                  refine ⟨13055097301708029584940593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703398201138686389960395 13055097301708029584940593)
                  ·
                    refine ⟨9791322976281022188705445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13055097301708029584940593 9791322976281022188705445)
                    ·
                      refine ⟨1835873058052691660382271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9791322976281022188705445 1835873058052691660382271)
                      ·
                        rfl

theorem cell23_3575350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3575350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575350 prefixEnd_3575350 := by exact prefixLift 3575350
  have htrace : WordTrace (prefixWord ++ tailWord_3575350) baseStart_3575350 baseEnd_3575350 := by
    simpa [prefixWord, tailWord_3575350, baseEnd_3575350] using wordTrace_append hprefix tailTrace_3575350
  have hstable : (prefixWord ++ tailWord_3575350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575350).length < 2 ^ (prefixWord ++ tailWord_3575350).sum := by decide
  have hdescent : baseEnd_3575350 < baseStart_3575350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575353 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3575353 : Nat := 118140960795 + 3575353 * 2 ^ 59
def prefixEnd_3575353 : Nat := 4983230072969 + 3 ^ 40 * 3575353 * 2
def baseEnd_3575353 : Nat := 1835874598494655148644757

theorem tailTrace_3575353 : CollatzResearch.WordTrace tailWord_3575353 prefixEnd_3575353 1835874598494655148644757 := by
  unfold tailWord_3575353
  simp only [CollatzResearch.WordTrace]
  refine ⟨130403837016114177523434713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86935891344076118348956475 130403837016114177523434713)
  ·
    refine ⟨97802877762085633142576035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130403837016114177523434713 97802877762085633142576035)
    ·
      refine ⟨146704316643128449713864053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97802877762085633142576035 146704316643128449713864053)
      ·
        refine ⟨13753529685293292160674755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146704316643128449713864053 13753529685293292160674755)
        ·
          refine ⟨20630294527939938241012133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13753529685293292160674755 20630294527939938241012133)
          ·
            refine ⟨3868180223988738420189775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20630294527939938241012133 3868180223988738420189775)
            ·
              refine ⟨5802270335983107630284663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868180223988738420189775 5802270335983107630284663)
              ·
                refine ⟨8703405503974661445426995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802270335983107630284663 8703405503974661445426995)
                ·
                  refine ⟨13055108255961992168140493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703405503974661445426995 13055108255961992168140493)
                  ·
                    refine ⟨4895665595985747063052685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13055108255961992168140493 4895665595985747063052685)
                    ·
                      refine ⟨1835874598494655148644757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895665595985747063052685 1835874598494655148644757)
                      ·
                        rfl

theorem cell23_3575353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3575353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575353 prefixEnd_3575353 := by exact prefixLift 3575353
  have htrace : WordTrace (prefixWord ++ tailWord_3575353) baseStart_3575353 baseEnd_3575353 := by
    simpa [prefixWord, tailWord_3575353, baseEnd_3575353] using wordTrace_append hprefix tailTrace_3575353
  have hstable : (prefixWord ++ tailWord_3575353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575353).length < 2 ^ (prefixWord ++ tailWord_3575353).sum := by decide
  have hdescent : baseEnd_3575353 < baseStart_3575353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575376 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2]
def baseStart_3575376 : Nat := 118140960795 + 3575376 * 2 ^ 59
def prefixEnd_3575376 : Nat := 4983230072969 + 3 ^ 40 * 3575376 * 2
def baseEnd_3575376 : Nat := 1835886408549708558657151

theorem tailTrace_3575376 : CollatzResearch.WordTrace tailWord_3575376 prefixEnd_3575376 1835886408549708558657151 := by
  unfold tailWord_3575376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65202337947515426225760991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86936450596687234967681321 65202337947515426225760991)
  ·
    refine ⟨97803506921273139338641487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65202337947515426225760991 97803506921273139338641487)
    ·
      refine ⟨146705260381909709007962231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97803506921273139338641487 146705260381909709007962231)
      ·
        refine ⟨220057890572864563511943347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146705260381909709007962231 220057890572864563511943347)
        ·
          refine ⟨330086835859296845267915021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220057890572864563511943347 330086835859296845267915021)
          ·
            refine ⟨123782563447236316975468133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330086835859296845267915021 123782563447236316975468133)
            ·
              refine ⟨23209230646356809432900275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123782563447236316975468133 23209230646356809432900275)
              ·
                refine ⟨34813845969535214149350413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23209230646356809432900275 34813845969535214149350413)
                ·
                  refine ⟨13055192238575705306006405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34813845969535214149350413 13055192238575705306006405)
                  ·
                    refine ⟨2447848544732944744876201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13055192238575705306006405 2447848544732944744876201)
                    ·
                      refine ⟨1835886408549708558657151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447848544732944744876201 1835886408549708558657151)
                      ·
                        rfl

theorem cell23_3575376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2].length) (baseStart_3575376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575376 prefixEnd_3575376 := by exact prefixLift 3575376
  have htrace : WordTrace (prefixWord ++ tailWord_3575376) baseStart_3575376 baseEnd_3575376 := by
    simpa [prefixWord, tailWord_3575376, baseEnd_3575376] using wordTrace_append hprefix tailTrace_3575376
  have hstable : (prefixWord ++ tailWord_3575376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575376).length < 2 ^ (prefixWord ++ tailWord_3575376).sum := by decide
  have hdescent : baseEnd_3575376 < baseStart_3575376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575379 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3]
def baseStart_3575379 : Nat := 118140960795 + 3575379 * 2 ^ 59
def prefixEnd_3575379 : Nat := 4983230072969 + 3 ^ 40 * 3575379 * 2
def baseEnd_3575379 : Nat := 1835887948991672046919637

theorem tailTrace_3575379 : CollatzResearch.WordTrace tailWord_3575379 prefixEnd_3575379 1835887948991672046919637 := by
  unfold tailWord_3575379
  simp only [CollatzResearch.WordTrace]
  refine ⟨130404785314019983963881191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86936523542679989309254127 130404785314019983963881191)
  ·
    refine ⟨195607177971029975945821787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130404785314019983963881191 195607177971029975945821787)
    ·
      refine ⟨293410766956544963918732681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195607177971029975945821787 293410766956544963918732681)
      ·
        refine ⟨220058075217408722939049511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293410766956544963918732681 220058075217408722939049511)
        ·
          refine ⟨330087112826113084408574267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220058075217408722939049511 330087112826113084408574267)
          ·
            refine ⟨495130669239169626612861401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330087112826113084408574267 495130669239169626612861401)
            ·
              refine ⟨371348001929377219959646051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495130669239169626612861401 371348001929377219959646051)
              ·
                refine ⟨557022002894065829939469077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371348001929377219959646051 557022002894065829939469077)
                ·
                  refine ⟨26110406385659335778412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557022002894065829939469077 26110406385659335778412613)
                  ·
                    refine ⟨4895701197311125458452365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26110406385659335778412613 4895701197311125458452365)
                    ·
                      refine ⟨1835887948991672046919637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4895701197311125458452365 1835887948991672046919637)
                      ·
                        rfl

theorem cell23_3575379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_3575379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575379 prefixEnd_3575379 := by exact prefixLift 3575379
  have htrace : WordTrace (prefixWord ++ tailWord_3575379) baseStart_3575379 baseEnd_3575379 := by
    simpa [prefixWord, tailWord_3575379, baseEnd_3575379] using wordTrace_append hprefix tailTrace_3575379
  have hstable : (prefixWord ++ tailWord_3575379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575379).length < 2 ^ (prefixWord ++ tailWord_3575379).sum := by decide
  have hdescent : baseEnd_3575379 < baseStart_3575379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575393 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_3575393 : Nat := 118140960795 + 3575393 * 2 ^ 59
def prefixEnd_3575393 : Nat := 4983230072969 + 3 ^ 40 * 3575393 * 2
def baseEnd_3575393 : Nat := 1835895137720834992144573

theorem tailTrace_3575393 : CollatzResearch.WordTrace tailWord_3575393 prefixEnd_3575393 1835895137720834992144573 := by
  unfold tailWord_3575393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130405295935969264354890833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86936863957312842903260555 130405295935969264354890833)
  ·
    refine ⟨97803971951976948266168125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130405295935969264354890833 97803971951976948266168125)
    ·
      refine ⟨36676489481991355599813047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97803971951976948266168125 36676489481991355599813047)
      ·
        refine ⟨55014734222987033399719571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36676489481991355599813047 55014734222987033399719571)
        ·
          refine ⟨82522101334480550099579357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55014734222987033399719571 82522101334480550099579357)
          ·
            refine ⟨30945788000430206287342259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82522101334480550099579357 30945788000430206287342259)
            ·
              refine ⟨46418682000645309431013389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30945788000430206287342259 46418682000645309431013389)
              ·
                refine ⟨17407005750241991036630021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46418682000645309431013389 17407005750241991036630021)
                ·
                  refine ⟨3263813578170373319368129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17407005750241991036630021 3263813578170373319368129)
                  ·
                    refine ⟨2447860183627779989526097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263813578170373319368129 2447860183627779989526097)
                    ·
                      refine ⟨1835895137720834992144573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447860183627779989526097 1835895137720834992144573)
                      ·
                        rfl

theorem cell23_3575393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_3575393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575393 prefixEnd_3575393 := by exact prefixLift 3575393
  have htrace : WordTrace (prefixWord ++ tailWord_3575393) baseStart_3575393 baseEnd_3575393 := by
    simpa [prefixWord, tailWord_3575393, baseEnd_3575393] using wordTrace_append hprefix tailTrace_3575393
  have hstable : (prefixWord ++ tailWord_3575393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575393).length < 2 ^ (prefixWord ++ tailWord_3575393).sum := by decide
  have hdescent : baseEnd_3575393 < baseStart_3575393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575444 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3575444 : Nat := 118140960795 + 3575444 * 2 ^ 59
def prefixEnd_3575444 : Nat := 4983230072969 + 3 ^ 40 * 3575444 * 2
def baseEnd_3575444 : Nat := 1835921325234214292606839

theorem tailTrace_3575444 : CollatzResearch.WordTrace tailWord_3575444 prefixEnd_3575444 1835921325234214292606839 := by
  unfold tailWord_3575444
  simp only [CollatzResearch.WordTrace]
  refine ⟨65203578029392250032498693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86938104039189666709998257 65203578029392250032498693)
  ·
    refine ⟨12225670880511046881093505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65203578029392250032498693 12225670880511046881093505)
    ·
      refine ⟨9169253160383285160820129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12225670880511046881093505 9169253160383285160820129)
      ·
        refine ⟨6876939870287463870615097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9169253160383285160820129 6876939870287463870615097)
        ·
          refine ⟨5157704902715597902961323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6876939870287463870615097 5157704902715597902961323)
          ·
            refine ⟨7736557354073396854441985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157704902715597902961323 7736557354073396854441985)
            ·
              refine ⟨5802418015555047640831489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7736557354073396854441985 5802418015555047640831489)
              ·
                refine ⟨4351813511666285730623617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802418015555047640831489 4351813511666285730623617)
                ·
                  refine ⟨3263860133749714297967713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351813511666285730623617 3263860133749714297967713)
                  ·
                    refine ⟨2447895100312285723475785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263860133749714297967713 2447895100312285723475785)
                    ·
                      refine ⟨1835921325234214292606839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447895100312285723475785 1835921325234214292606839)
                      ·
                        rfl

theorem cell23_3575444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3575444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575444 prefixEnd_3575444 := by exact prefixLift 3575444
  have htrace : WordTrace (prefixWord ++ tailWord_3575444) baseStart_3575444 baseEnd_3575444 := by
    simpa [prefixWord, tailWord_3575444, baseEnd_3575444] using wordTrace_append hprefix tailTrace_3575444
  have hstable : (prefixWord ++ tailWord_3575444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575444).length < 2 ^ (prefixWord ++ tailWord_3575444).sum := by decide
  have hdescent : baseEnd_3575444 < baseStart_3575444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575456 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3575456 : Nat := 118140960795 + 3575456 * 2 ^ 59
def prefixEnd_3575456 : Nat := 4983230072969 + 3 ^ 40 * 3575456 * 2
def baseEnd_3575456 : Nat := 1835927487002068245656783

theorem tailTrace_3575456 : CollatzResearch.WordTrace tailWord_3575456 prefixEnd_3575456 1835927487002068245656783 := by
  unfold tailWord_3575456
  simp only [CollatzResearch.WordTrace]
  refine ⟨65203796867370513057217111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86938395823160684076289481 65203796867370513057217111)
  ·
    refine ⟨97805695301055769585825667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65203796867370513057217111 97805695301055769585825667)
    ·
      refine ⟨146708542951583654378738501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97805695301055769585825667 146708542951583654378738501)
      ·
        refine ⟨27507851803421935196013469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146708542951583654378738501 27507851803421935196013469)
        ·
          refine ⟨10315444426283225698505051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27507851803421935196013469 10315444426283225698505051)
          ·
            refine ⟨15473166639424838547757577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315444426283225698505051 15473166639424838547757577)
            ·
              refine ⟨11604874979568628910818183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15473166639424838547757577 11604874979568628910818183)
              ·
                refine ⟨17407312469352943366227275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604874979568628910818183 17407312469352943366227275)
                ·
                  refine ⟨26110968704029415049340913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17407312469352943366227275 26110968704029415049340913)
                  ·
                    refine ⟨19583226528022061287005685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26110968704029415049340913 19583226528022061287005685)
                    ·
                      refine ⟨1835927487002068245656783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19583226528022061287005685 1835927487002068245656783)
                      ·
                        rfl

theorem cell23_3575456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3575456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575456 prefixEnd_3575456 := by exact prefixLift 3575456
  have htrace : WordTrace (prefixWord ++ tailWord_3575456) baseStart_3575456 baseEnd_3575456 := by
    simpa [prefixWord, tailWord_3575456, baseEnd_3575456] using wordTrace_append hprefix tailTrace_3575456
  have hstable : (prefixWord ++ tailWord_3575456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575456).length < 2 ^ (prefixWord ++ tailWord_3575456).sum := by decide
  have hdescent : baseEnd_3575456 < baseStart_3575456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575540 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3575540 : Nat := 118140960795 + 3575540 * 2 ^ 59
def prefixEnd_3575540 : Nat := 4983230072969 + 3 ^ 40 * 3575540 * 2
def baseEnd_3575540 : Nat := 203996735486338435222933

theorem tailTrace_3575540 : CollatzResearch.WordTrace tailWord_3575540 prefixEnd_3575540 203996735486338435222933 := by
  unfold tailWord_3575540
  simp only [CollatzResearch.WordTrace]
  refine ⟨65205328733218354230246037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86940438310957805640328049 65205328733218354230246037)
  ·
    refine ⟨3056499784369610354542783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65205328733218354230246037 3056499784369610354542783)
    ·
      refine ⟨4584749676554415531814175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056499784369610354542783 4584749676554415531814175)
      ·
        refine ⟨6877124514831623297721263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584749676554415531814175 6877124514831623297721263)
        ·
          refine ⟨10315686772247434946581895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877124514831623297721263 10315686772247434946581895)
          ·
            refine ⟨15473530158371152419872843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315686772247434946581895 15473530158371152419872843)
            ·
              refine ⟨23210295237556728629809265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15473530158371152419872843 23210295237556728629809265)
              ·
                refine ⟨17407721428167546472356949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23210295237556728629809265 17407721428167546472356949)
                ·
                  refine ⟨203996735486338435222933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17407721428167546472356949 203996735486338435222933)
                  ·
                    rfl

theorem cell23_3575540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3575540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575540 prefixEnd_3575540 := by exact prefixLift 3575540
  have htrace : WordTrace (prefixWord ++ tailWord_3575540) baseStart_3575540 baseEnd_3575540 := by
    simpa [prefixWord, tailWord_3575540, baseEnd_3575540] using wordTrace_append hprefix tailTrace_3575540
  have hstable : (prefixWord ++ tailWord_3575540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575540).length < 2 ^ (prefixWord ++ tailWord_3575540).sum := by decide
  have hdescent : baseEnd_3575540 < baseStart_3575540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575543 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_3575543 : Nat := 118140960795 + 3575543 * 2 ^ 59
def prefixEnd_3575543 : Nat := 4983230072969 + 3 ^ 40 * 3575543 * 2
def baseEnd_3575543 : Nat := 1835972159819009405268883

theorem tailTrace_3575543 : CollatzResearch.WordTrace tailWord_3575543 prefixEnd_3575543 1835972159819009405268883 := by
  unfold tailWord_3575543
  simp only [CollatzResearch.WordTrace]
  refine ⟨130410766885425839972851283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86940511256950559981900855 130410766885425839972851283)
  ·
    refine ⟨195616150328138759959276925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130410766885425839972851283 195616150328138759959276925)
    ·
      refine ⟨73356056373052034984728847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195616150328138759959276925 73356056373052034984728847)
      ·
        refine ⟨110034084559578052477093271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73356056373052034984728847 110034084559578052477093271)
        ·
          refine ⟨165051126839367078715639907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110034084559578052477093271 165051126839367078715639907)
          ·
            refine ⟨247576690259050618073459861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165051126839367078715639907 247576690259050618073459861)
            ·
              refine ⟨11605157355892997722193431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247576690259050618073459861 11605157355892997722193431)
              ·
                refine ⟨17407736033839496583290147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605157355892997722193431 17407736033839496583290147)
                ·
                  refine ⟨26111604050759244874935221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17407736033839496583290147 26111604050759244874935221)
                  ·
                    refine ⟨2447962879758679207025177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26111604050759244874935221 2447962879758679207025177)
                    ·
                      refine ⟨1835972159819009405268883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447962879758679207025177 1835972159819009405268883)
                      ·
                        rfl

theorem cell23_3575543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_3575543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575543 prefixEnd_3575543 := by exact prefixLift 3575543
  have htrace : WordTrace (prefixWord ++ tailWord_3575543) baseStart_3575543 baseEnd_3575543 := by
    simpa [prefixWord, tailWord_3575543, baseEnd_3575543] using wordTrace_append hprefix tailTrace_3575543
  have hstable : (prefixWord ++ tailWord_3575543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575543).length < 2 ^ (prefixWord ++ tailWord_3575543).sum := by decide
  have hdescent : baseEnd_3575543 < baseStart_3575543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575553 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3575553 : Nat := 118140960795 + 3575553 * 2 ^ 59
def prefixEnd_3575553 : Nat := 4983230072969 + 3 ^ 40 * 3575553 * 2
def baseEnd_3575553 : Nat := 611992431541851455381279

theorem tailTrace_3575553 : CollatzResearch.WordTrace tailWord_3575553 prefixEnd_3575553 611992431541851455381279 := by
  unfold tailWord_3575553
  simp only [CollatzResearch.WordTrace]
  refine ⟨130411131615389611680715313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86940754410259741120476875 130411131615389611680715313)
  ·
    refine ⟨97808348711542208760536485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130411131615389611680715313 97808348711542208760536485)
    ·
      refine ⟨18339065383414164142600591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97808348711542208760536485 18339065383414164142600591)
      ·
        refine ⟨27508598075121246213900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18339065383414164142600591 27508598075121246213900887)
        ·
          refine ⟨41262897112681869320851331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27508598075121246213900887 41262897112681869320851331)
          ·
            refine ⟨61894345669022803981276997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41262897112681869320851331 61894345669022803981276997)
            ·
              refine ⟨11605189812941775746489437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61894345669022803981276997 11605189812941775746489437)
              ·
                refine ⟨4351946179853165904933539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11605189812941775746489437 4351946179853165904933539)
                ·
                  refine ⟨6527919269779748857400309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351946179853165904933539 6527919269779748857400309)
                  ·
                    refine ⟨611992431541851455381279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6527919269779748857400309 611992431541851455381279)
                    ·
                      rfl

theorem cell23_3575553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3575553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575553 prefixEnd_3575553 := by exact prefixLift 3575553
  have htrace : WordTrace (prefixWord ++ tailWord_3575553) baseStart_3575553 baseEnd_3575553 := by
    simpa [prefixWord, tailWord_3575553, baseEnd_3575553] using wordTrace_append hprefix tailTrace_3575553
  have hstable : (prefixWord ++ tailWord_3575553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575553).length < 2 ^ (prefixWord ++ tailWord_3575553).sum := by decide
  have hdescent : baseEnd_3575553 < baseStart_3575553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575560 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_3575560 : Nat := 118140960795 + 3575560 * 2 ^ 59
def prefixEnd_3575560 : Nat := 4983230072969 + 3 ^ 40 * 3575560 * 2
def baseEnd_3575560 : Nat := 1835980888990135838756305

theorem tailTrace_3575560 : CollatzResearch.WordTrace tailWord_3575560 prefixEnd_3575560 1835980888990135838756305 := by
  unfold tailWord_3575560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65205693463182125938110067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86940924617576167917480089 65205693463182125938110067)
  ·
    refine ⟨97808540194773188907165101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65205693463182125938110067 97808540194773188907165101)
    ·
      refine ⟨36678202573039945840186913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97808540194773188907165101 36678202573039945840186913)
      ·
        refine ⟨27508651929779959380140185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36678202573039945840186913 27508651929779959380140185)
        ·
          refine ⟨20631488947334969535105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27508651929779959380140185 20631488947334969535105139)
          ·
            refine ⟨30947233421002454302657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20631488947334969535105139 30947233421002454302657709)
            ·
              refine ⟨11605212532875920363496641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30947233421002454302657709 11605212532875920363496641)
              ·
                refine ⟨8703909399656940272622481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11605212532875920363496641 8703909399656940272622481)
                ·
                  refine ⟨6527932049742705204466861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703909399656940272622481 6527932049742705204466861)
                  ·
                    refine ⟨2447974518653514451675073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6527932049742705204466861 2447974518653514451675073)
                    ·
                      refine ⟨1835980888990135838756305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2447974518653514451675073 1835980888990135838756305)
                      ·
                        rfl

theorem cell23_3575560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_3575560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575560 prefixEnd_3575560 := by exact prefixLift 3575560
  have htrace : WordTrace (prefixWord ++ tailWord_3575560) baseStart_3575560 baseEnd_3575560 := by
    simpa [prefixWord, tailWord_3575560, baseEnd_3575560] using wordTrace_append hprefix tailTrace_3575560
  have hstable : (prefixWord ++ tailWord_3575560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575560).length < 2 ^ (prefixWord ++ tailWord_3575560).sum := by decide
  have hdescent : baseEnd_3575560 < baseStart_3575560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575596 : List Nat := [2, 2, 1, 1, 1, 5, 2, 9]
def baseStart_3575596 : Nat := 118140960795 + 3575596 * 2 ^ 59
def prefixEnd_3575596 : Nat := 4983230072969 + 3 ^ 40 * 3575596 * 2
def baseEnd_3575596 : Nat := 67999976825692507329857

theorem tailTrace_3575596 : CollatzResearch.WordTrace tailWord_3575596 prefixEnd_3575596 67999976825692507329857 := by
  unfold tailWord_3575596
  simp only [CollatzResearch.WordTrace]
  refine ⟨65206349977116915012265321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86941799969489220016353761 65206349977116915012265321)
  ·
    refine ⟨48904762482837686259198991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65206349977116915012265321 48904762482837686259198991)
    ·
      refine ⟨73357143724256529388798487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48904762482837686259198991 73357143724256529388798487)
      ·
        refine ⟨110035715586384794083197731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73357143724256529388798487 110035715586384794083197731)
        ·
          refine ⟨165053573379577191124796597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110035715586384794083197731 165053573379577191124796597)
          ·
            refine ⟨15473772504335361667949681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165053573379577191124796597 15473772504335361667949681)
            ·
              refine ⟨11605329378251521250962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15473772504335361667949681 11605329378251521250962261)
              ·
                refine ⟨67999976825692507329857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11605329378251521250962261 67999976825692507329857)
                ·
                  rfl

theorem cell23_3575596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 9].length) (baseStart_3575596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575596 prefixEnd_3575596 := by exact prefixLift 3575596
  have htrace : WordTrace (prefixWord ++ tailWord_3575596) baseStart_3575596 baseEnd_3575596 := by
    simpa [prefixWord, tailWord_3575596, baseEnd_3575596] using wordTrace_append hprefix tailTrace_3575596
  have hstable : (prefixWord ++ tailWord_3575596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575596).length < 2 ^ (prefixWord ++ tailWord_3575596).sum := by decide
  have hdescent : baseEnd_3575596 < baseStart_3575596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575610 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_3575610 : Nat := 118140960795 + 3575610 * 2 ^ 59
def prefixEnd_3575610 : Nat := 4983230072969 + 3 ^ 40 * 3575610 * 2
def baseEnd_3575610 : Nat := 1836006563022860643131075

theorem tailTrace_3575610 : CollatzResearch.WordTrace tailWord_3575610 prefixEnd_3575610 1836006563022860643131075 := by
  unfold tailWord_3575610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32603302644045777603885071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86942140384122073610360189 32603302644045777603885071)
  ·
    refine ⟨48904953966068666405827607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32603302644045777603885071 48904953966068666405827607)
    ·
      refine ⟨73357430949102999608741411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48904953966068666405827607 73357430949102999608741411)
      ·
        refine ⟨110036146423654499413112117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73357430949102999608741411 110036146423654499413112117)
        ·
          refine ⟨10315888727217609319979261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110036146423654499413112117 10315888727217609319979261)
          ·
            refine ⟨3868458272706603494992223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10315888727217609319979261 3868458272706603494992223)
            ·
              refine ⟨5802687409059905242488335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868458272706603494992223 5802687409059905242488335)
              ·
                refine ⟨8704031113589857863732503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802687409059905242488335 8704031113589857863732503)
                ·
                  refine ⟨13056046670384786795598755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8704031113589857863732503 13056046670384786795598755)
                  ·
                    refine ⟨19584070005577180193398133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13056046670384786795598755 19584070005577180193398133)
                    ·
                      refine ⟨1836006563022860643131075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19584070005577180193398133 1836006563022860643131075)
                      ·
                        rfl

theorem cell23_3575610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_3575610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575610 prefixEnd_3575610 := by exact prefixLift 3575610
  have htrace : WordTrace (prefixWord ++ tailWord_3575610) baseStart_3575610 baseEnd_3575610 := by
    simpa [prefixWord, tailWord_3575610, baseEnd_3575610] using wordTrace_append hprefix tailTrace_3575610
  have hstable : (prefixWord ++ tailWord_3575610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575610).length < 2 ^ (prefixWord ++ tailWord_3575610).sum := by decide
  have hdescent : baseEnd_3575610 < baseStart_3575610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575624 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_3575624 : Nat := 118140960795 + 3575624 * 2 ^ 59
def prefixEnd_3575624 : Nat := 4983230072969 + 3 ^ 40 * 3575624 * 2
def baseEnd_3575624 : Nat := 1836013751752023588356011

theorem tailTrace_3575624 : CollatzResearch.WordTrace tailWord_3575624 prefixEnd_3575624 1836013751752023588356011 := by
  unfold tailWord_3575624
  simp only [CollatzResearch.WordTrace]
  refine ⟨65206860599066195403274963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86942480798754927204366617 65206860599066195403274963)
  ·
    refine ⟨97810290898599293104912445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65206860599066195403274963 97810290898599293104912445)
    ·
      refine ⟨36678859086974734914342167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97810290898599293104912445 36678859086974734914342167)
      ·
        refine ⟨55018288630462102371513251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36678859086974734914342167 55018288630462102371513251)
        ·
          refine ⟨82527432945693153557269877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55018288630462102371513251 82527432945693153557269877)
          ·
            refine ⟨7736946838658733145994051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82527432945693153557269877 7736946838658733145994051)
            ·
              refine ⟨11605420257988099718991077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736946838658733145994051 11605420257988099718991077)
              ·
                refine ⟨2176016298372768697310827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11605420257988099718991077 2176016298372768697310827)
                ·
                  refine ⟨3264024447559153045966241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176016298372768697310827 3264024447559153045966241)
                  ·
                    refine ⟨2448018335669364784474681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264024447559153045966241 2448018335669364784474681)
                    ·
                      refine ⟨1836013751752023588356011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448018335669364784474681 1836013751752023588356011)
                      ·
                        rfl

theorem cell23_3575624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_3575624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575624 prefixEnd_3575624 := by exact prefixLift 3575624
  have htrace : WordTrace (prefixWord ++ tailWord_3575624) baseStart_3575624 baseEnd_3575624 := by
    simpa [prefixWord, tailWord_3575624, baseEnd_3575624] using wordTrace_append hprefix tailTrace_3575624
  have hstable : (prefixWord ++ tailWord_3575624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575624).length < 2 ^ (prefixWord ++ tailWord_3575624).sum := by decide
  have hdescent : baseEnd_3575624 < baseStart_3575624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575626 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3575626 : Nat := 118140960795 + 3575626 * 2 ^ 59
def prefixEnd_3575626 : Nat := 4983230072969 + 3 ^ 40 * 3575626 * 2
def baseEnd_3575626 : Nat := 612004926237777526843667

theorem tailTrace_3575626 : CollatzResearch.WordTrace tailWord_3575626 prefixEnd_3575626 612004926237777526843667 := by
  unfold tailWord_3575626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32603448536031286287030683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86942529429416763432081821 32603448536031286287030683)
  ·
    refine ⟨48905172804046929430546025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32603448536031286287030683 48905172804046929430546025)
    ·
      refine ⟨36678879603035197072909519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48905172804046929430546025 36678879603035197072909519)
      ·
        refine ⟨55018319404552795609364279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36678879603035197072909519 55018319404552795609364279)
        ·
          refine ⟨82527479106829193414046419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55018319404552795609364279 82527479106829193414046419)
          ·
            refine ⟨123791218660243790121069629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82527479106829193414046419 123791218660243790121069629)
            ·
              refine ⟨46421706997591421295401111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123791218660243790121069629 46421706997591421295401111)
              ·
                refine ⟨69632560496387131943101667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46421706997591421295401111 69632560496387131943101667)
                ·
                  refine ⟨104448840744580697914652501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69632560496387131943101667 104448840744580697914652501)
                  ·
                    refine ⟨612004926237777526843667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 104448840744580697914652501 612004926237777526843667)
                    ·
                      rfl

theorem cell23_3575626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3575626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575626 prefixEnd_3575626 := by exact prefixLift 3575626
  have htrace : WordTrace (prefixWord ++ tailWord_3575626) baseStart_3575626 baseEnd_3575626 := by
    simpa [prefixWord, tailWord_3575626, baseEnd_3575626] using wordTrace_append hprefix tailTrace_3575626
  have hstable : (prefixWord ++ tailWord_3575626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575626).length < 2 ^ (prefixWord ++ tailWord_3575626).sum := by decide
  have hdescent : baseEnd_3575626 < baseStart_3575626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575658 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3575658 : Nat := 118140960795 + 3575658 * 2 ^ 59
def prefixEnd_3575658 : Nat := 4983230072969 + 3 ^ 40 * 3575658 * 2
def baseEnd_3575658 : Nat := 1836031210094276455330855

theorem tailTrace_3575658 : CollatzResearch.WordTrace tailWord_3575658 prefixEnd_3575658 1836031210094276455330855 := by
  unfold tailWord_3575658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32603740320002303653321907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86943307520006143075525085 32603740320002303653321907)
  ·
    refine ⟨48905610480003455479982861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32603740320002303653321907 48905610480003455479982861)
    ·
      refine ⟨18339603930001295804993573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48905610480003455479982861 18339603930001295804993573)
      ·
        refine ⟨3438675736875242963436295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18339603930001295804993573 3438675736875242963436295)
        ·
          refine ⟨5158013605312864445154443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438675736875242963436295 5158013605312864445154443)
          ·
            refine ⟨7737020407969296667731665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158013605312864445154443 7737020407969296667731665)
            ·
              refine ⟨5802765305976972500798749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7737020407969296667731665 5802765305976972500798749)
              ·
                refine ⟨2176036989741364687799531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5802765305976972500798749 2176036989741364687799531)
                ·
                  refine ⟨3264055484612047031699297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176036989741364687799531 3264055484612047031699297)
                  ·
                    refine ⟨2448041613459035273774473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264055484612047031699297 2448041613459035273774473)
                    ·
                      refine ⟨1836031210094276455330855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448041613459035273774473 1836031210094276455330855)
                      ·
                        rfl

theorem cell23_3575658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3575658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575658 prefixEnd_3575658 := by exact prefixLift 3575658
  have htrace : WordTrace (prefixWord ++ tailWord_3575658) baseStart_3575658 baseEnd_3575658 := by
    simpa [prefixWord, tailWord_3575658, baseEnd_3575658] using wordTrace_append hprefix tailTrace_3575658
  have hstable : (prefixWord ++ tailWord_3575658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575658).length < 2 ^ (prefixWord ++ tailWord_3575658).sum := by decide
  have hdescent : baseEnd_3575658 < baseStart_3575658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575697 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_3575697 : Nat := 118140960795 + 3575697 * 2 ^ 59
def prefixEnd_3575697 : Nat := 4983230072969 + 3 ^ 40 * 3575697 * 2
def baseEnd_3575697 : Nat := 1836051235839801802743175

theorem tailTrace_3575697 : CollatzResearch.WordTrace tailWord_3575697 prefixEnd_3575697 1836051235839801802743175 := by
  unfold tailWord_3575697
  simp only [CollatzResearch.WordTrace]
  refine ⟨130416383726867924273957345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86944255817911949515971563 130416383726867924273957345)
  ·
    refine ⟨97812287795150943205468009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130416383726867924273957345 97812287795150943205468009)
    ·
      refine ⟨73359215846363207404101007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97812287795150943205468009 73359215846363207404101007)
      ·
        refine ⟨110038823769544811106151511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73359215846363207404101007 110038823769544811106151511)
        ·
          refine ⟨165058235654317216659227267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110038823769544811106151511 165058235654317216659227267)
          ·
            refine ⟨247587353481475824988840901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165058235654317216659227267 247587353481475824988840901)
            ·
              refine ⟨46422628777776717185407669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247587353481475824988840901 46422628777776717185407669)
              ·
                refine ⟨4352121447916567236131969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46422628777776717185407669 4352121447916567236131969)
                ·
                  refine ⟨3264091085937425427098977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352121447916567236131969 3264091085937425427098977)
                  ·
                    refine ⟨2448068314453069070324233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264091085937425427098977 2448068314453069070324233)
                    ·
                      refine ⟨1836051235839801802743175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448068314453069070324233 1836051235839801802743175)
                      ·
                        rfl

theorem cell23_3575697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_3575697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575697 prefixEnd_3575697 := by exact prefixLift 3575697
  have htrace : WordTrace (prefixWord ++ tailWord_3575697) baseStart_3575697 baseEnd_3575697 := by
    simpa [prefixWord, tailWord_3575697, baseEnd_3575697] using wordTrace_append hprefix tailTrace_3575697
  have hstable : (prefixWord ++ tailWord_3575697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575697).length < 2 ^ (prefixWord ++ tailWord_3575697).sum := by decide
  have hdescent : baseEnd_3575697 < baseStart_3575697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575703 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 7]
def baseStart_3575703 : Nat := 118140960795 + 3575703 * 2 ^ 59
def prefixEnd_3575703 : Nat := 4983230072969 + 3 ^ 40 * 3575703 * 2
def baseEnd_3575703 : Nat := 204006035191525419918683

theorem tailTrace_3575703 : CollatzResearch.WordTrace tailWord_3575703 prefixEnd_3575703 204006035191525419918683 := by
  unfold tailWord_3575703
  simp only [CollatzResearch.WordTrace]
  refine ⟨130416602564846187298675763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86944401709897458199117175 130416602564846187298675763)
  ·
    refine ⟨195624903847269280948013645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130416602564846187298675763 195624903847269280948013645)
    ·
      refine ⟨73359338942725980355505117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195624903847269280948013645 73359338942725980355505117)
      ·
        refine ⟨27509752103522242633314419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73359338942725980355505117 27509752103522242633314419)
        ·
          refine ⟨41264628155283363949971629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27509752103522242633314419 41264628155283363949971629)
          ·
            refine ⟨15474235558231261481239361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41264628155283363949971629 15474235558231261481239361)
            ·
              refine ⟨11605676668673446110929521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15474235558231261481239361 11605676668673446110929521)
              ·
                refine ⟨8704257501505084583197141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11605676668673446110929521 8704257501505084583197141)
                ·
                  refine ⟨204006035191525419918683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8704257501505084583197141 204006035191525419918683)
                  ·
                    rfl

theorem cell23_3575703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 7].length) (baseStart_3575703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575703 prefixEnd_3575703 := by exact prefixLift 3575703
  have htrace : WordTrace (prefixWord ++ tailWord_3575703) baseStart_3575703 baseEnd_3575703 := by
    simpa [prefixWord, tailWord_3575703, baseEnd_3575703] using wordTrace_append hprefix tailTrace_3575703
  have hstable : (prefixWord ++ tailWord_3575703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575703).length < 2 ^ (prefixWord ++ tailWord_3575703).sum := by decide
  have hdescent : baseEnd_3575703 < baseStart_3575703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575737 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 5]
def baseStart_3575737 : Nat := 118140960795 + 3575737 * 2 ^ 59
def prefixEnd_3575737 : Nat := 4983230072969 + 3 ^ 40 * 3575737 * 2
def baseEnd_3575737 : Nat := 204007975007331294026999

theorem tailTrace_3575737 : CollatzResearch.WordTrace tailWord_3575737 prefixEnd_3575737 204007975007331294026999 := by
  unfold tailWord_3575737
  simp only [CollatzResearch.WordTrace]
  refine ⟨130417842646723011105413465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86945228431148674070275643 130417842646723011105413465)
  ·
    refine ⟨97813381985042258329060099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130417842646723011105413465 97813381985042258329060099)
    ·
      refine ⟨146720072977563387493590149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97813381985042258329060099 146720072977563387493590149)
      ·
        refine ⟨27510013683293135155048153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146720072977563387493590149 27510013683293135155048153)
        ·
          refine ⟨20632510262469851366286115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27510013683293135155048153 20632510262469851366286115)
          ·
            refine ⟨30948765393704777049429173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20632510262469851366286115 30948765393704777049429173)
            ·
              refine ⟨2901446755659822848383985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30948765393704777049429173 2901446755659822848383985)
              ·
                refine ⟨2176085066744867136287989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901446755659822848383985 2176085066744867136287989)
                ·
                  refine ⟨204007975007331294026999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176085066744867136287989 204007975007331294026999)
                  ·
                    rfl

theorem cell23_3575737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 5].length) (baseStart_3575737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575737 prefixEnd_3575737 := by exact prefixLift 3575737
  have htrace : WordTrace (prefixWord ++ tailWord_3575737) baseStart_3575737 baseEnd_3575737 := by
    simpa [prefixWord, tailWord_3575737, baseEnd_3575737] using wordTrace_append hprefix tailTrace_3575737
  have hstable : (prefixWord ++ tailWord_3575737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575737).length < 2 ^ (prefixWord ++ tailWord_3575737).sum := by decide
  have hdescent : baseEnd_3575737 < baseStart_3575737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575743 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_3575743 : Nat := 118140960795 + 3575743 * 2 ^ 59
def prefixEnd_3575743 : Nat := 4983230072969 + 3 ^ 40 * 3575743 * 2
def baseEnd_3575743 : Nat := 1836074855949908622767963

theorem tailTrace_3575743 : CollatzResearch.WordTrace tailWord_3575743 prefixEnd_3575743 1836074855949908622767963 := by
  unfold tailWord_3575743
  simp only [CollatzResearch.WordTrace]
  refine ⟨130418061484701274130131883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86945374323134182753421255 130418061484701274130131883)
  ·
    refine ⟨195627092227051911195197825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130418061484701274130131883 195627092227051911195197825)
    ·
      refine ⟨146720319170288933396398369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195627092227051911195197825 146720319170288933396398369)
      ·
        refine ⟨110040239377716700047298777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146720319170288933396398369 110040239377716700047298777)
        ·
          refine ⟨82530179533287525035474083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110040239377716700047298777 82530179533287525035474083)
          ·
            refine ⟨123795269299931287553211125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82530179533287525035474083 123795269299931287553211125)
            ·
              refine ⟨11605806496868558208113543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123795269299931287553211125 11605806496868558208113543)
              ·
                refine ⟨17408709745302837312170315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605806496868558208113543 17408709745302837312170315)
                ·
                  refine ⟨26113064617954255968255473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17408709745302837312170315 26113064617954255968255473)
                  ·
                    refine ⟨19584798463465691976191605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26113064617954255968255473 19584798463465691976191605)
                    ·
                      refine ⟨1836074855949908622767963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19584798463465691976191605 1836074855949908622767963)
                      ·
                        rfl

theorem cell23_3575743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_3575743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575743 prefixEnd_3575743 := by exact prefixLift 3575743
  have htrace : WordTrace (prefixWord ++ tailWord_3575743) baseStart_3575743 baseEnd_3575743 := by
    simpa [prefixWord, tailWord_3575743, baseEnd_3575743] using wordTrace_append hprefix tailTrace_3575743
  have hstable : (prefixWord ++ tailWord_3575743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575743).length < 2 ^ (prefixWord ++ tailWord_3575743).sum := by decide
  have hdescent : baseEnd_3575743 < baseStart_3575743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575821 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3575821 : Nat := 118140960795 + 3575821 * 2 ^ 59
def prefixEnd_3575821 : Nat := 4983230072969 + 3 ^ 40 * 3575821 * 2
def baseEnd_3575821 : Nat := 1836114907440959317592605

theorem tailTrace_3575821 : CollatzResearch.WordTrace tailWord_3575821 prefixEnd_3575821 1836114907440959317592605 := by
  unfold tailWord_3575821
  simp only [CollatzResearch.WordTrace]
  refine ⟨130420906378418693451471317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86947270918945795634314211 130420906378418693451471317)
  ·
    refine ⟨3056739993244188127768859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130420906378418693451471317 3056739993244188127768859)
    ·
      refine ⟨4585109989866282191653289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056739993244188127768859 4585109989866282191653289)
      ·
        refine ⟨3438832492399711643739967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585109989866282191653289 3438832492399711643739967)
        ·
          refine ⟨5158248738599567465609951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438832492399711643739967 5158248738599567465609951)
          ·
            refine ⟨7737373107899351198414927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158248738599567465609951 7737373107899351198414927)
            ·
              refine ⟨11606059661849026797622391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737373107899351198414927 11606059661849026797622391)
              ·
                refine ⟨17409089492773540196433587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11606059661849026797622391 17409089492773540196433587)
                ·
                  refine ⟨26113634239160310294650381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17409089492773540196433587 26113634239160310294650381)
                  ·
                    refine ⟨9792612839685116360493893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26113634239160310294650381 9792612839685116360493893)
                    ·
                      refine ⟨1836114907440959317592605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9792612839685116360493893 1836114907440959317592605)
                      ·
                        rfl

theorem cell23_3575821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3575821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575821 prefixEnd_3575821 := by exact prefixLift 3575821
  have htrace : WordTrace (prefixWord ++ tailWord_3575821) baseStart_3575821 baseEnd_3575821 := by
    simpa [prefixWord, tailWord_3575821, baseEnd_3575821] using wordTrace_append hprefix tailTrace_3575821
  have hstable : (prefixWord ++ tailWord_3575821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575821).length < 2 ^ (prefixWord ++ tailWord_3575821).sum := by decide
  have hdescent : baseEnd_3575821 < baseStart_3575821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575831 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 1, 4]
def baseStart_3575831 : Nat := 118140960795 + 3575831 * 2 ^ 59
def prefixEnd_3575831 : Nat := 4983230072969 + 3 ^ 40 * 3575831 * 2
def baseEnd_3575831 : Nat := 612040014082501426155853

theorem tailTrace_3575831 : CollatzResearch.WordTrace tailWord_3575831 prefixEnd_3575831 612040014082501426155853 := by
  unfold tailWord_3575831
  simp only [CollatzResearch.WordTrace]
  refine ⟨130421271108382465159335347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86947514072254976772890231 130421271108382465159335347)
  ·
    refine ⟨195631906662573697739003021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130421271108382465159335347 195631906662573697739003021)
    ·
      refine ⟨73361964998465136652126133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195631906662573697739003021 73361964998465136652126133)
      ·
        refine ⟨6877684218606106561136825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73361964998465136652126133 6877684218606106561136825)
        ·
          refine ⟨5158263163954579920852619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877684218606106561136825 5158263163954579920852619)
          ·
            refine ⟨7737394745931869881278929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158263163954579920852619 7737394745931869881278929)
            ·
              refine ⟨5803046059448902410959197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7737394745931869881278929 5803046059448902410959197)
              ·
                refine ⟨2176142272293338404109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5803046059448902410959197 2176142272293338404109699)
                ·
                  refine ⟨3264213408440007606164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176142272293338404109699 3264213408440007606164549)
                  ·
                    refine ⟨612040014082501426155853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264213408440007606164549 612040014082501426155853)
                    ·
                      rfl

theorem cell23_3575831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_3575831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575831 prefixEnd_3575831 := by exact prefixLift 3575831
  have htrace : WordTrace (prefixWord ++ tailWord_3575831) baseStart_3575831 baseEnd_3575831 := by
    simpa [prefixWord, tailWord_3575831, baseEnd_3575831] using wordTrace_append hprefix tailTrace_3575831
  have hstable : (prefixWord ++ tailWord_3575831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575831).length < 2 ^ (prefixWord ++ tailWord_3575831).sum := by decide
  have hdescent : baseEnd_3575831 < baseStart_3575831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575833 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3575833 : Nat := 118140960795 + 3575833 * 2 ^ 59
def prefixEnd_3575833 : Nat := 4983230072969 + 3 ^ 40 * 3575833 * 2
def baseEnd_3575833 : Nat := 1836121069208813270642549

theorem tailTrace_3575833 : CollatzResearch.WordTrace tailWord_3575833 prefixEnd_3575833 1836121069208813270642549 := by
  unfold tailWord_3575833
  simp only [CollatzResearch.WordTrace]
  refine ⟨130421344054375219500908153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86947562702916813000605435 130421344054375219500908153)
  ·
    refine ⟨97816008040781414625681115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130421344054375219500908153 97816008040781414625681115)
    ·
      refine ⟨146724012061172121938521673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97816008040781414625681115 146724012061172121938521673)
      ·
        refine ⟨110043009045879091453891255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146724012061172121938521673 110043009045879091453891255)
        ·
          refine ⟨165064513568818637180836883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110043009045879091453891255 165064513568818637180836883)
          ·
            refine ⟨247596770353227955771255325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165064513568818637180836883 247596770353227955771255325)
            ·
              refine ⟨92848788882460483414220747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247596770353227955771255325 92848788882460483414220747)
              ·
                refine ⟨139273183323690725121331121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92848788882460483414220747 139273183323690725121331121)
                ·
                  refine ⟨104454887492768043840998341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139273183323690725121331121 104454887492768043840998341)
                  ·
                    refine ⟨19585291404894008220187189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104454887492768043840998341 19585291404894008220187189)
                    ·
                      refine ⟨1836121069208813270642549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19585291404894008220187189 1836121069208813270642549)
                      ·
                        rfl

theorem cell23_3575833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3575833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575833 prefixEnd_3575833 := by exact prefixLift 3575833
  have htrace : WordTrace (prefixWord ++ tailWord_3575833) baseStart_3575833 baseEnd_3575833 := by
    simpa [prefixWord, tailWord_3575833, baseEnd_3575833] using wordTrace_append hprefix tailTrace_3575833
  have hstable : (prefixWord ++ tailWord_3575833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575833).length < 2 ^ (prefixWord ++ tailWord_3575833).sum := by decide
  have hdescent : baseEnd_3575833 < baseStart_3575833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575844 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 6]
def baseStart_3575844 : Nat := 118140960795 + 3575844 * 2 ^ 59
def prefixEnd_3575844 : Nat := 4983230072969 + 3 ^ 40 * 3575844 * 2
def baseEnd_3575844 : Nat := 204014079721779191956111

theorem tailTrace_3575844 : CollatzResearch.WordTrace tailWord_3575844 prefixEnd_3575844 204014079721779191956111 := by
  unfold tailWord_3575844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65210872628667684189779293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86947830171556912253039057 65210872628667684189779293)
  ·
    refine ⟨24454077235750381571167235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65210872628667684189779293 24454077235750381571167235)
    ·
      refine ⟨36681115853625572356750853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24454077235750381571167235 36681115853625572356750853)
      ·
        refine ⟨6877709222554794816890785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36681115853625572356750853 6877709222554794816890785)
        ·
          refine ⟨5158281916916096112668089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877709222554794816890785 5158281916916096112668089)
          ·
            refine ⟨3868711437687072084501067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158281916916096112668089 3868711437687072084501067)
            ·
              refine ⟨5803067156530608126751601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868711437687072084501067 5803067156530608126751601)
              ·
                refine ⟨4352300367397956095063701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803067156530608126751601 4352300367397956095063701)
                ·
                  refine ⟨204014079721779191956111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4352300367397956095063701 204014079721779191956111)
                  ·
                    rfl

theorem cell23_3575844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_3575844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575844 prefixEnd_3575844 := by exact prefixLift 3575844
  have htrace : WordTrace (prefixWord ++ tailWord_3575844) baseStart_3575844 baseEnd_3575844 := by
    simpa [prefixWord, tailWord_3575844, baseEnd_3575844] using wordTrace_append hprefix tailTrace_3575844
  have hstable : (prefixWord ++ tailWord_3575844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575844).length < 2 ^ (prefixWord ++ tailWord_3575844).sum := by decide
  have hdescent : baseEnd_3575844 < baseStart_3575844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575854 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3575854 : Nat := 118140960795 + 3575854 * 2 ^ 59
def prefixEnd_3575854 : Nat := 4983230072969 + 3 ^ 40 * 3575854 * 2
def baseEnd_3575854 : Nat := 1836131852302557688479953

theorem tailTrace_3575854 : CollatzResearch.WordTrace tailWord_3575854 prefixEnd_3575854 1836131852302557688479953 := by
  unfold tailWord_3575854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16302763748412392510927827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86948073324866093391615077 16302763748412392510927827)
  ·
    refine ⟨24454145622618588766391741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16302763748412392510927827 24454145622618588766391741)
    ·
      refine ⟨9170304608481970787396903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24454145622618588766391741 9170304608481970787396903)
      ·
        refine ⟨13755456912722956181095355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170304608481970787396903 13755456912722956181095355)
        ·
          refine ⟨20633185369084434271643033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13755456912722956181095355 20633185369084434271643033)
          ·
            refine ⟨15474889026813325703732275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20633185369084434271643033 15474889026813325703732275)
            ·
              refine ⟨23212333540219988555598413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15474889026813325703732275 23212333540219988555598413)
              ·
                refine ⟨8704625077582495708349405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23212333540219988555598413 8704625077582495708349405)
                ·
                  refine ⟨3264234404093435890631027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8704625077582495708349405 3264234404093435890631027)
                  ·
                    refine ⟨4896351606140153835946541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264234404093435890631027 4896351606140153835946541)
                    ·
                      refine ⟨1836131852302557688479953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896351606140153835946541 1836131852302557688479953)
                      ·
                        rfl

theorem cell23_3575854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3575854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575854 prefixEnd_3575854 := by exact prefixLift 3575854
  have htrace : WordTrace (prefixWord ++ tailWord_3575854) baseStart_3575854 baseEnd_3575854 := by
    simpa [prefixWord, tailWord_3575854, baseEnd_3575854] using wordTrace_append hprefix tailTrace_3575854
  have hstable : (prefixWord ++ tailWord_3575854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575854).length < 2 ^ (prefixWord ++ tailWord_3575854).sum := by decide
  have hdescent : baseEnd_3575854 < baseStart_3575854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575883 : List Nat := [1, 1, 1, 1, 3, 1, 2, 13]
def baseStart_3575883 : Nat := 118140960795 + 3575883 * 2 ^ 59
def prefixEnd_3575883 : Nat := 4983230072969 + 3 ^ 40 * 3575883 * 2
def baseEnd_3575883 : Nat := 68005434934871780556197

theorem tailTrace_3575883 : CollatzResearch.WordTrace tailWord_3575883 prefixEnd_3575883 68005434934871780556197 := by
  unfold tailWord_3575883
  simp only [CollatzResearch.WordTrace]
  refine ⟨130423167704194078040228303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86948778469462718693485535 130423167704194078040228303)
  ·
    refine ⟨195634751556291117060342455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130423167704194078040228303 195634751556291117060342455)
    ·
      refine ⟨293452127334436675590513683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195634751556291117060342455 293452127334436675590513683)
      ·
        refine ⟨440178191001655013385770525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293452127334436675590513683 440178191001655013385770525)
        ·
          refine ⟨165066821625620630019663947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440178191001655013385770525 165066821625620630019663947)
          ·
            refine ⟨247600232438430945029495921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165066821625620630019663947 247600232438430945029495921)
            ·
              refine ⟨185700174328823208772121941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247600232438430945029495921 185700174328823208772121941)
              ·
                refine ⟨68005434934871780556197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 185700174328823208772121941 68005434934871780556197)
                ·
                  rfl

theorem cell23_3575883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 13].length) (baseStart_3575883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575883 prefixEnd_3575883 := by exact prefixLift 3575883
  have htrace : WordTrace (prefixWord ++ tailWord_3575883) baseStart_3575883 baseEnd_3575883 := by
    simpa [prefixWord, tailWord_3575883, baseEnd_3575883] using wordTrace_append hprefix tailTrace_3575883
  have hstable : (prefixWord ++ tailWord_3575883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575883).length < 2 ^ (prefixWord ++ tailWord_3575883).sum := by decide
  have hdescent : baseEnd_3575883 < baseStart_3575883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575897 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3575897 : Nat := 118140960795 + 3575897 * 2 ^ 59
def prefixEnd_3575897 : Nat := 4983230072969 + 3 ^ 40 * 3575897 * 2
def baseEnd_3575897 : Nat := 1836153931970701020242255

theorem tailTrace_3575897 : CollatzResearch.WordTrace tailWord_3575897 prefixEnd_3575897 1836153931970701020242255 := by
  unfold tailWord_3575897
  simp only [CollatzResearch.WordTrace]
  refine ⟨130423678326143358431237945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86949118884095572287491963 130423678326143358431237945)
  ·
    refine ⟨97817758744607518823428459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130423678326143358431237945 97817758744607518823428459)
    ·
      refine ⟨146726638116911278235142689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97817758744607518823428459 146726638116911278235142689)
      ·
        refine ⟨110044978587683458676357017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146726638116911278235142689 110044978587683458676357017)
        ·
          refine ⟨82533733940762594007267763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110044978587683458676357017 82533733940762594007267763)
          ·
            refine ⟨123800600911143891010901645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82533733940762594007267763 123800600911143891010901645)
            ·
              refine ⟨46425225341678959129088117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123800600911143891010901645 46425225341678959129088117)
              ·
                refine ⟨4352364875782402418352011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46425225341678959129088117 4352364875782402418352011)
                ·
                  refine ⟨6528547313673603627528017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352364875782402418352011 6528547313673603627528017)
                  ·
                    refine ⟨4896410485255202720646013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6528547313673603627528017 4896410485255202720646013)
                    ·
                      refine ⟨1836153931970701020242255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896410485255202720646013 1836153931970701020242255)
                      ·
                        rfl

theorem cell23_3575897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3575897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575897 prefixEnd_3575897 := by exact prefixLift 3575897
  have htrace : WordTrace (prefixWord ++ tailWord_3575897) baseStart_3575897 baseEnd_3575897 := by
    simpa [prefixWord, tailWord_3575897, baseEnd_3575897] using wordTrace_append hprefix tailTrace_3575897
  have hstable : (prefixWord ++ tailWord_3575897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575897).length < 2 ^ (prefixWord ++ tailWord_3575897).sum := by decide
  have hdescent : baseEnd_3575897 < baseStart_3575897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575900 : List Nat := [2, 2, 4, 1, 1, 2, 11]
def baseStart_3575900 : Nat := 118140960795 + 3575900 * 2 ^ 59
def prefixEnd_3575900 : Nat := 4983230072969 + 3 ^ 40 * 3575900 * 2
def baseEnd_3575900 : Nat := 22668586079168697635861

theorem tailTrace_3575900 : CollatzResearch.WordTrace tailWord_3575900 prefixEnd_3575900 22668586079168697635861 := by
  unfold tailWord_3575900
  simp only [CollatzResearch.WordTrace]
  refine ⟨65211893872566244971798577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86949191830088326629064769 65211893872566244971798577)
  ·
    refine ⟨48908920404424683728848933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65211893872566244971798577 48908920404424683728848933)
    ·
      refine ⟨9170422575829628199159175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48908920404424683728848933 9170422575829628199159175)
      ·
        refine ⟨13755633863744442298738763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170422575829628199159175 13755633863744442298738763)
        ·
          refine ⟨20633450795616663448108145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13755633863744442298738763 20633450795616663448108145)
          ·
            refine ⟨15475088096712497586081109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20633450795616663448108145 15475088096712497586081109)
            ·
              refine ⟨22668586079168697635861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15475088096712497586081109 22668586079168697635861)
              ·
                rfl

theorem cell23_3575900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 11].length) (baseStart_3575900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575900 prefixEnd_3575900 := by exact prefixLift 3575900
  have htrace : WordTrace (prefixWord ++ tailWord_3575900) baseStart_3575900 baseEnd_3575900 := by
    simpa [prefixWord, tailWord_3575900, baseEnd_3575900] using wordTrace_append hprefix tailTrace_3575900
  have hstable : (prefixWord ++ tailWord_3575900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575900).length < 2 ^ (prefixWord ++ tailWord_3575900).sum := by decide
  have hdescent : baseEnd_3575900 < baseStart_3575900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575944 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3575944 : Nat := 118140960795 + 3575944 * 2 ^ 59
def prefixEnd_3575944 : Nat := 4983230072969 + 3 ^ 40 * 3575944 * 2
def baseEnd_3575944 : Nat := 1836178065561462336354539

theorem tailTrace_3575944 : CollatzResearch.WordTrace tailWord_3575944 prefixEnd_3575944 1836178065561462336354539 := by
  unfold tailWord_3575944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65212696278486542729099443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86950261704648723638799257 65212696278486542729099443)
  ·
    refine ⟨97819044417729814093649165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65212696278486542729099443 97819044417729814093649165)
    ·
      refine ⟨36682141656648680285118437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97819044417729814093649165 36682141656648680285118437)
      ·
        refine ⟨6877901560621627553459707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36682141656648680285118437 6877901560621627553459707)
        ·
          refine ⟨10316852340932441330189561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877901560621627553459707 10316852340932441330189561)
          ·
            refine ⟨7737639255699330997642171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316852340932441330189561 7737639255699330997642171)
            ·
              refine ⟨11606458883548996496463257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737639255699330997642171 11606458883548996496463257)
              ·
                refine ⟨8704844162661747372347443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11606458883548996496463257 8704844162661747372347443)
                ·
                  refine ⟨13057266243992621058521165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8704844162661747372347443 13057266243992621058521165)
                  ·
                    refine ⟨4896474841497232896945437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13057266243992621058521165 4896474841497232896945437)
                    ·
                      refine ⟨1836178065561462336354539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896474841497232896945437 1836178065561462336354539)
                      ·
                        rfl

theorem cell23_3575944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3575944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575944 prefixEnd_3575944 := by exact prefixLift 3575944
  have htrace : WordTrace (prefixWord ++ tailWord_3575944) baseStart_3575944 baseEnd_3575944 := by
    simpa [prefixWord, tailWord_3575944, baseEnd_3575944] using wordTrace_append hprefix tailTrace_3575944
  have hstable : (prefixWord ++ tailWord_3575944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575944).length < 2 ^ (prefixWord ++ tailWord_3575944).sum := by decide
  have hdescent : baseEnd_3575944 < baseStart_3575944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575962 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3575962 : Nat := 118140960795 + 3575962 * 2 ^ 59
def prefixEnd_3575962 : Nat := 4983230072969 + 3 ^ 40 * 3575962 * 2
def baseEnd_3575962 : Nat := 1836187308213243265929457

theorem tailTrace_3575962 : CollatzResearch.WordTrace tailWord_3575962 prefixEnd_3575962 1836187308213243265929457 := by
  unfold tailWord_3575962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32606512267726968633088535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86950699380605249688236093 32606512267726968633088535)
  ·
    refine ⟨48909768401590452949632803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32606512267726968633088535 48909768401590452949632803)
    ·
      refine ⟨73364652602385679424449205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48909768401590452949632803 73364652602385679424449205)
      ·
        refine ⟨6877936181473657446042113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73364652602385679424449205 6877936181473657446042113)
        ·
          refine ⟨5158452136105243084531585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877936181473657446042113 5158452136105243084531585)
          ·
            refine ⟨3868839102078932313398689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158452136105243084531585 3868839102078932313398689)
            ·
              refine ⟨2901629326559199235049017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868839102078932313398689 2901629326559199235049017)
              ·
                refine ⟨2176221994919399426286763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901629326559199235049017 2176221994919399426286763)
                ·
                  refine ⟨3264332992379099139430145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176221994919399426286763 3264332992379099139430145)
                  ·
                    refine ⟨2448249744284324354572609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264332992379099139430145 2448249744284324354572609)
                    ·
                      refine ⟨1836187308213243265929457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448249744284324354572609 1836187308213243265929457)
                      ·
                        rfl

theorem cell23_3575962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3575962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575962 prefixEnd_3575962 := by exact prefixLift 3575962
  have htrace : WordTrace (prefixWord ++ tailWord_3575962) baseStart_3575962 baseEnd_3575962 := by
    simpa [prefixWord, tailWord_3575962, baseEnd_3575962] using wordTrace_append hprefix tailTrace_3575962
  have hstable : (prefixWord ++ tailWord_3575962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575962).length < 2 ^ (prefixWord ++ tailWord_3575962).sum := by decide
  have hdescent : baseEnd_3575962 < baseStart_3575962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575967 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3575967 : Nat := 118140960795 + 3575967 * 2 ^ 59
def prefixEnd_3575967 : Nat := 4983230072969 + 3 ^ 40 * 3575967 * 2
def baseEnd_3575967 : Nat := 1836189875616515746366933

theorem tailTrace_3575967 : CollatzResearch.WordTrace tailWord_3575967 prefixEnd_3575967 1836189875616515746366933 := by
  unfold tailWord_3575967
  simp only [CollatzResearch.WordTrace]
  refine ⟨130426231435889760386286155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86950820957259840257524103 130426231435889760386286155)
  ·
    refine ⟨195639347153834640579429233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130426231435889760386286155 195639347153834640579429233)
    ·
      refine ⟨146729510365375980434571925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195639347153834640579429233 146729510365375980434571925)
      ·
        refine ⟨6877945798376999082870559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146729510365375980434571925 6877945798376999082870559)
        ·
          refine ⟨10316918697565498624305839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877945798376999082870559 10316918697565498624305839)
          ·
            refine ⟨15475378046348247936458759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316918697565498624305839 15475378046348247936458759)
            ·
              refine ⟨23213067069522371904688139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475378046348247936458759 23213067069522371904688139)
              ·
                refine ⟨34819600604283557857032209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23213067069522371904688139 34819600604283557857032209)
                ·
                  refine ⟨26114700453212668392774157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34819600604283557857032209 26114700453212668392774157)
                  ·
                    refine ⟨9793012669954750647290309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26114700453212668392774157 9793012669954750647290309)
                    ·
                      refine ⟨1836189875616515746366933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9793012669954750647290309 1836189875616515746366933)
                      ·
                        rfl

theorem cell23_3575967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3575967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3575967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3575967 prefixEnd_3575967 := by exact prefixLift 3575967
  have htrace : WordTrace (prefixWord ++ tailWord_3575967) baseStart_3575967 baseEnd_3575967 := by
    simpa [prefixWord, tailWord_3575967, baseEnd_3575967] using wordTrace_append hprefix tailTrace_3575967
  have hstable : (prefixWord ++ tailWord_3575967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575967).length < 2 ^ (prefixWord ++ tailWord_3575967).sum := by decide
  have hdescent : baseEnd_3575967 < baseStart_3575967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576017 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_3576017 : Nat := 118140960795 + 3576017 * 2 ^ 59
def prefixEnd_3576017 : Nat := 4983230072969 + 3 ^ 40 * 3576017 * 2
def baseEnd_3576017 : Nat := 1836215549649240550741703

theorem tailTrace_3576017 : CollatzResearch.WordTrace tailWord_3576017 prefixEnd_3576017 1836215549649240550741703 := by
  unfold tailWord_3576017
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428055085708618925606305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86952036723805745950404203 130428055085708618925606305)
  ·
    refine ⟨97821041314281464194204729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130428055085708618925606305 97821041314281464194204729)
    ·
      refine ⟨73365780985711098145653547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97821041314281464194204729 73365780985711098145653547)
      ·
        refine ⟨110048671478566647218480321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73365780985711098145653547 110048671478566647218480321)
        ·
          refine ⟨82536503608924985413860241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110048671478566647218480321 82536503608924985413860241)
          ·
            refine ⟨61902377706693739060395181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82536503608924985413860241 61902377706693739060395181)
            ·
              refine ⟨23213391640010152147648193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61902377706693739060395181 23213391640010152147648193)
              ·
                refine ⟨17410043730007614110736145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23213391640010152147648193 17410043730007614110736145)
                ·
                  refine ⟨13057532797505710583052109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17410043730007614110736145 13057532797505710583052109)
                  ·
                    refine ⟨4896574799064641468644541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13057532797505710583052109 4896574799064641468644541)
                    ·
                      refine ⟨1836215549649240550741703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896574799064641468644541 1836215549649240550741703)
                      ·
                        rfl

theorem cell23_3576017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_3576017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576017 prefixEnd_3576017 := by exact prefixLift 3576017
  have htrace : WordTrace (prefixWord ++ tailWord_3576017) baseStart_3576017 baseEnd_3576017 := by
    simpa [prefixWord, tailWord_3576017, baseEnd_3576017] using wordTrace_append hprefix tailTrace_3576017
  have hstable : (prefixWord ++ tailWord_3576017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576017).length < 2 ^ (prefixWord ++ tailWord_3576017).sum := by decide
  have hdescent : baseEnd_3576017 < baseStart_3576017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576018 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3576018 : Nat := 118140960795 + 3576018 * 2 ^ 59
def prefixEnd_3576018 : Nat := 4983230072969 + 3 ^ 40 * 3576018 * 2
def baseEnd_3576018 : Nat := 1836216063129895046829199

theorem tailTrace_3576018 : CollatzResearch.WordTrace tailWord_3576018 prefixEnd_3576018 1836216063129895046829199 := by
  unfold tailWord_3576018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607022889676249024098177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86952061039136664064261805 32607022889676249024098177)
  ·
    refine ⟨24455267167257186768073633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32607022889676249024098177 24455267167257186768073633)
    ·
      refine ⟨18341450375442890076055225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24455267167257186768073633 18341450375442890076055225)
      ·
        refine ⟨13756087781582167557041419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18341450375442890076055225 13756087781582167557041419)
        ·
          refine ⟨20634131672373251335562129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13756087781582167557041419 20634131672373251335562129)
          ·
            refine ⟨15475598754279938501671597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20634131672373251335562129 15475598754279938501671597)
            ·
              refine ⟨5803349532854976938126849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15475598754279938501671597 5803349532854976938126849)
              ·
                refine ⟨4352512149641232703595137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803349532854976938126849 4352512149641232703595137)
                ·
                  refine ⟨3264384112230924527696353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352512149641232703595137 3264384112230924527696353)
                  ·
                    refine ⟨2448288084173193395772265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264384112230924527696353 2448288084173193395772265)
                    ·
                      refine ⟨1836216063129895046829199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448288084173193395772265 1836216063129895046829199)
                      ·
                        rfl

theorem cell23_3576018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3576018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576018 prefixEnd_3576018 := by exact prefixLift 3576018
  have htrace : WordTrace (prefixWord ++ tailWord_3576018) baseStart_3576018 baseEnd_3576018 := by
    simpa [prefixWord, tailWord_3576018, baseEnd_3576018] using wordTrace_append hprefix tailTrace_3576018
  have hstable : (prefixWord ++ tailWord_3576018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576018).length < 2 ^ (prefixWord ++ tailWord_3576018).sum := by decide
  have hdescent : baseEnd_3576018 < baseStart_3576018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576024 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 5]
def baseStart_3576024 : Nat := 118140960795 + 3576024 * 2 ^ 59
def prefixEnd_3576024 : Nat := 4983230072969 + 3 ^ 40 * 3576024 * 2
def baseEnd_3576024 : Nat := 204024349334869113706019

theorem tailTrace_3576024 : CollatzResearch.WordTrace tailWord_3576024 prefixEnd_3576024 204024349334869113706019 := by
  unfold tailWord_3576024
  simp only [CollatzResearch.WordTrace]
  refine ⟨65214155198341629560555563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86952206931122172747407417 65214155198341629560555563)
  ·
    refine ⟨97821232797512444340833345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65214155198341629560555563 97821232797512444340833345)
    ·
      refine ⟨73365924598134333255625009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97821232797512444340833345 73365924598134333255625009)
      ·
        refine ⟨55024443448600749941718757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73365924598134333255625009 55024443448600749941718757)
        ·
          refine ⟨10317083146612640614072267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55024443448600749941718757 10317083146612640614072267)
          ·
            refine ⟨15475624719918960921108401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10317083146612640614072267 15475624719918960921108401)
            ·
              refine ⟨11606718539939220690831301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15475624719918960921108401 11606718539939220690831301)
              ·
                refine ⟨2176259726238603879530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11606718539939220690831301 2176259726238603879530869)
                ·
                  refine ⟨204024349334869113706019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176259726238603879530869 204024349334869113706019)
                  ·
                    rfl

theorem cell23_3576024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 5].length) (baseStart_3576024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576024 prefixEnd_3576024 := by exact prefixLift 3576024
  have htrace : WordTrace (prefixWord ++ tailWord_3576024) baseStart_3576024 baseEnd_3576024 := by
    simpa [prefixWord, tailWord_3576024, baseEnd_3576024] using wordTrace_append hprefix tailTrace_3576024
  have hstable : (prefixWord ++ tailWord_3576024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576024).length < 2 ^ (prefixWord ++ tailWord_3576024).sum := by decide
  have hdescent : baseEnd_3576024 < baseStart_3576024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576035 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3576035 : Nat := 118140960795 + 3576035 * 2 ^ 59
def prefixEnd_3576035 : Nat := 4983230072969 + 3 ^ 40 * 3576035 * 2
def baseEnd_3576035 : Nat := 1836224792301021480316621

theorem tailTrace_3576035 : CollatzResearch.WordTrace tailWord_3576035 prefixEnd_3576035 1836224792301021480316621 := by
  unfold tailWord_3576035
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428711599643407999761559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86952474399762271999841039 130428711599643407999761559)
  ·
    refine ⟨195643067399465111999642339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130428711599643407999761559 195643067399465111999642339)
    ·
      refine ⟨293464601099197667999463509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195643067399465111999642339 293464601099197667999463509)
      ·
        refine ⟨3439038294131222671868713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 293464601099197667999463509 3439038294131222671868713)
        ·
          refine ⟨2579278720598417003901535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439038294131222671868713 2579278720598417003901535)
          ·
            refine ⟨3868918080897625505852303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579278720598417003901535 3868918080897625505852303)
            ·
              refine ⟨5803377121346438258778455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868918080897625505852303 5803377121346438258778455)
              ·
                refine ⟨8705065682019657388167683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803377121346438258778455 8705065682019657388167683)
                ·
                  refine ⟨13057598523029486082251525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8705065682019657388167683 13057598523029486082251525)
                  ·
                    refine ⟨2448299723068028640422161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13057598523029486082251525 2448299723068028640422161)
                    ·
                      refine ⟨1836224792301021480316621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448299723068028640422161 1836224792301021480316621)
                      ·
                        rfl

theorem cell23_3576035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3576035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576035 prefixEnd_3576035 := by exact prefixLift 3576035
  have htrace : WordTrace (prefixWord ++ tailWord_3576035) baseStart_3576035 baseEnd_3576035 := by
    simpa [prefixWord, tailWord_3576035, baseEnd_3576035] using wordTrace_append hprefix tailTrace_3576035
  have hstable : (prefixWord ++ tailWord_3576035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576035).length < 2 ^ (prefixWord ++ tailWord_3576035).sum := by decide
  have hdescent : baseEnd_3576035 < baseStart_3576035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576037 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_3576037 : Nat := 118140960795 + 3576037 * 2 ^ 59
def prefixEnd_3576037 : Nat := 4983230072969 + 3 ^ 40 * 3576037 * 2
def baseEnd_3576037 : Nat := 612075273087443490830537

theorem tailTrace_3576037 : CollatzResearch.WordTrace tailWord_3576037 prefixEnd_3576037 612075273087443490830537 := by
  unfold tailWord_3576037
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428784545636162341334365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86952523030424108227556243 130428784545636162341334365)
  ·
    refine ⟨48910794204613560878000387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130428784545636162341334365 48910794204613560878000387)
    ·
      refine ⟨73366191306920341317000581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48910794204613560878000387 73366191306920341317000581)
      ·
        refine ⟨13756160870047563996937609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73366191306920341317000581 13756160870047563996937609)
        ·
          refine ⟨10317120652535672997703207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13756160870047563996937609 10317120652535672997703207)
          ·
            refine ⟨15475680978803509496554811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10317120652535672997703207 15475680978803509496554811)
            ·
              refine ⟨23213521468205264244832217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475680978803509496554811 23213521468205264244832217)
              ·
                refine ⟨17410141101153948183624163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23213521468205264244832217 17410141101153948183624163)
                ·
                  refine ⟨26115211651730922275436245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17410141101153948183624163 26115211651730922275436245)
                  ·
                    refine ⟨612075273087443490830537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26115211651730922275436245 612075273087443490830537)
                    ·
                      rfl

theorem cell23_3576037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_3576037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576037 prefixEnd_3576037 := by exact prefixLift 3576037
  have htrace : WordTrace (prefixWord ++ tailWord_3576037) baseStart_3576037 baseEnd_3576037 := by
    simpa [prefixWord, tailWord_3576037, baseEnd_3576037] using wordTrace_append hprefix tailTrace_3576037
  have hstable : (prefixWord ++ tailWord_3576037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576037).length < 2 ^ (prefixWord ++ tailWord_3576037).sum := by decide
  have hdescent : baseEnd_3576037 < baseStart_3576037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576071 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 2, 5]
def baseStart_3576071 : Nat := 118140960795 + 3576071 * 2 ^ 59
def prefixEnd_3576071 : Nat := 4983230072969 + 3 ^ 40 * 3576071 * 2
def baseEnd_3576071 : Nat := 612081092534861113155485

theorem tailTrace_3576071 : CollatzResearch.WordTrace tailWord_3576071 prefixEnd_3576071 612081092534861113155485 := by
  unfold tailWord_3576071
  simp only [CollatzResearch.WordTrace]
  refine ⟨130430024627512986148072067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86953349751675324098714711 130430024627512986148072067)
  ·
    refine ⟨195645036941269479222108101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130430024627512986148072067 195645036941269479222108101)
    ·
      refine ⟨36683444426488027354145269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195645036941269479222108101 36683444426488027354145269)
      ·
        refine ⟨3439072914983252564451119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36683444426488027354145269 3439072914983252564451119)
        ·
          refine ⟨5158609372474878846676679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439072914983252564451119 5158609372474878846676679)
          ·
            refine ⟨7737914058712318270015019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158609372474878846676679 7737914058712318270015019)
            ·
              refine ⟨11606871088068477405022529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737914058712318270015019 11606871088068477405022529)
              ·
                refine ⟨8705153316051358053766897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11606871088068477405022529 8705153316051358053766897)
                ·
                  refine ⟨6528864987038518540325173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705153316051358053766897 6528864987038518540325173)
                  ·
                    refine ⟨612081092534861113155485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6528864987038518540325173 612081092534861113155485)
                    ·
                      rfl

theorem cell23_3576071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_3576071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576071 prefixEnd_3576071 := by exact prefixLift 3576071
  have htrace : WordTrace (prefixWord ++ tailWord_3576071) baseStart_3576071 baseEnd_3576071 := by
    simpa [prefixWord, tailWord_3576071, baseEnd_3576071] using wordTrace_append hprefix tailTrace_3576071
  have hstable : (prefixWord ++ tailWord_3576071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576071).length < 2 ^ (prefixWord ++ tailWord_3576071).sum := by decide
  have hdescent : baseEnd_3576071 < baseStart_3576071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576074 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_3576074 : Nat := 118140960795 + 3576074 * 2 ^ 59
def prefixEnd_3576074 : Nat := 4983230072969 + 3 ^ 40 * 3576074 * 2
def baseEnd_3576074 : Nat := 1836244818046546827728941

theorem tailTrace_3576074 : CollatzResearch.WordTrace tailWord_3576074 prefixEnd_3576074 1836244818046546827728941 := by
  unfold tailWord_3576074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607533511625529415107819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86953422697668078440287517 32607533511625529415107819)
  ·
    refine ⟨48911300267438294122661729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32607533511625529415107819 48911300267438294122661729)
    ·
      refine ⟨36683475200578720591996297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48911300267438294122661729 36683475200578720591996297)
      ·
        refine ⟨27512606400434040443997223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36683475200578720591996297 27512606400434040443997223)
        ·
          refine ⟨41268909600651060665995835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27512606400434040443997223 41268909600651060665995835)
          ·
            refine ⟨61903364400976590998993753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41268909600651060665995835 61903364400976590998993753)
            ·
              refine ⟨46427523300732443249245315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61903364400976590998993753 46427523300732443249245315)
              ·
                refine ⟨69641284951098664873867973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46427523300732443249245315 69641284951098664873867973)
                ·
                  refine ⟨13057740928330999663850245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69641284951098664873867973 13057740928330999663850245)
                  ·
                    refine ⟨2448326424062062436971921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13057740928330999663850245 2448326424062062436971921)
                    ·
                      refine ⟨1836244818046546827728941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448326424062062436971921 1836244818046546827728941)
                      ·
                        rfl

theorem cell23_3576074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_3576074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576074 prefixEnd_3576074 := by exact prefixLift 3576074
  have htrace : WordTrace (prefixWord ++ tailWord_3576074) baseStart_3576074 baseEnd_3576074 := by
    simpa [prefixWord, tailWord_3576074, baseEnd_3576074] using wordTrace_append hprefix tailTrace_3576074
  have hstable : (prefixWord ++ tailWord_3576074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576074).length < 2 ^ (prefixWord ++ tailWord_3576074).sum := by decide
  have hdescent : baseEnd_3576074 < baseStart_3576074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576164 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3576164 : Nat := 118140960795 + 3576164 * 2 ^ 59
def prefixEnd_3576164 : Nat := 4983230072969 + 3 ^ 40 * 3576164 * 2
def baseEnd_3576164 : Nat := 1836291031305451475603527

theorem tailTrace_3576164 : CollatzResearch.WordTrace tailWord_3576164 prefixEnd_3576164 1836291031305451475603527 := by
  unfold tailWord_3576164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65216708308088031515603773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86955611077450708687471697 65216708308088031515603773)
  ·
    refine ⟨24456265615533011818351415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65216708308088031515603773 24456265615533011818351415)
    ·
      refine ⟨36684398423299517727527123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456265615533011818351415 36684398423299517727527123)
      ·
        refine ⟨55026597634949276591290685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36684398423299517727527123 55026597634949276591290685)
        ·
          refine ⟨20634974113105978721734007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55026597634949276591290685 20634974113105978721734007)
          ·
            refine ⟨30952461169658968082601011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20634974113105978721734007 30952461169658968082601011)
            ·
              refine ⟨46428691754488452123901517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30952461169658968082601011 46428691754488452123901517)
              ·
                refine ⟨17410759407933169546463069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46428691754488452123901517 17410759407933169546463069)
                ·
                  refine ⟨6529034777974938579923651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17410759407933169546463069 6529034777974938579923651)
                  ·
                    refine ⟨9793552166962407869885477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6529034777974938579923651 9793552166962407869885477)
                    ·
                      refine ⟨1836291031305451475603527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9793552166962407869885477 1836291031305451475603527)
                      ·
                        rfl

theorem cell23_3576164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3576164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576164 prefixEnd_3576164 := by exact prefixLift 3576164
  have htrace : WordTrace (prefixWord ++ tailWord_3576164) baseStart_3576164 baseEnd_3576164 := by
    simpa [prefixWord, tailWord_3576164, baseEnd_3576164] using wordTrace_append hprefix tailTrace_3576164
  have hstable : (prefixWord ++ tailWord_3576164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576164).length < 2 ^ (prefixWord ++ tailWord_3576164).sum := by decide
  have hdescent : baseEnd_3576164 < baseStart_3576164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576168 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3576168 : Nat := 118140960795 + 3576168 * 2 ^ 59
def prefixEnd_3576168 : Nat := 4983230072969 + 3 ^ 40 * 3576168 * 2
def baseEnd_3576168 : Nat := 1836293085228069459953509

theorem tailTrace_3576168 : CollatzResearch.WordTrace tailWord_3576168 prefixEnd_3576168 1836293085228069459953509 := by
  unfold tailWord_3576168
  simp only [CollatzResearch.WordTrace]
  refine ⟨65216781254080785857176579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86955708338774381142902105 65216781254080785857176579)
  ·
    refine ⟨97825171881121178785764869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65216781254080785857176579 97825171881121178785764869)
    ·
      refine ⟨18342219727710221022330913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97825171881121178785764869 18342219727710221022330913)
      ·
        refine ⟨13756664795782665766748185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18342219727710221022330913 13756664795782665766748185)
        ·
          refine ⟨10317498596836999325061139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13756664795782665766748185 10317498596836999325061139)
          ·
            refine ⟨15476247895255498987591709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10317498596836999325061139 15476247895255498987591709)
            ·
              refine ⟨5803592960720812120346891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15476247895255498987591709 5803592960720812120346891)
              ·
                refine ⟨8705389441081218180520337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803592960720812120346891 8705389441081218180520337)
                ·
                  refine ⟨6529042080810913635390253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705389441081218180520337 6529042080810913635390253)
                  ·
                    refine ⟨2448390780304092613271345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6529042080810913635390253 2448390780304092613271345)
                    ·
                      refine ⟨1836293085228069459953509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448390780304092613271345 1836293085228069459953509)
                      ·
                        rfl

theorem cell23_3576168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3576168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576168 prefixEnd_3576168 := by exact prefixLift 3576168
  have htrace : WordTrace (prefixWord ++ tailWord_3576168) baseStart_3576168 baseEnd_3576168 := by
    simpa [prefixWord, tailWord_3576168, baseEnd_3576168] using wordTrace_append hprefix tailTrace_3576168
  have hstable : (prefixWord ++ tailWord_3576168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576168).length < 2 ^ (prefixWord ++ tailWord_3576168).sum := by decide
  have hdescent : baseEnd_3576168 < baseStart_3576168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576177 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3576177 : Nat := 118140960795 + 3576177 * 2 ^ 59
def prefixEnd_3576177 : Nat := 4983230072969 + 3 ^ 40 * 3576177 * 2
def baseEnd_3576177 : Nat := 1836297706553959924740967

theorem tailTrace_3576177 : CollatzResearch.WordTrace tailWord_3576177 prefixEnd_3576177 1836297706553959924740967 := by
  unfold tailWord_3576177
  simp only [CollatzResearch.WordTrace]
  refine ⟨130433890765128966251430785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86955927176752644167620523 130433890765128966251430785)
  ·
    refine ⟨97825418073846724688573089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130433890765128966251430785 97825418073846724688573089)
    ·
      refine ⟨73369063555385043516429817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97825418073846724688573089 73369063555385043516429817)
      ·
        refine ⟨55026797666538782637322363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73369063555385043516429817 55026797666538782637322363)
        ·
          refine ⟨82540196499808173955983545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55026797666538782637322363 82540196499808173955983545)
          ·
            refine ⟨61905147374856130466987659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82540196499808173955983545 61905147374856130466987659)
            ·
              refine ⟨92857721062284195700481489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61905147374856130466987659 92857721062284195700481489)
              ·
                refine ⟨69643290796713146775361117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92857721062284195700481489 69643290796713146775361117)
                ·
                  refine ⟨26116234048767430040760419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69643290796713146775361117 26116234048767430040760419)
                  ·
                    refine ⟨39174351073151145061140629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26116234048767430040760419 39174351073151145061140629)
                    ·
                      refine ⟨1836297706553959924740967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39174351073151145061140629 1836297706553959924740967)
                      ·
                        rfl

theorem cell23_3576177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3576177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576177 prefixEnd_3576177 := by exact prefixLift 3576177
  have htrace : WordTrace (prefixWord ++ tailWord_3576177) baseStart_3576177 baseEnd_3576177 := by
    simpa [prefixWord, tailWord_3576177, baseEnd_3576177] using wordTrace_append hprefix tailTrace_3576177
  have hstable : (prefixWord ++ tailWord_3576177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576177).length < 2 ^ (prefixWord ++ tailWord_3576177).sum := by decide
  have hdescent : baseEnd_3576177 < baseStart_3576177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576178 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3576178 : Nat := 118140960795 + 3576178 * 2 ^ 59
def prefixEnd_3576178 : Nat := 4983230072969 + 3 ^ 40 * 3576178 * 2
def baseEnd_3576178 : Nat := 612099406678204806942821

theorem tailTrace_3576178 : CollatzResearch.WordTrace tailWord_3576178 prefixEnd_3576178 612099406678204806942821 := by
  unfold tailWord_3576178
  simp only [CollatzResearch.WordTrace]
  refine ⟨32608481809531335855554297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86955951492083562281478125 32608481809531335855554297)
  ·
    refine ⟨24456361357148501891665723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32608481809531335855554297 24456361357148501891665723)
    ·
      refine ⟨36684542035722752837498585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456361357148501891665723 36684542035722752837498585)
      ·
        refine ⟨27513406526792064628123939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36684542035722752837498585 27513406526792064628123939)
        ·
          refine ⟨41270109790188096942185909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27513406526792064628123939 41270109790188096942185909)
          ·
            refine ⟨3869072792830134088329929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41270109790188096942185909 3869072792830134088329929)
            ·
              refine ⟨2901804594622600566247447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869072792830134088329929 2901804594622600566247447)
              ·
                refine ⟨4352706891933900849371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901804594622600566247447 4352706891933900849371171)
                ·
                  refine ⟨6529060337900851274056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352706891933900849371171 6529060337900851274056757)
                  ·
                    refine ⟨612099406678204806942821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6529060337900851274056757 612099406678204806942821)
                    ·
                      rfl

theorem cell23_3576178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3576178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576178 prefixEnd_3576178 := by exact prefixLift 3576178
  have htrace : WordTrace (prefixWord ++ tailWord_3576178) baseStart_3576178 baseEnd_3576178 := by
    simpa [prefixWord, tailWord_3576178, baseEnd_3576178] using wordTrace_append hprefix tailTrace_3576178
  have hstable : (prefixWord ++ tailWord_3576178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576178).length < 2 ^ (prefixWord ++ tailWord_3576178).sum := by decide
  have hdescent : baseEnd_3576178 < baseStart_3576178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576187 : List Nat := [1, 1, 1, 1, 1, 8, 10]
def baseStart_3576187 : Nat := 118140960795 + 3576187 * 2 ^ 59
def prefixEnd_3576187 : Nat := 4983230072969 + 3 ^ 40 * 3576187 * 2
def baseEnd_3576187 : Nat := 22670405448895122044641

theorem tailTrace_3576187 : CollatzResearch.WordTrace tailWord_3576187 prefixEnd_3576187 22670405448895122044641 := by
  unfold tailWord_3576187
  simp only [CollatzResearch.WordTrace]
  refine ⟨130434255495092737959294815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86956170330061825306196543 130434255495092737959294815)
  ·
    refine ⟨195651383242639106938942223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130434255495092737959294815 195651383242639106938942223)
    ·
      refine ⟨293477074863958660408413335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195651383242639106938942223 293477074863958660408413335)
      ·
        refine ⟨440215612295937990612620003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293477074863958660408413335 440215612295937990612620003)
        ·
          refine ⟨660323418443906985918930005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440215612295937990612620003 660323418443906985918930005)
          ·
            refine ⟨7738165059889534991237461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 660323418443906985918930005 7738165059889534991237461)
            ·
              refine ⟨22670405448895122044641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7738165059889534991237461 22670405448895122044641)
              ·
                rfl

theorem cell23_3576187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 10].length) (baseStart_3576187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576187 prefixEnd_3576187 := by exact prefixLift 3576187
  have htrace : WordTrace (prefixWord ++ tailWord_3576187) baseStart_3576187 baseEnd_3576187 := by
    simpa [prefixWord, tailWord_3576187, baseEnd_3576187] using wordTrace_append hprefix tailTrace_3576187
  have hstable : (prefixWord ++ tailWord_3576187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576187).length < 2 ^ (prefixWord ++ tailWord_3576187).sum := by decide
  have hdescent : baseEnd_3576187 < baseStart_3576187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3576197 : Nat := 118140960795 + 3576197 * 2 ^ 59
def prefixEnd_3576197 : Nat := 4983230072969 + 3 ^ 40 * 3576197 * 2
def baseEnd_3576197 : Nat := 1836307976167049846490875

theorem tailTrace_3576197 : CollatzResearch.WordTrace tailWord_3576197 prefixEnd_3576197 1836307976167049846490875 := by
  unfold tailWord_3576197
  simp only [CollatzResearch.WordTrace]
  refine ⟨130434620225056509667158845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86956413483371006444772563 130434620225056509667158845)
  ·
    refine ⟨48912982584396191125184567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130434620225056509667158845 48912982584396191125184567)
    ·
      refine ⟨73369473876594286687776851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48912982584396191125184567 73369473876594286687776851)
      ·
        refine ⟨110054210814891430031665277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73369473876594286687776851 110054210814891430031665277)
        ·
          refine ⟨41270329055584286261874479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110054210814891430031665277 41270329055584286261874479)
          ·
            refine ⟨61905493583376429392811719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41270329055584286261874479 61905493583376429392811719)
            ·
              refine ⟨92858240375064644089217579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61905493583376429392811719 92858240375064644089217579)
              ·
                refine ⟨139287360562596966133826369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92858240375064644089217579 139287360562596966133826369)
                ·
                  refine ⟨104465520421947724600369777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139287360562596966133826369 104465520421947724600369777)
                  ·
                    refine ⟨78349140316460793450277333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104465520421947724600369777 78349140316460793450277333)
                    ·
                      refine ⟨1836307976167049846490875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78349140316460793450277333 1836307976167049846490875)
                      ·
                        rfl

theorem cell23_3576197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3576197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576197 prefixEnd_3576197 := by exact prefixLift 3576197
  have htrace : WordTrace (prefixWord ++ tailWord_3576197) baseStart_3576197 baseEnd_3576197 := by
    simpa [prefixWord, tailWord_3576197, baseEnd_3576197] using wordTrace_append hprefix tailTrace_3576197
  have hstable : (prefixWord ++ tailWord_3576197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576197).length < 2 ^ (prefixWord ++ tailWord_3576197).sum := by decide
  have hdescent : baseEnd_3576197 < baseStart_3576197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576218 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3576218 : Nat := 118140960795 + 3576218 * 2 ^ 59
def prefixEnd_3576218 : Nat := 4983230072969 + 3 ^ 40 * 3576218 * 2
def baseEnd_3576218 : Nat := 1836318759260794264328279

theorem tailTrace_3576218 : CollatzResearch.WordTrace tailWord_3576218 prefixEnd_3576218 1836318759260794264328279 := by
  unfold tailWord_3576218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32608846539495107563418327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86956924105320286835782205 32608846539495107563418327)
  ·
    refine ⟨48913269809242661345127491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32608846539495107563418327 48913269809242661345127491)
    ·
      refine ⟨73369904713863992017691237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48913269809242661345127491 73369904713863992017691237)
      ·
        refine ⟨13756857133849498503317107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73369904713863992017691237 13756857133849498503317107)
        ·
          refine ⟨20635285700774247754975661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13756857133849498503317107 20635285700774247754975661)
          ·
            refine ⟨7738232137790342908115873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20635285700774247754975661 7738232137790342908115873)
            ·
              refine ⟨5803674103342757181086905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7738232137790342908115873 5803674103342757181086905)
              ·
                refine ⟨4352755577507067885815179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803674103342757181086905 4352755577507067885815179)
                ·
                  refine ⟨6529133366260601828722769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352755577507067885815179 6529133366260601828722769)
                  ·
                    refine ⟨4896850024695451371542077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529133366260601828722769 4896850024695451371542077)
                    ·
                      refine ⟨1836318759260794264328279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896850024695451371542077 1836318759260794264328279)
                      ·
                        rfl

theorem cell23_3576218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3576218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576218 prefixEnd_3576218 := by exact prefixLift 3576218
  have htrace : WordTrace (prefixWord ++ tailWord_3576218) baseStart_3576218 baseEnd_3576218 := by
    simpa [prefixWord, tailWord_3576218, baseEnd_3576218] using wordTrace_append hprefix tailTrace_3576218
  have hstable : (prefixWord ++ tailWord_3576218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576218).length < 2 ^ (prefixWord ++ tailWord_3576218).sum := by decide
  have hdescent : baseEnd_3576218 < baseStart_3576218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576271 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 4, 2]
def baseStart_3576271 : Nat := 118140960795 + 3576271 * 2 ^ 59
def prefixEnd_3576271 : Nat := 4983230072969 + 3 ^ 40 * 3576271 * 2
def baseEnd_3576271 : Nat := 1836345973735482556965535

theorem tailTrace_3576271 : CollatzResearch.WordTrace tailWord_3576271 prefixEnd_3576271 1836345973735482556965535 := by
  unfold tailWord_3576271
  simp only [CollatzResearch.WordTrace]
  refine ⟨130437319226788420305352667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86958212817858946870235111 130437319226788420305352667)
  ·
    refine ⟨195655978840182630458029001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130437319226788420305352667 195655978840182630458029001)
    ·
      refine ⟨146741984130136972843521751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195655978840182630458029001 146741984130136972843521751)
      ·
        refine ⟨220112976195205459265282627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146741984130136972843521751 220112976195205459265282627)
        ·
          refine ⟨330169464292808188897923941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220112976195205459265282627 330169464292808188897923941)
          ·
            refine ⟨61906774554901535418360739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330169464292808188897923941 61906774554901535418360739)
            ·
              refine ⟨92860161832352303127541109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61906774554901535418360739 92860161832352303127541109)
              ·
                refine ⟨8705640171783028418206979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92860161832352303127541109 8705640171783028418206979)
                ·
                  refine ⟨13058460257674542627310469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8705640171783028418206979 13058460257674542627310469)
                  ·
                    refine ⟨2448461298313976742620713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13058460257674542627310469 2448461298313976742620713)
                    ·
                      refine ⟨1836345973735482556965535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448461298313976742620713 1836345973735482556965535)
                      ·
                        rfl

theorem cell23_3576271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4, 2].length) (baseStart_3576271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576271 prefixEnd_3576271 := by exact prefixLift 3576271
  have htrace : WordTrace (prefixWord ++ tailWord_3576271) baseStart_3576271 baseEnd_3576271 := by
    simpa [prefixWord, tailWord_3576271, baseEnd_3576271] using wordTrace_append hprefix tailTrace_3576271
  have hstable : (prefixWord ++ tailWord_3576271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576271).length < 2 ^ (prefixWord ++ tailWord_3576271).sum := by decide
  have hdescent : baseEnd_3576271 < baseStart_3576271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576305 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_3576305 : Nat := 118140960795 + 3576305 * 2 ^ 59
def prefixEnd_3576305 : Nat := 4983230072969 + 3 ^ 40 * 3576305 * 2
def baseEnd_3576305 : Nat := 1836363432077735423940379

theorem tailTrace_3576305 : CollatzResearch.WordTrace tailWord_3576305 prefixEnd_3576305 1836363432077735423940379 := by
  unfold tailWord_3576305
  simp only [CollatzResearch.WordTrace]
  refine ⟨130438559308665244112090369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86959039539110162741393579 130438559308665244112090369)
  ·
    refine ⟨97828919481498933084067777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130438559308665244112090369 97828919481498933084067777)
    ·
      refine ⟨73371689611124199813050833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97828919481498933084067777 73371689611124199813050833)
      ·
        refine ⟨55028767208343149859788125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73371689611124199813050833 55028767208343149859788125)
        ·
          refine ⟨20635787703128681197420547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55028767208343149859788125 20635787703128681197420547)
          ·
            refine ⟨30953681554693021796130821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20635787703128681197420547 30953681554693021796130821)
            ·
              refine ⟨5803815291504941586774529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30953681554693021796130821 5803815291504941586774529)
              ·
                refine ⟨4352861468628706190080897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803815291504941586774529 4352861468628706190080897)
                ·
                  refine ⟨3264646101471529642560673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352861468628706190080897 3264646101471529642560673)
                  ·
                    refine ⟨2448484576103647231920505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264646101471529642560673 2448484576103647231920505)
                    ·
                      refine ⟨1836363432077735423940379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448484576103647231920505 1836363432077735423940379)
                      ·
                        rfl

theorem cell23_3576305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_3576305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576305 prefixEnd_3576305 := by exact prefixLift 3576305
  have htrace : WordTrace (prefixWord ++ tailWord_3576305) baseStart_3576305 baseEnd_3576305 := by
    simpa [prefixWord, tailWord_3576305, baseEnd_3576305] using wordTrace_append hprefix tailTrace_3576305
  have hstable : (prefixWord ++ tailWord_3576305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576305).length < 2 ^ (prefixWord ++ tailWord_3576305).sum := by decide
  have hdescent : baseEnd_3576305 < baseStart_3576305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576321 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_3576321 : Nat := 118140960795 + 3576321 * 2 ^ 59
def prefixEnd_3576321 : Nat := 4983230072969 + 3 ^ 40 * 3576321 * 2
def baseEnd_3576321 : Nat := 1836371647768207361340305

theorem tailTrace_3576321 : CollatzResearch.WordTrace tailWord_3576321 prefixEnd_3576321 1836371647768207361340305 := by
  unfold tailWord_3576321
  simp only [CollatzResearch.WordTrace]
  refine ⟨130439142876607278844672817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86959428584404852563115211 130439142876607278844672817)
  ·
    refine ⟨97829357157455459133504613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130439142876607278844672817 97829357157455459133504613)
    ·
      refine ⟨18343004467022898587532115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97829357157455459133504613 18343004467022898587532115)
      ·
        refine ⟨27514506700534347881298173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343004467022898587532115 27514506700534347881298173)
        ·
          refine ⟨10317940012700380455486815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27514506700534347881298173 10317940012700380455486815)
          ·
            refine ⟨15476910019050570683230223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10317940012700380455486815 15476910019050570683230223)
            ·
              refine ⟨23215365028575856024845335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15476910019050570683230223 23215365028575856024845335)
              ·
                refine ⟨34823047542863784037268003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23215365028575856024845335 34823047542863784037268003)
                ·
                  refine ⟨52234571314295676055902005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34823047542863784037268003 52234571314295676055902005)
                  ·
                    refine ⟨4896991060715219630240813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52234571314295676055902005 4896991060715219630240813)
                    ·
                      refine ⟨1836371647768207361340305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4896991060715219630240813 1836371647768207361340305)
                      ·
                        rfl

theorem cell23_3576321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_3576321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576321 prefixEnd_3576321 := by exact prefixLift 3576321
  have htrace : WordTrace (prefixWord ++ tailWord_3576321) baseStart_3576321 baseEnd_3576321 := by
    simpa [prefixWord, tailWord_3576321, baseEnd_3576321] using wordTrace_append hprefix tailTrace_3576321
  have hstable : (prefixWord ++ tailWord_3576321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576321).length < 2 ^ (prefixWord ++ tailWord_3576321).sum := by decide
  have hdescent : baseEnd_3576321 < baseStart_3576321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576322 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3576322 : Nat := 118140960795 + 3576322 * 2 ^ 59
def prefixEnd_3576322 : Nat := 4983230072969 + 3 ^ 40 * 3576322 * 2
def baseEnd_3576322 : Nat := 1836372161248861857427801

theorem tailTrace_3576322 : CollatzResearch.WordTrace tailWord_3576322 prefixEnd_3576322 1836372161248861857427801 := by
  unfold tailWord_3576322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32609794837400914003864805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86959452899735770676972813 32609794837400914003864805)
  ·
    refine ⟨6114336532012671375724651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32609794837400914003864805 6114336532012671375724651)
    ·
      refine ⟨9171504798019007063586977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6114336532012671375724651 9171504798019007063586977)
      ·
        refine ⟨6878628598514255297690233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9171504798019007063586977 6878628598514255297690233)
        ·
          refine ⟨5158971448885691473267675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6878628598514255297690233 5158971448885691473267675)
          ·
            refine ⟨7738457173328537209901513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158971448885691473267675 7738457173328537209901513)
            ·
              refine ⟨5803842879996402907426135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7738457173328537209901513 5803842879996402907426135)
              ·
                refine ⟨8705764319994604361139203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803842879996402907426135 8705764319994604361139203)
                ·
                  refine ⟨13058646479991906541708805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8705764319994604361139203 13058646479991906541708805)
                  ·
                    refine ⟨2448496214998482476570401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13058646479991906541708805 2448496214998482476570401)
                    ·
                      refine ⟨1836372161248861857427801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448496214998482476570401 1836372161248861857427801)
                      ·
                        rfl

theorem cell23_3576322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3576322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576322 prefixEnd_3576322 := by exact prefixLift 3576322
  have htrace : WordTrace (prefixWord ++ tailWord_3576322) baseStart_3576322 baseEnd_3576322 := by
    simpa [prefixWord, tailWord_3576322, baseEnd_3576322] using wordTrace_append hprefix tailTrace_3576322
  have hstable : (prefixWord ++ tailWord_3576322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576322).length < 2 ^ (prefixWord ++ tailWord_3576322).sum := by decide
  have hdescent : baseEnd_3576322 < baseStart_3576322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576356 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3576356 : Nat := 118140960795 + 3576356 * 2 ^ 59
def prefixEnd_3576356 : Nat := 4983230072969 + 3 ^ 40 * 3576356 * 2
def baseEnd_3576356 : Nat := 1836389619591114724402645

theorem tailTrace_3576356 : CollatzResearch.WordTrace tailWord_3576356 prefixEnd_3576356 1836389619591114724402645 := by
  unfold tailWord_3576356
  simp only [CollatzResearch.WordTrace]
  refine ⟨65220209715740239911098461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86960279620986986548131281 65220209715740239911098461)
  ·
    refine ⟨24457578643402589966661923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65220209715740239911098461 24457578643402589966661923)
    ·
      refine ⟨36686367965103884949992885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24457578643402589966661923 36686367965103884949992885)
      ·
        refine ⟨3439346996728489214061833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36686367965103884949992885 3439346996728489214061833)
        ·
          refine ⟨2579510247546366910546375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439346996728489214061833 2579510247546366910546375)
          ·
            refine ⟨3869265371319550365819563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579510247546366910546375 3869265371319550365819563)
            ·
              refine ⟨5803898056979325548729345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869265371319550365819563 5803898056979325548729345)
              ·
                refine ⟨4352923542734494161547009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803898056979325548729345 4352923542734494161547009)
                ·
                  refine ⟨3264692657050870621160257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352923542734494161547009 3264692657050870621160257)
                  ·
                    refine ⟨2448519492788152965870193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264692657050870621160257 2448519492788152965870193)
                    ·
                      refine ⟨1836389619591114724402645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448519492788152965870193 1836389619591114724402645)
                      ·
                        rfl

theorem cell23_3576356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3576356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576356 prefixEnd_3576356 := by exact prefixLift 3576356
  have htrace : WordTrace (prefixWord ++ tailWord_3576356) baseStart_3576356 baseEnd_3576356 := by
    simpa [prefixWord, tailWord_3576356, baseEnd_3576356] using wordTrace_append hprefix tailTrace_3576356
  have hstable : (prefixWord ++ tailWord_3576356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576356).length < 2 ^ (prefixWord ++ tailWord_3576356).sum := by decide
  have hdescent : baseEnd_3576356 < baseStart_3576356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576364 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3576364 : Nat := 118140960795 + 3576364 * 2 ^ 59
def prefixEnd_3576364 : Nat := 4983230072969 + 3 ^ 40 * 3576364 * 2
def baseEnd_3576364 : Nat := 1836393727436350693102607

theorem tailTrace_3576364 : CollatzResearch.WordTrace tailWord_3576364 prefixEnd_3576364 1836393727436350693102607 := by
  unfold tailWord_3576364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65220355607725748594244073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86960474143634331458992097 65220355607725748594244073)
  ·
    refine ⟨48915266705794311445683055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65220355607725748594244073 48915266705794311445683055)
    ·
      refine ⟨73372900058691467168524583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48915266705794311445683055 73372900058691467168524583)
      ·
        refine ⟨110059350088037200752786875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73372900058691467168524583 110059350088037200752786875)
        ·
          refine ⟨165089025132055801129180313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110059350088037200752786875 165089025132055801129180313)
          ·
            refine ⟨123816768849041850846885235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165089025132055801129180313 123816768849041850846885235)
            ·
              refine ⟨185725153273562776270327853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123816768849041850846885235 185725153273562776270327853)
              ·
                refine ⟨69646932477586041101372945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185725153273562776270327853 69646932477586041101372945)
                ·
                  refine ⟨52235199358189530826029709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69646932477586041101372945 52235199358189530826029709)
                  ·
                    refine ⟨19588199759321074059761141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52235199358189530826029709 19588199759321074059761141)
                    ·
                      refine ⟨1836393727436350693102607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19588199759321074059761141 1836393727436350693102607)
                      ·
                        rfl

theorem cell23_3576364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3576364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576364 prefixEnd_3576364 := by exact prefixLift 3576364
  have htrace : WordTrace (prefixWord ++ tailWord_3576364) baseStart_3576364 baseEnd_3576364 := by
    simpa [prefixWord, tailWord_3576364, baseEnd_3576364] using wordTrace_append hprefix tailTrace_3576364
  have hstable : (prefixWord ++ tailWord_3576364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576364).length < 2 ^ (prefixWord ++ tailWord_3576364).sum := by decide
  have hdescent : baseEnd_3576364 < baseStart_3576364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576378 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_3576378 : Nat := 118140960795 + 3576378 * 2 ^ 59
def prefixEnd_3576378 : Nat := 4983230072969 + 3 ^ 40 * 3576378 * 2
def baseEnd_3576378 : Nat := 1836400916165513638327543

theorem tailTrace_3576378 : CollatzResearch.WordTrace tailWord_3576378 prefixEnd_3576378 1836400916165513638327543 := by
  unfold tailWord_3576378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32610305459350194394874447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86960814558267185052998525 32610305459350194394874447)
  ·
    refine ⟨48915458189025291592311671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32610305459350194394874447 48915458189025291592311671)
    ·
      refine ⟨73373187283537937388467507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48915458189025291592311671 73373187283537937388467507)
      ·
        refine ⟨110059780925306906082701261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73373187283537937388467507 110059780925306906082701261)
        ·
          refine ⟨41272417846990089781012973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110059780925306906082701261 41272417846990089781012973)
          ·
            refine ⟨15477156692621283667879865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41272417846990089781012973 15477156692621283667879865)
            ·
              refine ⟨11607867519465962750909899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15477156692621283667879865 11607867519465962750909899)
              ·
                refine ⟨17411801279198944126364849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11607867519465962750909899 17411801279198944126364849)
                ·
                  refine ⟨13058850959399208094773637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17411801279198944126364849 13058850959399208094773637)
                  ·
                    refine ⟨2448534554887351517770057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13058850959399208094773637 2448534554887351517770057)
                    ·
                      refine ⟨1836400916165513638327543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448534554887351517770057 1836400916165513638327543)
                      ·
                        rfl

theorem cell23_3576378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_3576378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576378 prefixEnd_3576378 := by exact prefixLift 3576378
  have htrace : WordTrace (prefixWord ++ tailWord_3576378) baseStart_3576378 baseEnd_3576378 := by
    simpa [prefixWord, tailWord_3576378, baseEnd_3576378] using wordTrace_append hprefix tailTrace_3576378
  have hstable : (prefixWord ++ tailWord_3576378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576378).length < 2 ^ (prefixWord ++ tailWord_3576378).sum := by decide
  have hdescent : baseEnd_3576378 < baseStart_3576378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576405 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3576405 : Nat := 118140960795 + 3576405 * 2 ^ 59
def prefixEnd_3576405 : Nat := 4983230072969 + 3 ^ 40 * 3576405 * 2
def baseEnd_3576405 : Nat := 612138260047728344229973

theorem tailTrace_3576405 : CollatzResearch.WordTrace tailWord_3576405 prefixEnd_3576405 612138260047728344229973 := by
  unfold tailWord_3576405
  simp only [CollatzResearch.WordTrace]
  refine ⟨130442206608302961190730669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86961471072201974127153779 130442206608302961190730669)
  ·
    refine ⟨48915827478113610446524001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130442206608302961190730669 48915827478113610446524001)
    ·
      refine ⟨36686870608585207834893001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48915827478113610446524001 36686870608585207834893001)
      ·
        refine ⟨27515152956438905876169751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36686870608585207834893001 27515152956438905876169751)
        ·
          refine ⟨41272729434658358814254627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515152956438905876169751 41272729434658358814254627)
          ·
            refine ⟨61909094151987538221381941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41272729434658358814254627 61909094151987538221381941)
            ·
              refine ⟨5803977576748831708254557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61909094151987538221381941 5803977576748831708254557)
              ·
                refine ⟨2176491591280811890595459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5803977576748831708254557 2176491591280811890595459)
                ·
                  refine ⟨3264737386921217835893189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176491591280811890595459 3264737386921217835893189)
                  ·
                    refine ⟨612138260047728344229973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264737386921217835893189 612138260047728344229973)
                    ·
                      rfl

theorem cell23_3576405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3576405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576405 prefixEnd_3576405 := by exact prefixLift 3576405
  have htrace : WordTrace (prefixWord ++ tailWord_3576405) baseStart_3576405 baseEnd_3576405 := by
    simpa [prefixWord, tailWord_3576405, baseEnd_3576405] using wordTrace_append hprefix tailTrace_3576405
  have hstable : (prefixWord ++ tailWord_3576405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576405).length < 2 ^ (prefixWord ++ tailWord_3576405).sum := by decide
  have hdescent : baseEnd_3576405 < baseStart_3576405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576448 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_3576448 : Nat := 118140960795 + 3576448 * 2 ^ 59
def prefixEnd_3576448 : Nat := 4983230072969 + 3 ^ 40 * 3576448 * 2
def baseEnd_3576448 : Nat := 612145619937109454817407

theorem tailTrace_3576448 : CollatzResearch.WordTrace tailWord_3576448 prefixEnd_3576448 612145619937109454817407 := by
  unfold tailWord_3576448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65221887473573589767272999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86962516631431453023030665 65221887473573589767272999)
  ·
    refine ⟨97832831210360384650909499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65221887473573589767272999 97832831210360384650909499)
    ·
      refine ⟨146749246815540576976364249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97832831210360384650909499 146749246815540576976364249)
      ·
        refine ⟨110061935111655432732273187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146749246815540576976364249 110061935111655432732273187)
        ·
          refine ⟨165092902667483149098409781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110061935111655432732273187 165092902667483149098409781)
          ·
            refine ⟨15477459625076545227975917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165092902667483149098409781 15477459625076545227975917)
            ·
              refine ⟨5804047359403704460490969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15477459625076545227975917 5804047359403704460490969)
              ·
                refine ⟨4353035519552778345368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5804047359403704460490969 4353035519552778345368227)
                ·
                  refine ⟨6529553279329167518052341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353035519552778345368227 6529553279329167518052341)
                  ·
                    refine ⟨612145619937109454817407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6529553279329167518052341 612145619937109454817407)
                    ·
                      rfl

theorem cell23_3576448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_3576448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576448 prefixEnd_3576448 := by exact prefixLift 3576448
  have htrace : WordTrace (prefixWord ++ tailWord_3576448) baseStart_3576448 baseEnd_3576448 := by
    simpa [prefixWord, tailWord_3576448, baseEnd_3576448] using wordTrace_append hprefix tailTrace_3576448
  have hstable : (prefixWord ++ tailWord_3576448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576448).length < 2 ^ (prefixWord ++ tailWord_3576448).sum := by decide
  have hdescent : baseEnd_3576448 < baseStart_3576448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576455 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_3576455 : Nat := 118140960795 + 3576455 * 2 ^ 59
def prefixEnd_3576455 : Nat := 4983230072969 + 3 ^ 40 * 3576455 * 2
def baseEnd_3576455 : Nat := 1836440454175909837064689

theorem tailTrace_3576455 : CollatzResearch.WordTrace tailWord_3576455 prefixEnd_3576455 1836440454175909837064689 := by
  unfold tailWord_3576455
  simp only [CollatzResearch.WordTrace]
  refine ⟨130444030258121819730050819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86962686838747879820033879 130444030258121819730050819)
  ·
    refine ⟨195666045387182729595076229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130444030258121819730050819 195666045387182729595076229)
    ·
      refine ⟨36687383510096761799076793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195666045387182729595076229 36687383510096761799076793)
      ·
        refine ⟨27515537632572571349307595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36687383510096761799076793 27515537632572571349307595)
        ·
          refine ⟨41273306448858857023961393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515537632572571349307595 41273306448858857023961393)
          ·
            refine ⟨30954979836644142767971045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41273306448858857023961393 30954979836644142767971045)
            ·
              refine ⟨5804058719370776768994571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30954979836644142767971045 5804058719370776768994571)
              ·
                refine ⟨8706088079056165153491857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804058719370776768994571 8706088079056165153491857)
                ·
                  refine ⟨6529566059292123865118893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8706088079056165153491857 6529566059292123865118893)
                  ·
                    refine ⟨2448587272234546449419585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6529566059292123865118893 2448587272234546449419585)
                    ·
                      refine ⟨1836440454175909837064689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448587272234546449419585 1836440454175909837064689)
                      ·
                        rfl

theorem cell23_3576455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_3576455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576455 prefixEnd_3576455 := by exact prefixLift 3576455
  have htrace : WordTrace (prefixWord ++ tailWord_3576455) baseStart_3576455 baseEnd_3576455 := by
    simpa [prefixWord, tailWord_3576455, baseEnd_3576455] using wordTrace_append hprefix tailTrace_3576455
  have hstable : (prefixWord ++ tailWord_3576455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576455).length < 2 ^ (prefixWord ++ tailWord_3576455).sum := by decide
  have hdescent : baseEnd_3576455 < baseStart_3576455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576462 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3576462 : Nat := 118140960795 + 3576462 * 2 ^ 59
def prefixEnd_3576462 : Nat := 4983230072969 + 3 ^ 40 * 3576462 * 2
def baseEnd_3576462 : Nat := 1836444048540491309677157

theorem tailTrace_3576462 : CollatzResearch.WordTrace tailWord_3576462 prefixEnd_3576462 1836444048540491309677157 := by
  unfold tailWord_3576462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16305535696137057490694455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86962857046064306617037093 16305535696137057490694455)
  ·
    refine ⟨24458303544205586236041683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16305535696137057490694455 24458303544205586236041683)
    ·
      refine ⟨36687455316308379354062525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24458303544205586236041683 36687455316308379354062525)
      ·
        refine ⟨13757795743615642257773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36687455316308379354062525 13757795743615642257773447)
        ·
          refine ⟨20636693615423463386660171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757795743615642257773447 20636693615423463386660171)
          ·
            refine ⟨30955040423135195079990257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636693615423463386660171 30955040423135195079990257)
            ·
              refine ⟨23216280317351396309992693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30955040423135195079990257 23216280317351396309992693)
              ·
                refine ⟨2176526279751693404061815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23216280317351396309992693 2176526279751693404061815)
                ·
                  refine ⟨3264789419627540106092723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176526279751693404061815 3264789419627540106092723)
                  ·
                    refine ⟨4897184129441310159139085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264789419627540106092723 4897184129441310159139085)
                    ·
                      refine ⟨1836444048540491309677157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897184129441310159139085 1836444048540491309677157)
                      ·
                        rfl

theorem cell23_3576462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3576462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576462 prefixEnd_3576462 := by exact prefixLift 3576462
  have htrace : WordTrace (prefixWord ++ tailWord_3576462) baseStart_3576462 baseEnd_3576462 := by
    simpa [prefixWord, tailWord_3576462, baseEnd_3576462] using wordTrace_append hprefix tailTrace_3576462
  have hstable : (prefixWord ++ tailWord_3576462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576462).length < 2 ^ (prefixWord ++ tailWord_3576462).sum := by decide
  have hdescent : baseEnd_3576462 < baseStart_3576462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576478 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3576478 : Nat := 118140960795 + 3576478 * 2 ^ 59
def prefixEnd_3576478 : Nat := 4983230072969 + 3 ^ 40 * 3576478 * 2
def baseEnd_3576478 : Nat := 612150754743654415692361

theorem tailTrace_3576478 : CollatzResearch.WordTrace tailWord_3576478 prefixEnd_3576478 612150754743654415692361 := by
  unfold tailWord_3576478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16305608642129811832267261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86963246091358996438758725 16305608642129811832267261)
  ·
    refine ⟨6114603240798679437100223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16305608642129811832267261 6114603240798679437100223)
    ·
      refine ⟨9171904861198019155650335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6114603240798679437100223 9171904861198019155650335)
      ·
        refine ⟨13757857291797028733475503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9171904861198019155650335 13757857291797028733475503)
        ·
          refine ⟨20636785937695543100213255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757857291797028733475503 20636785937695543100213255)
          ·
            refine ⟨30955178906543314650319883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636785937695543100213255 30955178906543314650319883)
            ·
              refine ⟨46432768359814971975479825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30955178906543314650319883 46432768359814971975479825)
              ·
                refine ⟨34824576269861228981609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46432768359814971975479825 34824576269861228981609869)
                ·
                  refine ⟨13059216101197960868103701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34824576269861228981609869 13059216101197960868103701)
                  ·
                    refine ⟨612150754743654415692361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13059216101197960868103701 612150754743654415692361)
                    ·
                      rfl

theorem cell23_3576478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3576478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576478 prefixEnd_3576478 := by exact prefixLift 3576478
  have htrace : WordTrace (prefixWord ++ tailWord_3576478) baseStart_3576478 baseEnd_3576478 := by
    simpa [prefixWord, tailWord_3576478, baseEnd_3576478] using wordTrace_append hprefix tailTrace_3576478
  have hstable : (prefixWord ++ tailWord_3576478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576478).length < 2 ^ (prefixWord ++ tailWord_3576478).sum := by decide
  have hdescent : baseEnd_3576478 < baseStart_3576478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576485 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_3576485 : Nat := 118140960795 + 3576485 * 2 ^ 59
def prefixEnd_3576485 : Nat := 4983230072969 + 3 ^ 40 * 3576485 * 2
def baseEnd_3576485 : Nat := 1836455858595544719689551

theorem tailTrace_3576485 : CollatzResearch.WordTrace tailWord_3576485 prefixEnd_3576485 1836455858595544719689551 := by
  unfold tailWord_3576485
  simp only [CollatzResearch.WordTrace]
  refine ⟨130445124448013134853642909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86963416298675423235761939 130445124448013134853642909)
  ·
    refine ⟨48916921668004925570116091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130445124448013134853642909 48916921668004925570116091)
    ·
      refine ⟨73375382502007388355174137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48916921668004925570116091 73375382502007388355174137)
      ·
        refine ⟨55031536876505541266380603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73375382502007388355174137 55031536876505541266380603)
        ·
          refine ⟨82547305314758311899570905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55031536876505541266380603 82547305314758311899570905)
          ·
            refine ⟨61910478986068733924678179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82547305314758311899570905 61910478986068733924678179)
            ·
              refine ⟨92865718479103100887017269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61910478986068733924678179 92865718479103100887017269)
              ·
                refine ⟨8706161107415915708157869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92865718479103100887017269 8706161107415915708157869)
                ·
                  refine ⟨3264810415280968390559201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8706161107415915708157869 3264810415280968390559201)
                  ·
                    refine ⟨2448607811460726292919401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3264810415280968390559201 2448607811460726292919401)
                    ·
                      refine ⟨1836455858595544719689551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448607811460726292919401 1836455858595544719689551)
                      ·
                        rfl

theorem cell23_3576485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_3576485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576485 prefixEnd_3576485 := by exact prefixLift 3576485
  have htrace : WordTrace (prefixWord ++ tailWord_3576485) baseStart_3576485 baseEnd_3576485 := by
    simpa [prefixWord, tailWord_3576485, baseEnd_3576485] using wordTrace_append hprefix tailTrace_3576485
  have hstable : (prefixWord ++ tailWord_3576485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576485).length < 2 ^ (prefixWord ++ tailWord_3576485).sum := by decide
  have hdescent : baseEnd_3576485 < baseStart_3576485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576508 : List Nat := [2, 2, 2, 3, 1, 1, 5, 7]
def baseStart_3576508 : Nat := 118140960795 + 3576508 * 2 ^ 59
def prefixEnd_3576508 : Nat := 4983230072969 + 3 ^ 40 * 3576508 * 2
def baseEnd_3576508 : Nat := 68017321061133264063035

theorem tailTrace_3576508 : CollatzResearch.WordTrace tailWord_3576508 prefixEnd_3576508 68017321061133264063035 := by
  unfold tailWord_3576508
  simp only [CollatzResearch.WordTrace]
  refine ⟨65222981663464904890865089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86963975551286539854486785 65222981663464904890865089)
  ·
    refine ⟨48917236247598678668148817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65222981663464904890865089 48917236247598678668148817)
    ·
      refine ⟨36687927185699009001111613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48917236247598678668148817 36687927185699009001111613)
      ·
        refine ⟨13757972694637128375416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36687927185699009001111613 13757972694637128375416855)
        ·
          refine ⟨20636959041955692563125283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757972694637128375416855 20636959041955692563125283)
          ·
            refine ⟨30955438562933538844687925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636959041955692563125283 30955438562933538844687925)
            ·
              refine ⟨2902072365275019266689493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30955438562933538844687925 2902072365275019266689493)
              ·
                refine ⟨68017321061133264063035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2902072365275019266689493 68017321061133264063035)
                ·
                  rfl

theorem cell23_3576508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 7].length) (baseStart_3576508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576508 prefixEnd_3576508 := by exact prefixLift 3576508
  have htrace : WordTrace (prefixWord ++ tailWord_3576508) baseStart_3576508 baseEnd_3576508 := by
    simpa [prefixWord, tailWord_3576508, baseEnd_3576508] using wordTrace_append hprefix tailTrace_3576508
  have hstable : (prefixWord ++ tailWord_3576508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576508).length < 2 ^ (prefixWord ++ tailWord_3576508).sum := by decide
  have hdescent : baseEnd_3576508 < baseStart_3576508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576522 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_3576522 : Nat := 118140960795 + 3576522 * 2 ^ 59
def prefixEnd_3576522 : Nat := 4983230072969 + 3 ^ 40 * 3576522 * 2
def baseEnd_3576522 : Nat := 1836474857379761074926881

theorem tailTrace_3576522 : CollatzResearch.WordTrace tailWord_3576522 prefixEnd_3576522 1836474857379761074926881 := by
  unfold tailWord_3576522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32611618487219772543184955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86964315965919393448493213 32611618487219772543184955)
  ·
    refine ⟨48917427730829658814777433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32611618487219772543184955 48917427730829658814777433)
    ·
      refine ⟨36688070798122244111083075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48917427730829658814777433 36688070798122244111083075)
      ·
        refine ⟨55032106197183366166624613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36688070798122244111083075 55032106197183366166624613)
        ·
          refine ⟨10318519911971881156242115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55032106197183366166624613 10318519911971881156242115)
          ·
            refine ⟨15477779867957821734363173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318519911971881156242115 15477779867957821734363173)
            ·
              refine ⟨2902083725242091575193095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15477779867957821734363173 2902083725242091575193095)
              ·
                refine ⟨4353125587863137362789643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902083725242091575193095 4353125587863137362789643)
                ·
                  refine ⟨6529688381794706044184465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353125587863137362789643 6529688381794706044184465)
                  ·
                    refine ⟨4897266286346029533138349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529688381794706044184465 4897266286346029533138349)
                    ·
                      refine ⟨1836474857379761074926881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897266286346029533138349 1836474857379761074926881)
                      ·
                        rfl

theorem cell23_3576522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_3576522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576522 prefixEnd_3576522 := by exact prefixLift 3576522
  have htrace : WordTrace (prefixWord ++ tailWord_3576522) baseStart_3576522 baseEnd_3576522 := by
    simpa [prefixWord, tailWord_3576522, baseEnd_3576522] using wordTrace_append hprefix tailTrace_3576522
  have hstable : (prefixWord ++ tailWord_3576522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576522).length < 2 ^ (prefixWord ++ tailWord_3576522).sum := by decide
  have hdescent : baseEnd_3576522 < baseStart_3576522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576525 : List Nat := [1, 6, 2, 1, 2, 1, 10]
def baseStart_3576525 : Nat := 118140960795 + 3576525 * 2 ^ 59
def prefixEnd_3576525 : Nat := 4983230072969 + 3 ^ 40 * 3576525 * 2
def baseEnd_3576525 : Nat := 22672548121255858804807

theorem tailTrace_3576525 : CollatzResearch.WordTrace tailWord_3576525 prefixEnd_3576525 22672548121255858804807 := by
  unfold tailWord_3576525
  simp only [CollatzResearch.WordTrace]
  refine ⟨130446583367868221685099029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86964388911912147790066019 130446583367868221685099029)
  ·
    refine ⟨6114683595368822891489017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130446583367868221685099029 6114683595368822891489017)
    ·
      refine ⟨4586012696526617168616763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6114683595368822891489017 4586012696526617168616763)
      ·
        refine ⟨6879019044789925752925145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586012696526617168616763 6879019044789925752925145)
        ·
          refine ⟨5159264283592444314693859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6879019044789925752925145 5159264283592444314693859)
          ·
            refine ⟨7738896425388666472040789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159264283592444314693859 7738896425388666472040789)
            ·
              refine ⟨22672548121255858804807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7738896425388666472040789 22672548121255858804807)
              ·
                rfl

theorem cell23_3576525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 10].length) (baseStart_3576525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576525 prefixEnd_3576525 := by exact prefixLift 3576525
  have htrace : WordTrace (prefixWord ++ tailWord_3576525) baseStart_3576525 baseEnd_3576525 := by
    simpa [prefixWord, tailWord_3576525, baseEnd_3576525] using wordTrace_append hprefix tailTrace_3576525
  have hstable : (prefixWord ++ tailWord_3576525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576525).length < 2 ^ (prefixWord ++ tailWord_3576525).sum := by decide
  have hdescent : baseEnd_3576525 < baseStart_3576525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576535 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_3576535 : Nat := 118140960795 + 3576535 * 2 ^ 59
def prefixEnd_3576535 : Nat := 4983230072969 + 3 ^ 40 * 3576535 * 2
def baseEnd_3576535 : Nat := 1836481532628269524064321

theorem tailTrace_3576535 : CollatzResearch.WordTrace tailWord_3576535 prefixEnd_3576535 1836481532628269524064321 := by
  unfold tailWord_3576535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130446948097831993392963059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86964632065221328928642039 130446948097831993392963059)
  ·
    refine ⟨195670422146747990089444589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130446948097831993392963059 195670422146747990089444589)
    ·
      refine ⟨73376408305030496283541721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195670422146747990089444589 73376408305030496283541721)
      ·
        refine ⟨55032306228772872212656291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73376408305030496283541721 55032306228772872212656291)
        ·
          refine ⟨82548459343159308318984437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55032306228772872212656291 82548459343159308318984437)
          ·
            refine ⟨7738918063421185154904791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82548459343159308318984437 7738918063421185154904791)
            ·
              refine ⟨11608377095131777732357187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738918063421185154904791 11608377095131777732357187)
              ·
                refine ⟨17412565642697666598535781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11608377095131777732357187 17412565642697666598535781)
                ·
                  refine ⟨3264856058005812487225459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17412565642697666598535781 3264856058005812487225459)
                  ·
                    refine ⟨4897284087008718730838189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264856058005812487225459 4897284087008718730838189)
                    ·
                      refine ⟨1836481532628269524064321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897284087008718730838189 1836481532628269524064321)
                      ·
                        rfl

theorem cell23_3576535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_3576535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576535 prefixEnd_3576535 := by exact prefixLift 3576535
  have htrace : WordTrace (prefixWord ++ tailWord_3576535) baseStart_3576535 baseEnd_3576535 := by
    simpa [prefixWord, tailWord_3576535, baseEnd_3576535] using wordTrace_append hprefix tailTrace_3576535
  have hstable : (prefixWord ++ tailWord_3576535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576535).length < 2 ^ (prefixWord ++ tailWord_3576535).sum := by decide
  have hdescent : baseEnd_3576535 < baseStart_3576535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576552 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3576552 : Nat := 118140960795 + 3576552 * 2 ^ 59
def prefixEnd_3576552 : Nat := 4983230072969 + 3 ^ 40 * 3576552 * 2
def baseEnd_3576552 : Nat := 1836490261799395957551743

theorem tailTrace_3576552 : CollatzResearch.WordTrace tailWord_3576552 prefixEnd_3576552 1836490261799395957551743 := by
  unfold tailWord_3576552
  simp only [CollatzResearch.WordTrace]
  refine ⟨65223784069385202648165955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86965045425846936864221273 65223784069385202648165955)
  ·
    refine ⟨97835676104077803972248933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65223784069385202648165955 97835676104077803972248933)
    ·
      refine ⟨18344189269514588244796675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97835676104077803972248933 18344189269514588244796675)
      ·
        refine ⟨27516283904271882367195013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18344189269514588244796675 27516283904271882367195013)
        ·
          refine ⟨5159303232050977943849065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27516283904271882367195013 5159303232050977943849065)
          ·
            refine ⟨3869477424038233457886799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5159303232050977943849065 3869477424038233457886799)
            ·
              refine ⟨5804216136057350186830199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869477424038233457886799 5804216136057350186830199)
              ·
                refine ⟨8706324204086025280245299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804216136057350186830199 8706324204086025280245299)
                ·
                  refine ⟨13059486306129037920367949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706324204086025280245299 13059486306129037920367949)
                  ·
                    refine ⟨4897307364798389220137981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13059486306129037920367949 4897307364798389220137981)
                    ·
                      refine ⟨1836490261799395957551743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897307364798389220137981 1836490261799395957551743)
                      ·
                        rfl

theorem cell23_3576552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3576552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576552 prefixEnd_3576552 := by exact prefixLift 3576552
  have htrace : WordTrace (prefixWord ++ tailWord_3576552) baseStart_3576552 baseEnd_3576552 := by
    simpa [prefixWord, tailWord_3576552, baseEnd_3576552] using wordTrace_append hprefix tailTrace_3576552
  have hstable : (prefixWord ++ tailWord_3576552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576552).length < 2 ^ (prefixWord ++ tailWord_3576552).sum := by decide
  have hdescent : baseEnd_3576552 < baseStart_3576552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576562 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3576562 : Nat := 118140960795 + 3576562 * 2 ^ 59
def prefixEnd_3576562 : Nat := 4983230072969 + 3 ^ 40 * 3576562 * 2
def baseEnd_3576562 : Nat := 1836495396605940918426697

theorem tailTrace_3576562 : CollatzResearch.WordTrace tailWord_3576562 prefixEnd_3576562 1836495396605940918426697 := by
  unfold tailWord_3576562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32611983217183544251048985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86965288579156118002797293 32611983217183544251048985)
  ·
    refine ⟨24458987412887658188286739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32611983217183544251048985 24458987412887658188286739)
    ·
      refine ⟨36688481119331487282430109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24458987412887658188286739 36688481119331487282430109)
      ·
        refine ⟨13758180419749307730911291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36688481119331487282430109 13758180419749307730911291)
        ·
          refine ⟨20637270629623961596366937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13758180419749307730911291 20637270629623961596366937)
          ·
            refine ⟨15477952972217971197275203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20637270629623961596366937 15477952972217971197275203)
            ·
              refine ⟨23216929458326956795912805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15477952972217971197275203 23216929458326956795912805)
              ·
                refine ⟨4353174273436304399233651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23216929458326956795912805 4353174273436304399233651)
                ·
                  refine ⟨6529761410154456598850477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353174273436304399233651 6529761410154456598850477)
                  ·
                    refine ⟨2448660528807921224568929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6529761410154456598850477 2448660528807921224568929)
                    ·
                      refine ⟨1836495396605940918426697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448660528807921224568929 1836495396605940918426697)
                      ·
                        rfl

theorem cell23_3576562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3576562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576562 prefixEnd_3576562 := by exact prefixLift 3576562
  have htrace : WordTrace (prefixWord ++ tailWord_3576562) baseStart_3576562 baseEnd_3576562 := by
    simpa [prefixWord, tailWord_3576562, baseEnd_3576562] using wordTrace_append hprefix tailTrace_3576562
  have hstable : (prefixWord ++ tailWord_3576562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576562).length < 2 ^ (prefixWord ++ tailWord_3576562).sum := by decide
  have hdescent : baseEnd_3576562 < baseStart_3576562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576581 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 9]
def baseStart_3576581 : Nat := 118140960795 + 3576581 * 2 ^ 59
def prefixEnd_3576581 : Nat := 4983230072969 + 3 ^ 40 * 3576581 * 2
def baseEnd_3576581 : Nat := 204056128082041816009901

theorem tailTrace_3576581 : CollatzResearch.WordTrace tailWord_3576581 prefixEnd_3576581 204056128082041816009901 := by
  unfold tailWord_3576581
  simp only [CollatzResearch.WordTrace]
  refine ⟨130448625855665343249137597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86965750570443562166091731 130448625855665343249137597)
  ·
    refine ⟨48918234695874503718426599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130448625855665343249137597 48918234695874503718426599)
    ·
      refine ⟨73377352043811755577639899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48918234695874503718426599 73377352043811755577639899)
      ·
        refine ⟨110066028065717633366459849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73377352043811755577639899 110066028065717633366459849)
        ·
          refine ⟨82549521049288225024844887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110066028065717633366459849 82549521049288225024844887)
          ·
            refine ⟨123824281573932337537267331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82549521049288225024844887 123824281573932337537267331)
            ·
              refine ⟨185736422360898506305900997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123824281573932337537267331 185736422360898506305900997)
              ·
                refine ⟨34825579192668469932356437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185736422360898506305900997 34825579192668469932356437)
                ·
                  refine ⟨204056128082041816009901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34825579192668469932356437 204056128082041816009901)
                  ·
                    rfl

theorem cell23_3576581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_3576581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576581 prefixEnd_3576581 := by exact prefixLift 3576581
  have htrace : WordTrace (prefixWord ++ tailWord_3576581) baseStart_3576581 baseEnd_3576581 := by
    simpa [prefixWord, tailWord_3576581, baseEnd_3576581] using wordTrace_append hprefix tailTrace_3576581
  have hstable : (prefixWord ++ tailWord_3576581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576581).length < 2 ^ (prefixWord ++ tailWord_3576581).sum := by decide
  have hdescent : baseEnd_3576581 < baseStart_3576581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576591 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3576591 : Nat := 118140960795 + 3576591 * 2 ^ 59
def prefixEnd_3576591 : Nat := 4983230072969 + 3 ^ 40 * 3576591 * 2
def baseEnd_3576591 : Nat := 1836510287544921304964063

theorem tailTrace_3576591 : CollatzResearch.WordTrace tailWord_3576591 prefixEnd_3576591 1836510287544921304964063 := by
  unfold tailWord_3576591
  simp only [CollatzResearch.WordTrace]
  refine ⟨130448990585629114957001627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86965993723752743304667751 130448990585629114957001627)
  ·
    refine ⟨195673485878443672435502441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130448990585629114957001627 195673485878443672435502441)
    ·
      refine ⟨146755114408832754326626831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195673485878443672435502441 146755114408832754326626831)
      ·
        refine ⟨220132671613249131489940247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146755114408832754326626831 220132671613249131489940247)
        ·
          refine ⟨330199007419873697234910371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220132671613249131489940247 330199007419873697234910371)
          ·
            refine ⟨495298511129810545852365557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330199007419873697234910371 495298511129810545852365557)
            ·
              refine ⟨46434235418419738673659271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495298511129810545852365557 46434235418419738673659271)
              ·
                refine ⟨69651353127629608010488907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46434235418419738673659271 69651353127629608010488907)
                ·
                  refine ⟨104477029691444412015733361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69651353127629608010488907 104477029691444412015733361)
                  ·
                    refine ⟨78357772268583309011800021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104477029691444412015733361 78357772268583309011800021)
                    ·
                      refine ⟨1836510287544921304964063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78357772268583309011800021 1836510287544921304964063)
                      ·
                        rfl

theorem cell23_3576591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3576591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576591 prefixEnd_3576591 := by exact prefixLift 3576591
  have htrace : WordTrace (prefixWord ++ tailWord_3576591) baseStart_3576591 baseEnd_3576591 := by
    simpa [prefixWord, tailWord_3576591, baseEnd_3576591] using wordTrace_append hprefix tailTrace_3576591
  have hstable : (prefixWord ++ tailWord_3576591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576591).length < 2 ^ (prefixWord ++ tailWord_3576591).sum := by decide
  have hdescent : baseEnd_3576591 < baseStart_3576591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576601 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3576601 : Nat := 118140960795 + 3576601 * 2 ^ 59
def prefixEnd_3576601 : Nat := 4983230072969 + 3 ^ 40 * 3576601 * 2
def baseEnd_3576601 : Nat := 1836515422351466265839017

theorem tailTrace_3576601 : CollatzResearch.WordTrace tailWord_3576601 prefixEnd_3576601 1836515422351466265839017 := by
  unfold tailWord_3576601
  simp only [CollatzResearch.WordTrace]
  refine ⟨130449355315592886664865657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86966236877061924443243771 130449355315592886664865657)
  ·
    refine ⟨97837016486694664998649243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130449355315592886664865657 97837016486694664998649243)
    ·
      refine ⟨146755524730041997497973865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97837016486694664998649243 146755524730041997497973865)
      ·
        refine ⟨110066643547531498123480399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146755524730041997497973865 110066643547531498123480399)
        ·
          refine ⟨165099965321297247185220599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110066643547531498123480399 165099965321297247185220599)
          ·
            refine ⟨247649947981945870777830899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165099965321297247185220599 247649947981945870777830899)
            ·
              refine ⟨371474921972918806166746349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247649947981945870777830899 371474921972918806166746349)
              ·
                refine ⟨139303095739844552312529881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371474921972918806166746349 139303095739844552312529881)
                ·
                  refine ⟨104477321804883414234397411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139303095739844552312529881 104477321804883414234397411)
                  ·
                    refine ⟨156715982707325121351596117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104477321804883414234397411 156715982707325121351596117)
                    ·
                      refine ⟨1836515422351466265839017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156715982707325121351596117 1836515422351466265839017)
                      ·
                        rfl

theorem cell23_3576601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3576601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576601 prefixEnd_3576601 := by exact prefixLift 3576601
  have htrace : WordTrace (prefixWord ++ tailWord_3576601) baseStart_3576601 baseEnd_3576601 := by
    simpa [prefixWord, tailWord_3576601, baseEnd_3576601] using wordTrace_append hprefix tailTrace_3576601
  have hstable : (prefixWord ++ tailWord_3576601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576601).length < 2 ^ (prefixWord ++ tailWord_3576601).sum := by decide
  have hdescent : baseEnd_3576601 < baseStart_3576601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576665 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 6, 2]
def baseStart_3576665 : Nat := 118140960795 + 3576665 * 2 ^ 59
def prefixEnd_3576665 : Nat := 4983230072969 + 3 ^ 40 * 3576665 * 2
def baseEnd_3576665 : Nat := 1836548285113354015438723

theorem tailTrace_3576665 : CollatzResearch.WordTrace tailWord_3576665 prefixEnd_3576665 1836548285113354015438723 := by
  unfold tailWord_3576665
  simp only [CollatzResearch.WordTrace]
  refine ⟨130451689587361025595195449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86967793058240683730130299 130451689587361025595195449)
  ·
    refine ⟨97838767190520769196396587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130451689587361025595195449 97838767190520769196396587)
    ·
      refine ⟨146758150785781153794594881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97838767190520769196396587 146758150785781153794594881)
      ·
        refine ⟨110068613089335865345946161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146758150785781153794594881 110068613089335865345946161)
        ·
          refine ⟨82551459817001899009459621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110068613089335865345946161 82551459817001899009459621)
          ·
            refine ⟨15478398715687856064273679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82551459817001899009459621 15478398715687856064273679)
            ·
              refine ⟨23217598073531784096410519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15478398715687856064273679 23217598073531784096410519)
              ·
                refine ⟨34826397110297676144615779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23217598073531784096410519 34826397110297676144615779)
                ·
                  refine ⟨52239595665446514216923669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34826397110297676144615779 52239595665446514216923669)
                  ·
                    refine ⟨2448731046817805353918297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52239595665446514216923669 2448731046817805353918297)
                    ·
                      refine ⟨1836548285113354015438723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448731046817805353918297 1836548285113354015438723)
                      ·
                        rfl

theorem cell23_3576665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_3576665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576665 prefixEnd_3576665 := by exact prefixLift 3576665
  have htrace : WordTrace (prefixWord ++ tailWord_3576665) baseStart_3576665 baseEnd_3576665 := by
    simpa [prefixWord, tailWord_3576665, baseEnd_3576665] using wordTrace_append hprefix tailTrace_3576665
  have hstable : (prefixWord ++ tailWord_3576665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576665).length < 2 ^ (prefixWord ++ tailWord_3576665).sum := by decide
  have hdescent : baseEnd_3576665 < baseStart_3576665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576675 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 5, 4]
def baseStart_3576675 : Nat := 118140960795 + 3576675 * 2 ^ 59
def prefixEnd_3576675 : Nat := 4983230072969 + 3 ^ 40 * 3576675 * 2
def baseEnd_3576675 : Nat := 612184473306632992104559

theorem tailTrace_3576675 : CollatzResearch.WordTrace tailWord_3576675 prefixEnd_3576675 612184473306632992104559 := by
  unfold tailWord_3576675
  simp only [CollatzResearch.WordTrace]
  refine ⟨130452054317324797303059479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86968036211549864868706319 130452054317324797303059479)
  ·
    refine ⟨195678081475987195954589219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130452054317324797303059479 195678081475987195954589219)
    ·
      refine ⟨293517122213980793931883829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195678081475987195954589219 293517122213980793931883829)
      ·
        refine ⟨27517230207560699431114109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293517122213980793931883829 27517230207560699431114109)
        ·
          refine ⟨10318961327835262286667791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27517230207560699431114109 10318961327835262286667791)
          ·
            refine ⟨15478441991752893430001687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318961327835262286667791 15478441991752893430001687)
            ·
              refine ⟨23217662987629340145002531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15478441991752893430001687 23217662987629340145002531)
              ·
                refine ⟨34826494481444010217503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23217662987629340145002531 34826494481444010217503797)
                ·
                  refine ⟨3264983857635375957890981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34826494481444010217503797 3264983857635375957890981)
                  ·
                    refine ⟨612184473306632992104559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264983857635375957890981 612184473306632992104559)
                    ·
                      rfl

theorem cell23_3576675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 4].length) (baseStart_3576675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576675 prefixEnd_3576675 := by exact prefixLift 3576675
  have htrace : WordTrace (prefixWord ++ tailWord_3576675) baseStart_3576675 baseEnd_3576675 := by
    simpa [prefixWord, tailWord_3576675, baseEnd_3576675] using wordTrace_append hprefix tailTrace_3576675
  have hstable : (prefixWord ++ tailWord_3576675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576675).length < 2 ^ (prefixWord ++ tailWord_3576675).sum := by decide
  have hdescent : baseEnd_3576675 < baseStart_3576675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576726 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3576726 : Nat := 118140960795 + 3576726 * 2 ^ 59
def prefixEnd_3576726 : Nat := 4983230072969 + 3 ^ 40 * 3576726 * 2
def baseEnd_3576726 : Nat := 612193202477759425591981

theorem tailTrace_3576726 : CollatzResearch.WordTrace tailWord_3576726 prefixEnd_3576726 612193202477759425591981 := by
  unfold tailWord_3576726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153369652508752063322877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86969276293426688675444021 8153369652508752063322877)
  ·
    refine ⟨3057513619690782023746079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8153369652508752063322877 3057513619690782023746079)
    ·
      refine ⟨4586270429536173035619119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057513619690782023746079 4586270429536173035619119)
      ·
        refine ⟨6879405644304259553428679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586270429536173035619119 6879405644304259553428679)
        ·
          refine ⟨10319108466456389330143019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879405644304259553428679 10319108466456389330143019)
          ·
            refine ⟨15478662699684583995214529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319108466456389330143019 15478662699684583995214529)
            ·
              refine ⟨11608997024763437996410897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15478662699684583995214529 11608997024763437996410897)
              ·
                refine ⟨8706747768572578497308173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11608997024763437996410897 8706747768572578497308173)
                ·
                  refine ⟨3265030413214716936490565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8706747768572578497308173 3265030413214716936490565)
                  ·
                    refine ⟨612193202477759425591981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265030413214716936490565 612193202477759425591981)
                    ·
                      rfl

theorem cell23_3576726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3576726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576726 prefixEnd_3576726 := by exact prefixLift 3576726
  have htrace : WordTrace (prefixWord ++ tailWord_3576726) baseStart_3576726 baseEnd_3576726 := by
    simpa [prefixWord, tailWord_3576726, baseEnd_3576726] using wordTrace_append hprefix tailTrace_3576726
  have hstable : (prefixWord ++ tailWord_3576726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576726).length < 2 ^ (prefixWord ++ tailWord_3576726).sum := by decide
  have hdescent : baseEnd_3576726 < baseStart_3576726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576743 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3576743 : Nat := 118140960795 + 3576743 * 2 ^ 59
def prefixEnd_3576743 : Nat := 4983230072969 + 3 ^ 40 * 3576743 * 2
def baseEnd_3576743 : Nat := 612196112201468236754455

theorem tailTrace_3576743 : CollatzResearch.WordTrace tailWord_3576743 prefixEnd_3576743 612196112201468236754455 := by
  unfold tailWord_3576743
  simp only [CollatzResearch.WordTrace]
  refine ⟨130454534481078444916534883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86969689654052296611023255 130454534481078444916534883)
  ·
    refine ⟨195681801721617667374802325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130454534481078444916534883 195681801721617667374802325)
    ·
      refine ⟨9172584455700828158193859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195681801721617667374802325 9172584455700828158193859)
      ·
        refine ⟨13758876683551242237290789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172584455700828158193859 13758876683551242237290789)
        ·
          refine ⟨2579789378165857919492023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13758876683551242237290789 2579789378165857919492023)
          ·
            refine ⟨3869684067248786879238035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579789378165857919492023 3869684067248786879238035)
            ·
              refine ⟨5804526100873180318857053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869684067248786879238035 5804526100873180318857053)
              ·
                refine ⟨2176697287827442619571395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5804526100873180318857053 2176697287827442619571395)
                ·
                  refine ⟨3265045931741163929357093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176697287827442619571395 3265045931741163929357093)
                  ·
                    refine ⟨612196112201468236754455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265045931741163929357093 612196112201468236754455)
                    ·
                      rfl

theorem cell23_3576743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3576743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576743 prefixEnd_3576743 := by exact prefixLift 3576743
  have htrace : WordTrace (prefixWord ++ tailWord_3576743) baseStart_3576743 baseEnd_3576743 := by
    simpa [prefixWord, tailWord_3576743, baseEnd_3576743] using wordTrace_append hprefix tailTrace_3576743
  have hstable : (prefixWord ++ tailWord_3576743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576743).length < 2 ^ (prefixWord ++ tailWord_3576743).sum := by decide
  have hdescent : baseEnd_3576743 < baseStart_3576743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576775 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3576775 : Nat := 118140960795 + 3576775 * 2 ^ 59
def prefixEnd_3576775 : Nat := 4983230072969 + 3 ^ 40 * 3576775 * 2
def baseEnd_3576775 : Nat := 1836604767985348585063217

theorem tailTrace_3576775 : CollatzResearch.WordTrace tailWord_3576775 prefixEnd_3576775 1836604767985348585063217 := by
  unfold tailWord_3576775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130455701616962514381699779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86970467744641676254466519 130455701616962514381699779)
  ·
    refine ⟨195683552425443771572549669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130455701616962514381699779 195683552425443771572549669)
    ·
      refine ⟨36690666079770707169853063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195683552425443771572549669 36690666079770707169853063)
      ·
        refine ⟨55035999119656060754779595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36690666079770707169853063 55035999119656060754779595)
        ·
          refine ⟨82553998679484091132169393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55035999119656060754779595 82553998679484091132169393)
          ·
            refine ⟨61915499009613068349127045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82553998679484091132169393 61915499009613068349127045)
            ·
              refine ⟨11609156064302450315461321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61915499009613068349127045 11609156064302450315461321)
              ·
                refine ⟨8706867048226837736595991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609156064302450315461321 8706867048226837736595991)
                ·
                  refine ⟨13060300572340256604893987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706867048226837736595991 13060300572340256604893987)
                  ·
                    refine ⟨19590450858510384907340981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060300572340256604893987 19590450858510384907340981)
                    ·
                      refine ⟨1836604767985348585063217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19590450858510384907340981 1836604767985348585063217)
                      ·
                        rfl

theorem cell23_3576775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3576775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576775 prefixEnd_3576775 := by exact prefixLift 3576775
  have htrace : WordTrace (prefixWord ++ tailWord_3576775) baseStart_3576775 baseEnd_3576775 := by
    simpa [prefixWord, tailWord_3576775, baseEnd_3576775] using wordTrace_append hprefix tailTrace_3576775
  have hstable : (prefixWord ++ tailWord_3576775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576775).length < 2 ^ (prefixWord ++ tailWord_3576775).sum := by decide
  have hdescent : baseEnd_3576775 < baseStart_3576775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576785 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3576785 : Nat := 118140960795 + 3576785 * 2 ^ 59
def prefixEnd_3576785 : Nat := 4983230072969 + 3 ^ 40 * 3576785 * 2
def baseEnd_3576785 : Nat := 1836609902791893545938171

theorem tailTrace_3576785 : CollatzResearch.WordTrace tailWord_3576785 prefixEnd_3576785 1836609902791893545938171 := by
  unfold tailWord_3576785
  simp only [CollatzResearch.WordTrace]
  refine ⟨130456066346926286089563809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86970710897950857393042539 130456066346926286089563809)
  ·
    refine ⟨97842049760194714567172857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130456066346926286089563809 97842049760194714567172857)
    ·
      refine ⟨73381537320146035925379643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97842049760194714567172857 73381537320146035925379643)
      ·
        refine ⟨110072305980219053888069465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73381537320146035925379643 110072305980219053888069465)
        ·
          refine ⟨82554229485164290416052099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110072305980219053888069465 82554229485164290416052099)
          ·
            refine ⟨123831344227746435624078149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82554229485164290416052099 123831344227746435624078149)
            ·
              refine ⟨23218377042702456679514653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123831344227746435624078149 23218377042702456679514653)
              ·
                refine ⟨8706891391013421254817995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23218377042702456679514653 8706891391013421254817995)
                ·
                  refine ⟨13060337086520131882226993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706891391013421254817995 13060337086520131882226993)
                  ·
                    refine ⟨9795252814890098911670245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13060337086520131882226993 9795252814890098911670245)
                    ·
                      refine ⟨1836609902791893545938171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9795252814890098911670245 1836609902791893545938171)
                      ·
                        rfl

theorem cell23_3576785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3576785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576785 prefixEnd_3576785 := by exact prefixLift 3576785
  have htrace : WordTrace (prefixWord ++ tailWord_3576785) baseStart_3576785 baseEnd_3576785 := by
    simpa [prefixWord, tailWord_3576785, baseEnd_3576785] using wordTrace_append hprefix tailTrace_3576785
  have hstable : (prefixWord ++ tailWord_3576785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576785).length < 2 ^ (prefixWord ++ tailWord_3576785).sum := by decide
  have hdescent : baseEnd_3576785 < baseStart_3576785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576792 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3576792 : Nat := 118140960795 + 3576792 * 2 ^ 59
def prefixEnd_3576792 : Nat := 4983230072969 + 3 ^ 40 * 3576792 * 2
def baseEnd_3576792 : Nat := 1836613497156475018550639

theorem tailTrace_3576792 : CollatzResearch.WordTrace tailWord_3576792 prefixEnd_3576792 1836613497156475018550639 := by
  unfold tailWord_3576792
  simp only [CollatzResearch.WordTrace]
  refine ⟨65228160828950463142534315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86970881105267284190045753 65228160828950463142534315)
  ·
    refine ⟨97842241243425694713801473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65228160828950463142534315 97842241243425694713801473)
    ·
      refine ⟨73381680932569271035351105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97842241243425694713801473 73381680932569271035351105)
      ·
        refine ⟨55036260699426953276513329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73381680932569271035351105 55036260699426953276513329)
        ·
          refine ⟨41277195524570214957384997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55036260699426953276513329 41277195524570214957384997)
          ·
            refine ⟨7739474160856915304509687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41277195524570214957384997 7739474160856915304509687)
            ·
              refine ⟨11609211241285372956764531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739474160856915304509687 11609211241285372956764531)
              ·
                refine ⟨17413816861928059435146797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609211241285372956764531 17413816861928059435146797)
                ·
                  refine ⟨6530181323223022288180049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17413816861928059435146797 6530181323223022288180049)
                  ·
                    refine ⟨4897635992417266716135037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6530181323223022288180049 4897635992417266716135037)
                    ·
                      refine ⟨1836613497156475018550639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897635992417266716135037 1836613497156475018550639)
                      ·
                        rfl

theorem cell23_3576792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3576792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576792 prefixEnd_3576792 := by exact prefixLift 3576792
  have htrace : WordTrace (prefixWord ++ tailWord_3576792) baseStart_3576792 baseEnd_3576792 := by
    simpa [prefixWord, tailWord_3576792, baseEnd_3576792] using wordTrace_append hprefix tailTrace_3576792
  have hstable : (prefixWord ++ tailWord_3576792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576792).length < 2 ^ (prefixWord ++ tailWord_3576792).sum := by decide
  have hdescent : baseEnd_3576792 < baseStart_3576792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576839 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3576839 : Nat := 118140960795 + 3576839 * 2 ^ 59
def prefixEnd_3576839 : Nat := 4983230072969 + 3 ^ 40 * 3576839 * 2
def baseEnd_3576839 : Nat := 1836637630747236334662923

theorem tailTrace_3576839 : CollatzResearch.WordTrace tailWord_3576839 prefixEnd_3576839 1836637630747236334662923 := by
  unfold tailWord_3576839
  simp only [CollatzResearch.WordTrace]
  refine ⟨130458035888730653312029571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86972023925820435541353047 130458035888730653312029571)
  ·
    refine ⟨195687053833095979968044357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130458035888730653312029571 195687053833095979968044357)
    ·
      refine ⟨36691322593705496244008317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195687053833095979968044357 36691322593705496244008317)
      ·
        refine ⟨13759245972639561091503119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36691322593705496244008317 13759245972639561091503119)
        ·
          refine ⟨20638868958959341637254679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759245972639561091503119 20638868958959341637254679)
          ·
            refine ⟨30958303438439012455882019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20638868958959341637254679 30958303438439012455882019)
            ·
              refine ⟨46437455157658518683823029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30958303438439012455882019 46437455157658518683823029)
              ·
                refine ⟨4353511421030486126608409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46437455157658518683823029 4353511421030486126608409)
                ·
                  refine ⟨3265133565772864594956307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4353511421030486126608409 3265133565772864594956307)
                  ·
                    refine ⟨4897700348659296892434461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3265133565772864594956307 4897700348659296892434461)
                    ·
                      refine ⟨1836637630747236334662923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897700348659296892434461 1836637630747236334662923)
                      ·
                        rfl

theorem cell23_3576839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3576839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576839 prefixEnd_3576839 := by exact prefixLift 3576839
  have htrace : WordTrace (prefixWord ++ tailWord_3576839) baseStart_3576839 baseEnd_3576839 := by
    simpa [prefixWord, tailWord_3576839, baseEnd_3576839] using wordTrace_append hprefix tailTrace_3576839
  have hstable : (prefixWord ++ tailWord_3576839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576839).length < 2 ^ (prefixWord ++ tailWord_3576839).sum := by decide
  have hdescent : baseEnd_3576839 < baseStart_3576839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576866 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_3576866 : Nat := 118140960795 + 3576866 * 2 ^ 59
def prefixEnd_3576866 : Nat := 4983230072969 + 3 ^ 40 * 3576866 * 2
def baseEnd_3576866 : Nat := 1836651494724907729025299

theorem tailTrace_3576866 : CollatzResearch.WordTrace tailWord_3576866 prefixEnd_3576866 1836651494724907729025299 := by
  unfold tailWord_3576866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32614755164908209230815613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86972680439755224615508301 32614755164908209230815613)
  ·
    refine ⟨12230533186840578461555855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32614755164908209230815613 12230533186840578461555855)
    ·
      refine ⟨18345799780260867692333783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12230533186840578461555855 18345799780260867692333783)
      ·
        refine ⟨27518699670391301538500675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18345799780260867692333783 27518699670391301538500675)
        ·
          refine ⟨41278049505586952307751013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27518699670391301538500675 41278049505586952307751013)
          ·
            refine ⟨7739634282297553557703315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41278049505586952307751013 7739634282297553557703315)
            ·
              refine ⟨11609451423446330336554973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739634282297553557703315 11609451423446330336554973)
              ·
                refine ⟨4353544283792373876208115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11609451423446330336554973 4353544283792373876208115)
                ·
                  refine ⟨6530316425688560814312173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353544283792373876208115 6530316425688560814312173)
                  ·
                    refine ⟨2448868659633210305367065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6530316425688560814312173 2448868659633210305367065)
                    ·
                      refine ⟨1836651494724907729025299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2448868659633210305367065 1836651494724907729025299)
                      ·
                        rfl

theorem cell23_3576866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_3576866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576866 prefixEnd_3576866 := by exact prefixLift 3576866
  have htrace : WordTrace (prefixWord ++ tailWord_3576866) baseStart_3576866 baseEnd_3576866 := by
    simpa [prefixWord, tailWord_3576866, baseEnd_3576866] using wordTrace_append hprefix tailTrace_3576866
  have hstable : (prefixWord ++ tailWord_3576866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576866).length < 2 ^ (prefixWord ++ tailWord_3576866).sum := by decide
  have hdescent : baseEnd_3576866 < baseStart_3576866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576875 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_3576875 : Nat := 118140960795 + 3576875 * 2 ^ 59
def prefixEnd_3576875 : Nat := 4983230072969 + 3 ^ 40 * 3576875 * 2
def baseEnd_3576875 : Nat := 1836656116050798193812757

theorem tailTrace_3576875 : CollatzResearch.WordTrace tailWord_3576875 prefixEnd_3576875 1836656116050798193812757 := by
  unfold tailWord_3576875
  simp only [CollatzResearch.WordTrace]
  refine ⟨130459348916600231460340079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86972899277733487640226719 130459348916600231460340079)
  ·
    refine ⟨195689023374900347190510119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130459348916600231460340079 195689023374900347190510119)
    ·
      refine ⟨293533535062350520785765179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195689023374900347190510119 293533535062350520785765179)
      ·
        refine ⟨440300302593525781178647769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293533535062350520785765179 440300302593525781178647769)
        ·
          refine ⟨330225226945144335883985827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440300302593525781178647769 330225226945144335883985827)
          ·
            refine ⟨495337840417716503825978741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330225226945144335883985827 495337840417716503825978741)
            ·
              refine ⟨46437922539160922233685507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495337840417716503825978741 46437922539160922233685507)
              ·
                refine ⟨69656883808741383350528261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46437922539160922233685507 69656883808741383350528261)
                ·
                  refine ⟨13060665714139009378224049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69656883808741383350528261 13060665714139009378224049)
                  ·
                    refine ⟨9795499285604257033668037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13060665714139009378224049 9795499285604257033668037)
                    ·
                      refine ⟨1836656116050798193812757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9795499285604257033668037 1836656116050798193812757)
                      ·
                        rfl

theorem cell23_3576875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_3576875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576875 prefixEnd_3576875 := by exact prefixLift 3576875
  have htrace : WordTrace (prefixWord ++ tailWord_3576875) baseStart_3576875 baseEnd_3576875 := by
    simpa [prefixWord, tailWord_3576875, baseEnd_3576875] using wordTrace_append hprefix tailTrace_3576875
  have hstable : (prefixWord ++ tailWord_3576875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576875).length < 2 ^ (prefixWord ++ tailWord_3576875).sum := by decide
  have hdescent : baseEnd_3576875 < baseStart_3576875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576892 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3576892 : Nat := 118140960795 + 3576892 * 2 ^ 59
def prefixEnd_3576892 : Nat := 4983230072969 + 3 ^ 40 * 3576892 * 2
def baseEnd_3576892 : Nat := 1836664845221924627300179

theorem tailTrace_3576892 : CollatzResearch.WordTrace tailWord_3576892 prefixEnd_3576892 1836664845221924627300179 := by
  unfold tailWord_3576892
  simp only [CollatzResearch.WordTrace]
  refine ⟨65229984478769321681854465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86973312638359095575805953 65229984478769321681854465)
  ·
    refine ⟨48922488359076991261390849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65229984478769321681854465 48922488359076991261390849)
    ·
      refine ⟨36691866269307743446043137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48922488359076991261390849 36691866269307743446043137)
      ·
        refine ⟨27518899701980807584532353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36691866269307743446043137 27518899701980807584532353)
        ·
          refine ⟨20639174776485605688399265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27518899701980807584532353 20639174776485605688399265)
          ·
            refine ⟨15479381082364204266299449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639174776485605688399265 15479381082364204266299449)
            ·
              refine ⟨11609535811773153199724587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479381082364204266299449 11609535811773153199724587)
              ·
                refine ⟨17414303717659729799586881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609535811773153199724587 17414303717659729799586881)
                ·
                  refine ⟨13060727788244797349690161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17414303717659729799586881 13060727788244797349690161)
                  ·
                    refine ⟨9795545841183598012267621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13060727788244797349690161 9795545841183598012267621)
                    ·
                      refine ⟨1836664845221924627300179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9795545841183598012267621 1836664845221924627300179)
                      ·
                        rfl

theorem cell23_3576892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3576892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576892 prefixEnd_3576892 := by exact prefixLift 3576892
  have htrace : WordTrace (prefixWord ++ tailWord_3576892) baseStart_3576892 baseEnd_3576892 := by
    simpa [prefixWord, tailWord_3576892, baseEnd_3576892] using wordTrace_append hprefix tailTrace_3576892
  have hstable : (prefixWord ++ tailWord_3576892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576892).length < 2 ^ (prefixWord ++ tailWord_3576892).sum := by decide
  have hdescent : baseEnd_3576892 < baseStart_3576892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576936 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 7]
def baseStart_3576936 : Nat := 118140960795 + 3576936 * 2 ^ 59
def prefixEnd_3576936 : Nat := 4983230072969 + 3 ^ 40 * 3576936 * 2
def baseEnd_3576936 : Nat := 204076382041191383905553

theorem tailTrace_3576936 : CollatzResearch.WordTrace tailWord_3576936 prefixEnd_3576936 204076382041191383905553 := by
  unfold tailWord_3576936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65230786884689619439155331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86974382512919492585540441 65230786884689619439155331)
  ·
    refine ⟨97846180327034429158732997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65230786884689619439155331 97846180327034429158732997)
    ·
      refine ⟨18346158811318955467262437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97846180327034429158732997 18346158811318955467262437)
      ·
        refine ⟨3439904777122304150111707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18346158811318955467262437 3439904777122304150111707)
        ·
          refine ⟨5159857165683456225167561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439904777122304150111707 5159857165683456225167561)
          ·
            refine ⟨3869892874262592168875671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5159857165683456225167561 3869892874262592168875671)
            ·
              refine ⟨5804839311393888253313507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869892874262592168875671 5804839311393888253313507)
              ·
                refine ⟨8707258967090832379970261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804839311393888253313507 8707258967090832379970261)
                ·
                  refine ⟨204076382041191383905553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8707258967090832379970261 204076382041191383905553)
                  ·
                    rfl

theorem cell23_3576936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_3576936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576936 prefixEnd_3576936 := by exact prefixLift 3576936
  have htrace : WordTrace (prefixWord ++ tailWord_3576936) baseStart_3576936 baseEnd_3576936 := by
    simpa [prefixWord, tailWord_3576936, baseEnd_3576936] using wordTrace_append hprefix tailTrace_3576936
  have hstable : (prefixWord ++ tailWord_3576936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576936).length < 2 ^ (prefixWord ++ tailWord_3576936).sum := by decide
  have hdescent : baseEnd_3576936 < baseStart_3576936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576942 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3576942 : Nat := 118140960795 + 3576942 * 2 ^ 59
def prefixEnd_3576942 : Nat := 4983230072969 + 3 ^ 40 * 3576942 * 2
def baseEnd_3576942 : Nat := 1836690519254649431674949

theorem tailTrace_3576942 : CollatzResearch.WordTrace tailWord_3576942 prefixEnd_3576942 1836690519254649431674949 := by
  unfold tailWord_3576942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307724075919687737878635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86974528404905001268686053 16307724075919687737878635)
  ·
    refine ⟨24461586113879531606817953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16307724075919687737878635 24461586113879531606817953)
    ·
      refine ⟨18346189585409648705113465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24461586113879531606817953 18346189585409648705113465)
      ·
        refine ⟨13759642189057236528835099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18346189585409648705113465 13759642189057236528835099)
        ·
          refine ⟨20639463283585854793252649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759642189057236528835099 20639463283585854793252649)
          ·
            refine ⟨15479597462689391094939487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639463283585854793252649 15479597462689391094939487)
            ·
              refine ⟨23219396194034086642409231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15479597462689391094939487 23219396194034086642409231)
              ·
                refine ⟨34829094291051129963613847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23219396194034086642409231 34829094291051129963613847)
                ·
                  refine ⟨52243641436576694945420771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34829094291051129963613847 52243641436576694945420771)
                  ·
                    refine ⟨78365462154865042418131157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52243641436576694945420771 78365462154865042418131157)
                    ·
                      refine ⟨1836690519254649431674949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78365462154865042418131157 1836690519254649431674949)
                      ·
                        rfl

theorem cell23_3576942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3576942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576942 prefixEnd_3576942 := by exact prefixLift 3576942
  have htrace : WordTrace (prefixWord ++ tailWord_3576942) baseStart_3576942 baseEnd_3576942 := by
    simpa [prefixWord, tailWord_3576942, baseEnd_3576942] using wordTrace_append hprefix tailTrace_3576942
  have hstable : (prefixWord ++ tailWord_3576942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576942).length < 2 ^ (prefixWord ++ tailWord_3576942).sum := by decide
  have hdescent : baseEnd_3576942 < baseStart_3576942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576945 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3576945 : Nat := 118140960795 + 3576945 * 2 ^ 59
def prefixEnd_3576945 : Nat := 4983230072969 + 3 ^ 40 * 3576945 * 2
def baseEnd_3576945 : Nat := 612230686565537639979145

theorem tailTrace_3576945 : CollatzResearch.WordTrace tailWord_3576945 prefixEnd_3576945 612230686565537639979145 := by
  unfold tailWord_3576945
  simp only [CollatzResearch.WordTrace]
  refine ⟨130461902026346633415388289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86974601350897755610258859 130461902026346633415388289)
  ·
    refine ⟨97846426519759975061541217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130461902026346633415388289 97846426519759975061541217)
    ·
      refine ⟨73384819889819981296155913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97846426519759975061541217 73384819889819981296155913)
      ·
        refine ⟨55038614917364985972116935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73384819889819981296155913 55038614917364985972116935)
        ·
          refine ⟨82557922376047478958175403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55038614917364985972116935 82557922376047478958175403)
          ·
            refine ⟨123836883564071218437263105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82557922376047478958175403 123836883564071218437263105)
            ·
              refine ⟨92877662673053413827947329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123836883564071218437263105 92877662673053413827947329)
              ·
                refine ⟨69658247004790060370960497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92877662673053413827947329 69658247004790060370960497)
                ·
                  refine ⟨52243685253592545278220373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69658247004790060370960497 52243685253592545278220373)
                  ·
                    refine ⟨612230686565537639979145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52243685253592545278220373 612230686565537639979145)
                    ·
                      rfl

theorem cell23_3576945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3576945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576945 prefixEnd_3576945 := by exact prefixLift 3576945
  have htrace : WordTrace (prefixWord ++ tailWord_3576945) baseStart_3576945 baseEnd_3576945 := by
    simpa [prefixWord, tailWord_3576945, baseEnd_3576945] using wordTrace_append hprefix tailTrace_3576945
  have hstable : (prefixWord ++ tailWord_3576945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576945).length < 2 ^ (prefixWord ++ tailWord_3576945).sum := by decide
  have hdescent : baseEnd_3576945 < baseStart_3576945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576955 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_3576955 : Nat := 118140960795 + 3576955 * 2 ^ 59
def prefixEnd_3576955 : Nat := 4983230072969 + 3 ^ 40 * 3576955 * 2
def baseEnd_3576955 : Nat := 1836697194503157880812389

theorem tailTrace_3576955 : CollatzResearch.WordTrace tailWord_3576955 prefixEnd_3576955 1836697194503157880812389 := by
  unfold tailWord_3576955
  simp only [CollatzResearch.WordTrace]
  refine ⟨130462266756310405123252319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86974844504206936748834879 130462266756310405123252319)
  ·
    refine ⟨195693400134465607684878479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130462266756310405123252319 195693400134465607684878479)
    ·
      refine ⟨293540100201698411527317719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195693400134465607684878479 293540100201698411527317719)
      ·
        refine ⟨440310150302547617290976579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293540100201698411527317719 440310150302547617290976579)
        ·
          refine ⟨660465225453821425936464869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440310150302547617290976579 660465225453821425936464869)
          ·
            refine ⟨123837229772591517363087163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 660465225453821425936464869 123837229772591517363087163)
            ·
              refine ⟨185755844658887276044630745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123837229772591517363087163 185755844658887276044630745)
              ·
                refine ⟨139316883494165457033473059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185755844658887276044630745 139316883494165457033473059)
                ·
                  refine ⟨208975325241248185550209589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139316883494165457033473059 208975325241248185550209589)
                  ·
                    refine ⟨19591436741367017395332149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208975325241248185550209589 19591436741367017395332149)
                    ·
                      refine ⟨1836697194503157880812389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19591436741367017395332149 1836697194503157880812389)
                      ·
                        rfl

theorem cell23_3576955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_3576955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576955 prefixEnd_3576955 := by exact prefixLift 3576955
  have htrace : WordTrace (prefixWord ++ tailWord_3576955) baseStart_3576955 baseEnd_3576955 := by
    simpa [prefixWord, tailWord_3576955, baseEnd_3576955] using wordTrace_append hprefix tailTrace_3576955
  have hstable : (prefixWord ++ tailWord_3576955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576955).length < 2 ^ (prefixWord ++ tailWord_3576955).sum := by decide
  have hdescent : baseEnd_3576955 < baseStart_3576955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576969 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_3576969 : Nat := 118140960795 + 3576969 * 2 ^ 59
def prefixEnd_3576969 : Nat := 4983230072969 + 3 ^ 40 * 3576969 * 2
def baseEnd_3576969 : Nat := 1836704383232320826037325

theorem tailTrace_3576969 : CollatzResearch.WordTrace tailWord_3576969 prefixEnd_3576969 1836704383232320826037325 := by
  unfold tailWord_3576969
  simp only [CollatzResearch.WordTrace]
  refine ⟨130462777378259685514261961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86975184918839790342841307 130462777378259685514261961)
  ·
    refine ⟨97847083033694764135696471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130462777378259685514261961 97847083033694764135696471)
    ·
      refine ⟨146770624550542146203544707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97847083033694764135696471 146770624550542146203544707)
      ·
        refine ⟨220155936825813219305317061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146770624550542146203544707 220155936825813219305317061)
        ·
          refine ⟨41279238154839978619746949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220155936825813219305317061 41279238154839978619746949)
          ·
            refine ⟨7739857154032495991202553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41279238154839978619746949 7739857154032495991202553)
            ·
              refine ⟨5804892865524371993401915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739857154032495991202553 5804892865524371993401915)
              ·
                refine ⟨8707339298286557990102873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804892865524371993401915 8707339298286557990102873)
                ·
                  refine ⟨6530504473714918492577155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707339298286557990102873 6530504473714918492577155)
                  ·
                    refine ⟨9795756710572377738865733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530504473714918492577155 9795756710572377738865733)
                    ·
                      refine ⟨1836704383232320826037325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9795756710572377738865733 1836704383232320826037325)
                      ·
                        rfl

theorem cell23_3576969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_3576969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576969 prefixEnd_3576969 := by exact prefixLift 3576969
  have htrace : WordTrace (prefixWord ++ tailWord_3576969) baseStart_3576969 baseEnd_3576969 := by
    simpa [prefixWord, tailWord_3576969, baseEnd_3576969] using wordTrace_append hprefix tailTrace_3576969
  have hstable : (prefixWord ++ tailWord_3576969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576969).length < 2 ^ (prefixWord ++ tailWord_3576969).sum := by decide
  have hdescent : baseEnd_3576969 < baseStart_3576969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576972 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3576972 : Nat := 118140960795 + 3576972 * 2 ^ 59
def prefixEnd_3576972 : Nat := 4983230072969 + 3 ^ 40 * 3576972 * 2
def baseEnd_3576972 : Nat := 1836705923674284314299811

theorem tailTrace_3576972 : CollatzResearch.WordTrace tailWord_3576972 prefixEnd_3576972 1836705923674284314299811 := by
  unfold tailWord_3576972
  simp only [CollatzResearch.WordTrace]
  refine ⟨65231443398624408513310585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86975257864832544684414113 65231443398624408513310585)
  ·
    refine ⟨48923582548968306384982939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65231443398624408513310585 48923582548968306384982939)
    ·
      refine ⟨73385373823452459577474409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48923582548968306384982939 73385373823452459577474409)
      ·
        refine ⟨55039030367589344683105807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73385373823452459577474409 55039030367589344683105807)
        ·
          refine ⟨82558545551384017024658711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55039030367589344683105807 82558545551384017024658711)
          ·
            refine ⟨123837818327076025536988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82558545551384017024658711 123837818327076025536988067)
            ·
              refine ⟨185756727490614038305482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123837818327076025536988067 185756727490614038305482101)
              ·
                refine ⟨17414693202245066091138947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185756727490614038305482101 17414693202245066091138947)
                ·
                  refine ⟨26122039803367599136708421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17414693202245066091138947 26122039803367599136708421)
                  ·
                    refine ⟨4897882463131424838132829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26122039803367599136708421 4897882463131424838132829)
                    ·
                      refine ⟨1836705923674284314299811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897882463131424838132829 1836705923674284314299811)
                      ·
                        rfl

theorem cell23_3576972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3576972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576972 prefixEnd_3576972 := by exact prefixLift 3576972
  have htrace : WordTrace (prefixWord ++ tailWord_3576972) baseStart_3576972 baseEnd_3576972 := by
    simpa [prefixWord, tailWord_3576972, baseEnd_3576972] using wordTrace_append hprefix tailTrace_3576972
  have hstable : (prefixWord ++ tailWord_3576972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576972).length < 2 ^ (prefixWord ++ tailWord_3576972).sum := by decide
  have hdescent : baseEnd_3576972 < baseStart_3576972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576989 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3576989 : Nat := 118140960795 + 3576989 * 2 ^ 59
def prefixEnd_3576989 : Nat := 4983230072969 + 3 ^ 40 * 3576989 * 2
def baseEnd_3576989 : Nat := 1836714652845410747787233

theorem tailTrace_3576989 : CollatzResearch.WordTrace tailWord_3576989 prefixEnd_3576989 1836714652845410747787233 := by
  unfold tailWord_3576989
  simp only [CollatzResearch.WordTrace]
  refine ⟨130463506838187228929990021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86975671225458152619993347 130463506838187228929990021)
  ·
    refine ⟨24461907532160105424373129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130463506838187228929990021 24461907532160105424373129)
    ·
      refine ⟨18346430649120079068279847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24461907532160105424373129 18346430649120079068279847)
      ·
        refine ⟨27519645973680118602419771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18346430649120079068279847 27519645973680118602419771)
        ·
          refine ⟨41279468960520177903629657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27519645973680118602419771 41279468960520177903629657)
          ·
            refine ⟨30959601720390133427722243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41279468960520177903629657 30959601720390133427722243)
            ·
              refine ⟨46439402580585200141583365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30959601720390133427722243 46439402580585200141583365)
              ·
                refine ⟨8707387983859725026546881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46439402580585200141583365 8707387983859725026546881)
                ·
                  refine ⟨6530540987894793769910161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707387983859725026546881 6530540987894793769910161)
                  ·
                    refine ⟨4897905740921095327432621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6530540987894793769910161 4897905740921095327432621)
                    ·
                      refine ⟨1836714652845410747787233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4897905740921095327432621 1836714652845410747787233)
                      ·
                        rfl

theorem cell23_3576989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3576989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3576989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3576989 prefixEnd_3576989 := by exact prefixLift 3576989
  have htrace : WordTrace (prefixWord ++ tailWord_3576989) baseStart_3576989 baseEnd_3576989 := by
    simpa [prefixWord, tailWord_3576989, baseEnd_3576989] using wordTrace_append hprefix tailTrace_3576989
  have hstable : (prefixWord ++ tailWord_3576989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576989).length < 2 ^ (prefixWord ++ tailWord_3576989).sum := by decide
  have hdescent : baseEnd_3576989 < baseStart_3576989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577009 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 6]
def baseStart_3577009 : Nat := 118140960795 + 3577009 * 2 ^ 59
def prefixEnd_3577009 : Nat := 4983230072969 + 3 ^ 40 * 3577009 * 2
def baseEnd_3577009 : Nat := 204080546939833407726349

theorem tailTrace_3577009 : CollatzResearch.WordTrace tailWord_3577009 prefixEnd_3577009 204080546939833407726349 := by
  unfold tailWord_3577009
  simp only [CollatzResearch.WordTrace]
  refine ⟨130464236298114772345718081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86976157532076514897145387 130464236298114772345718081)
  ·
    refine ⟨97848177223586079259288561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130464236298114772345718081 97848177223586079259288561)
    ·
      refine ⟨73386132917689559444466421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97848177223586079259288561 73386132917689559444466421)
      ·
        refine ⟨6879949961033396197918727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73386132917689559444466421 6879949961033396197918727)
        ·
          refine ⟨10319924941550094296878091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879949961033396197918727 10319924941550094296878091)
          ·
            refine ⟨15479887412325141445317137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319924941550094296878091 15479887412325141445317137)
            ·
              refine ⟨11609915559243856083987853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479887412325141445317137 11609915559243856083987853)
              ·
                refine ⟨4353718334716446031495445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11609915559243856083987853 4353718334716446031495445)
                ·
                  refine ⟨204080546939833407726349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4353718334716446031495445 204080546939833407726349)
                  ·
                    rfl

theorem cell23_3577009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_3577009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577009 prefixEnd_3577009 := by exact prefixLift 3577009
  have htrace : WordTrace (prefixWord ++ tailWord_3577009) baseStart_3577009 baseEnd_3577009 := by
    simpa [prefixWord, tailWord_3577009, baseEnd_3577009] using wordTrace_append hprefix tailTrace_3577009
  have hstable : (prefixWord ++ tailWord_3577009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577009).length < 2 ^ (prefixWord ++ tailWord_3577009).sum := by decide
  have hdescent : baseEnd_3577009 < baseStart_3577009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577082 : List Nat := [3, 1, 1, 1, 1, 4, 3, 9]
def baseStart_3577082 : Nat := 118140960795 + 3577082 * 2 ^ 59
def prefixEnd_3577082 : Nat := 4983230072969 + 3 ^ 40 * 3577082 * 2
def baseEnd_3577082 : Nat := 68028237279491810515715

theorem tailTrace_3577082 : CollatzResearch.WordTrace tailWord_3577082 prefixEnd_3577082 68028237279491810515715 := by
  unfold tailWord_3577082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616724706712576453281375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86977932551233537208750333 32616724706712576453281375)
  ·
    refine ⟨48925087060068864679922063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32616724706712576453281375 48925087060068864679922063)
    ·
      refine ⟨73387630590103297019883095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48925087060068864679922063 73387630590103297019883095)
      ·
        refine ⟨110081445885154945529824643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73387630590103297019883095 110081445885154945529824643)
        ·
          refine ⟨165122168827732418294736965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110081445885154945529824643 165122168827732418294736965)
          ·
            refine ⟨30960406655199828430263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165122168827732418294736965 30960406655199828430263181)
            ·
              refine ⟨11610152495699935661348693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30960406655199828430263181 11610152495699935661348693)
              ·
                refine ⟨68028237279491810515715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11610152495699935661348693 68028237279491810515715)
                ·
                  rfl

theorem cell23_3577082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_3577082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577082 prefixEnd_3577082 := by exact prefixLift 3577082
  have htrace : WordTrace (prefixWord ++ tailWord_3577082) baseStart_3577082 baseEnd_3577082 := by
    simpa [prefixWord, tailWord_3577082, baseEnd_3577082] using wordTrace_append hprefix tailTrace_3577082
  have hstable : (prefixWord ++ tailWord_3577082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577082).length < 2 ^ (prefixWord ++ tailWord_3577082).sum := by decide
  have hdescent : baseEnd_3577082 < baseStart_3577082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577086 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3577086 : Nat := 118140960795 + 3577086 * 2 ^ 59
def prefixEnd_3577086 : Nat := 4983230072969 + 3 ^ 40 * 3577086 * 2
def baseEnd_3577086 : Nat := 612254820156298956091429

theorem tailTrace_3577086 : CollatzResearch.WordTrace tailWord_3577086 prefixEnd_3577086 612254820156298956091429 := by
  unfold tailWord_3577086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308380589854476812033889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86978029812557209664180741 16308380589854476812033889)
  ·
    refine ⟨12231285442390857609025417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16308380589854476812033889 12231285442390857609025417)
    ·
      refine ⟨9173464081793143206769063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12231285442390857609025417 9173464081793143206769063)
      ·
        refine ⟨13760196122689714810153595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173464081793143206769063 13760196122689714810153595)
        ·
          refine ⟨20640294184034572215230393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760196122689714810153595 20640294184034572215230393)
          ·
            refine ⟨15480220638025929161422795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20640294184034572215230393 15480220638025929161422795)
            ·
              refine ⟨23220330957038893742134193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15480220638025929161422795 23220330957038893742134193)
              ·
                refine ⟨17415248217779170306600645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23220330957038893742134193 17415248217779170306600645)
                ·
                  refine ⟨3265359040833594432487621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17415248217779170306600645 3265359040833594432487621)
                  ·
                    refine ⟨612254820156298956091429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265359040833594432487621 612254820156298956091429)
                    ·
                      rfl

theorem cell23_3577086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3577086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577086 prefixEnd_3577086 := by exact prefixLift 3577086
  have htrace : WordTrace (prefixWord ++ tailWord_3577086) baseStart_3577086 baseEnd_3577086 := by
    simpa [prefixWord, tailWord_3577086, baseEnd_3577086] using wordTrace_append hprefix tailTrace_3577086
  have hstable : (prefixWord ++ tailWord_3577086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577086).length < 2 ^ (prefixWord ++ tailWord_3577086).sum := by decide
  have hdescent : baseEnd_3577086 < baseStart_3577086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577096 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3577096 : Nat := 118140960795 + 3577096 * 2 ^ 59
def prefixEnd_3577096 : Nat := 4983230072969 + 3 ^ 40 * 3577096 * 2
def baseEnd_3577096 : Nat := 1836769595275441829149241

theorem tailTrace_3577096 : CollatzResearch.WordTrace tailWord_3577096 prefixEnd_3577096 1836769595275441829149241 := by
  unfold tailWord_3577096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65233704724399793102067571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86978272965866390802756761 65233704724399793102067571)
  ·
    refine ⟨97850557086599689653101357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65233704724399793102067571 97850557086599689653101357)
    ·
      refine ⟨36693958907474883619913009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97850557086599689653101357 36693958907474883619913009)
      ·
        refine ⟨27520469180606162714934757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36693958907474883619913009 27520469180606162714934757)
        ·
          refine ⟨5160087971363655509050267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27520469180606162714934757 5160087971363655509050267)
          ·
            refine ⟨7740131957045483263575401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160087971363655509050267 7740131957045483263575401)
            ·
              refine ⟨5805098967784112447681551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740131957045483263575401 5805098967784112447681551)
              ·
                refine ⟨8707648451676168671522327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805098967784112447681551 8707648451676168671522327)
                ·
                  refine ⟨13061472677514253007283491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707648451676168671522327 13061472677514253007283491)
                  ·
                    refine ⟨19592209016271379510925237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13061472677514253007283491 19592209016271379510925237)
                    ·
                      refine ⟨1836769595275441829149241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19592209016271379510925237 1836769595275441829149241)
                      ·
                        rfl

theorem cell23_3577096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3577096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577096 prefixEnd_3577096 := by exact prefixLift 3577096
  have htrace : WordTrace (prefixWord ++ tailWord_3577096) baseStart_3577096 baseEnd_3577096 := by
    simpa [prefixWord, tailWord_3577096, baseEnd_3577096] using wordTrace_append hprefix tailTrace_3577096
  have hstable : (prefixWord ++ tailWord_3577096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577096).length < 2 ^ (prefixWord ++ tailWord_3577096).sum := by decide
  have hdescent : baseEnd_3577096 < baseStart_3577096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577120 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_3577120 : Nat := 118140960795 + 3577120 * 2 ^ 59
def prefixEnd_3577120 : Nat := 4983230072969 + 3 ^ 40 * 3577120 * 2
def baseEnd_3577120 : Nat := 612260639603716578416377

theorem tailTrace_3577120 : CollatzResearch.WordTrace tailWord_3577120 prefixEnd_3577120 612260639603716578416377 := by
  unfold tailWord_3577120
  simp only [CollatzResearch.WordTrace]
  refine ⟨65234142400356319151504407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86978856533808425535339209 65234142400356319151504407)
  ·
    refine ⟨97851213600534478727256611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65234142400356319151504407 97851213600534478727256611)
    ·
      refine ⟨146776820400801718090884917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97851213600534478727256611 146776820400801718090884917)
      ·
        refine ⟨13760326912575161071020461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146776820400801718090884917 13760326912575161071020461)
        ·
          refine ⟨5160122592215685401632673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13760326912575161071020461 5160122592215685401632673)
          ·
            refine ⟨3870091944161764051224505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160122592215685401632673 3870091944161764051224505)
            ·
              refine ⟨2902568958121323038418379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870091944161764051224505 2902568958121323038418379)
              ·
                refine ⟨4353853437181984557627569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902568958121323038418379 4353853437181984557627569)
                ·
                  refine ⟨3265390077886488418220677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4353853437181984557627569 3265390077886488418220677)
                  ·
                    refine ⟨612260639603716578416377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265390077886488418220677 612260639603716578416377)
                    ·
                      rfl

theorem cell23_3577120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_3577120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577120 prefixEnd_3577120 := by exact prefixLift 3577120
  have htrace : WordTrace (prefixWord ++ tailWord_3577120) baseStart_3577120 baseEnd_3577120 := by
    simpa [prefixWord, tailWord_3577120, baseEnd_3577120] using wordTrace_append hprefix tailTrace_3577120
  have hstable : (prefixWord ++ tailWord_3577120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577120).length < 2 ^ (prefixWord ++ tailWord_3577120).sum := by decide
  have hdescent : baseEnd_3577120 < baseStart_3577120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577130 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3577130 : Nat := 118140960795 + 3577130 * 2 ^ 59
def prefixEnd_3577130 : Nat := 4983230072969 + 3 ^ 40 * 3577130 * 2
def baseEnd_3577130 : Nat := 1836787053617694696124085

theorem tailTrace_3577130 : CollatzResearch.WordTrace tailWord_3577130 prefixEnd_3577130 1836787053617694696124085 := by
  unfold tailWord_3577130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617162382669102502718211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86979099687117606673915229 32617162382669102502718211)
  ·
    refine ⟨48925743574003653754077317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32617162382669102502718211 48925743574003653754077317)
    ·
      refine ⟨9173576920125685078889497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48925743574003653754077317 9173576920125685078889497)
      ·
        refine ⟨6880182690094263809167123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9173576920125685078889497 6880182690094263809167123)
        ·
          refine ⟨10320274035141395713750685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880182690094263809167123 10320274035141395713750685)
          ·
            refine ⟨3870102763178023392656507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10320274035141395713750685 3870102763178023392656507)
            ·
              refine ⟨5805154144767035088984761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870102763178023392656507 5805154144767035088984761)
              ·
                refine ⟨4353865608575276316738571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805154144767035088984761 4353865608575276316738571)
                ·
                  refine ⟨6530798412862914475107857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353865608575276316738571 6530798412862914475107857)
                  ·
                    refine ⟨4898098809647185856330893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6530798412862914475107857 4898098809647185856330893)
                    ·
                      refine ⟨1836787053617694696124085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898098809647185856330893 1836787053617694696124085)
                      ·
                        rfl

theorem cell23_3577130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3577130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577130 prefixEnd_3577130 := by exact prefixLift 3577130
  have htrace : WordTrace (prefixWord ++ tailWord_3577130) baseStart_3577130 baseEnd_3577130 := by
    simpa [prefixWord, tailWord_3577130, baseEnd_3577130] using wordTrace_append hprefix tailTrace_3577130
  have hstable : (prefixWord ++ tailWord_3577130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577130).length < 2 ^ (prefixWord ++ tailWord_3577130).sum := by decide
  have hdescent : baseEnd_3577130 < baseStart_3577130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577132 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3577132 : Nat := 118140960795 + 3577132 * 2 ^ 59
def prefixEnd_3577132 : Nat := 4983230072969 + 3 ^ 40 * 3577132 * 2
def baseEnd_3577132 : Nat := 1836788080579003688299075

theorem tailTrace_3577132 : CollatzResearch.WordTrace tailWord_3577132 prefixEnd_3577132 1836788080579003688299075 := by
  unfold tailWord_3577132
  simp only [CollatzResearch.WordTrace]
  refine ⟨65234361238334582176222825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86979148317779442901630433 65234361238334582176222825)
  ·
    refine ⟨48925770928750936632167119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65234361238334582176222825 48925770928750936632167119)
    ·
      refine ⟨73388656393126404948250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48925770928750936632167119 73388656393126404948250679)
      ·
        refine ⟨110082984589689607422376019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73388656393126404948250679 110082984589689607422376019)
        ·
          refine ⟨165124476884534411133564029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110082984589689607422376019 165124476884534411133564029)
          ·
            refine ⟨61921678831700404175086511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165124476884534411133564029 61921678831700404175086511)
            ·
              refine ⟨92882518247550606262629767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61921678831700404175086511 92882518247550606262629767)
              ·
                refine ⟨139323777371325909393944651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92882518247550606262629767 139323777371325909393944651)
                ·
                  refine ⟨208985666056988864090916977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139323777371325909393944651 208985666056988864090916977)
                  ·
                    refine ⟨156739249542741648068187733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208985666056988864090916977 156739249542741648068187733)
                    ·
                      refine ⟨1836788080579003688299075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156739249542741648068187733 1836788080579003688299075)
                      ·
                        rfl

theorem cell23_3577132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3577132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577132 prefixEnd_3577132 := by exact prefixLift 3577132
  have htrace : WordTrace (prefixWord ++ tailWord_3577132) baseStart_3577132 baseEnd_3577132 := by
    simpa [prefixWord, tailWord_3577132, baseEnd_3577132] using wordTrace_append hprefix tailTrace_3577132
  have hstable : (prefixWord ++ tailWord_3577132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577132).length < 2 ^ (prefixWord ++ tailWord_3577132).sum := by decide
  have hdescent : baseEnd_3577132 < baseStart_3577132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577136 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2]
def baseStart_3577136 : Nat := 118140960795 + 3577136 * 2 ^ 59
def prefixEnd_3577136 : Nat := 4983230072969 + 3 ^ 40 * 3577136 * 2
def baseEnd_3577136 : Nat := 1836790134501621672649057

theorem tailTrace_3577136 : CollatzResearch.WordTrace tailWord_3577136 prefixEnd_3577136 1836790134501621672649057 := by
  unfold tailWord_3577136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65234434184327336517795631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86979245579103115357060841 65234434184327336517795631)
  ·
    refine ⟨97851651276491004776693447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65234434184327336517795631 97851651276491004776693447)
    ·
      refine ⟨146777476914736507165040171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97851651276491004776693447 146777476914736507165040171)
      ·
        refine ⟨220166215372104760747560257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146777476914736507165040171 220166215372104760747560257)
        ·
          refine ⟨165124661529078570560670193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220166215372104760747560257 165124661529078570560670193)
          ·
            refine ⟨123843496146808927920502645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165124661529078570560670193 123843496146808927920502645)
            ·
              refine ⟨11610327763763336992547123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123843496146808927920502645 11610327763763336992547123)
              ·
                refine ⟨17415491645645005488820685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610327763763336992547123 17415491645645005488820685)
                ·
                  refine ⟨6530809367116877058307757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17415491645645005488820685 6530809367116877058307757)
                  ·
                    refine ⟨2449053512668828896865409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6530809367116877058307757 2449053512668828896865409)
                    ·
                      refine ⟨1836790134501621672649057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449053512668828896865409 1836790134501621672649057)
                      ·
                        rfl

theorem cell23_3577136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2].length) (baseStart_3577136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577136 prefixEnd_3577136 := by exact prefixLift 3577136
  have htrace : WordTrace (prefixWord ++ tailWord_3577136) baseStart_3577136 baseEnd_3577136 := by
    simpa [prefixWord, tailWord_3577136, baseEnd_3577136] using wordTrace_append hprefix tailTrace_3577136
  have hstable : (prefixWord ++ tailWord_3577136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577136).length < 2 ^ (prefixWord ++ tailWord_3577136).sum := by decide
  have hdescent : baseEnd_3577136 < baseStart_3577136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577166 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_3577166 : Nat := 118140960795 + 3577166 * 2 ^ 59
def prefixEnd_3577166 : Nat := 4983230072969 + 3 ^ 40 * 3577166 * 2
def baseEnd_3577166 : Nat := 1836805538921256555273919

theorem tailTrace_3577166 : CollatzResearch.WordTrace tailWord_3577166 prefixEnd_3577166 1836805538921256555273919 := by
  unfold tailWord_3577166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308745319818248519897919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86979975039030658772788901 16308745319818248519897919)
  ·
    refine ⟨24463117979727372779846879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16308745319818248519897919 24463117979727372779846879)
    ·
      refine ⟨36694676969591059169770319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24463117979727372779846879 36694676969591059169770319)
      ·
        refine ⟨55042015454386588754655479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36694676969591059169770319 55042015454386588754655479)
        ·
          refine ⟨82563023181579883131983219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55042015454386588754655479 82563023181579883131983219)
          ·
            refine ⟨123844534772369824697974829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82563023181579883131983219 123844534772369824697974829)
            ·
              refine ⟨46441700539638684261740561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123844534772369824697974829 46441700539638684261740561)
              ·
                refine ⟨34831275404729013196305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46441700539638684261740561 34831275404729013196305421)
                ·
                  refine ⟨13061728276773379948614533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34831275404729013196305421 13061728276773379948614533)
                  ·
                    refine ⟨2449074051895008740365225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13061728276773379948614533 2449074051895008740365225)
                    ·
                      refine ⟨1836805538921256555273919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449074051895008740365225 1836805538921256555273919)
                      ·
                        rfl

theorem cell23_3577166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_3577166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577166 prefixEnd_3577166 := by exact prefixLift 3577166
  have htrace : WordTrace (prefixWord ++ tailWord_3577166) baseStart_3577166 baseEnd_3577166 := by
    simpa [prefixWord, tailWord_3577166, baseEnd_3577166] using wordTrace_append hprefix tailTrace_3577166
  have hstable : (prefixWord ++ tailWord_3577166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577166).length < 2 ^ (prefixWord ++ tailWord_3577166).sum := by decide
  have hdescent : baseEnd_3577166 < baseStart_3577166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577169 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_3577169 : Nat := 118140960795 + 3577169 * 2 ^ 59
def prefixEnd_3577169 : Nat := 4983230072969 + 3 ^ 40 * 3577169 * 2
def baseEnd_3577169 : Nat := 1836807079363220043536405

theorem tailTrace_3577169 : CollatzResearch.WordTrace tailWord_3577169 prefixEnd_3577169 1836807079363220043536405 := by
  unfold tailWord_3577169
  simp only [CollatzResearch.WordTrace]
  refine ⟨130470071977535119671542561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86980047985023413114361707 130470071977535119671542561)
  ·
    refine ⟨97852553983151339753656921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130470071977535119671542561 97852553983151339753656921)
    ·
      refine ⟨73389415487363504815242691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97852553983151339753656921 73389415487363504815242691)
      ·
        refine ⟨110084123231045257222864037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73389415487363504815242691 110084123231045257222864037)
        ·
          refine ⟨20640773105820985729287007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110084123231045257222864037 20640773105820985729287007)
          ·
            refine ⟨30961159658731478593930511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20640773105820985729287007 30961159658731478593930511)
            ·
              refine ⟨46441739488097217890895767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30961159658731478593930511 46441739488097217890895767)
              ·
                refine ⟨69662609232145826836343651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46441739488097217890895767 69662609232145826836343651)
                ·
                  refine ⟨104493913848218740254515477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69662609232145826836343651 104493913848218740254515477)
                  ·
                    refine ⟨4898152211635253449430413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104493913848218740254515477 4898152211635253449430413)
                    ·
                      refine ⟨1836807079363220043536405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898152211635253449430413 1836807079363220043536405)
                      ·
                        rfl

theorem cell23_3577169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_3577169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577169 prefixEnd_3577169 := by exact prefixLift 3577169
  have htrace : WordTrace (prefixWord ++ tailWord_3577169) baseStart_3577169 baseEnd_3577169 := by
    simpa [prefixWord, tailWord_3577169, baseEnd_3577169] using wordTrace_append hprefix tailTrace_3577169
  have hstable : (prefixWord ++ tailWord_3577169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577169).length < 2 ^ (prefixWord ++ tailWord_3577169).sum := by decide
  have hdescent : baseEnd_3577169 < baseStart_3577169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577186 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3577186 : Nat := 118140960795 + 3577186 * 2 ^ 59
def prefixEnd_3577186 : Nat := 4983230072969 + 3 ^ 40 * 3577186 * 2
def baseEnd_3577186 : Nat := 1836815808534346477023827

theorem tailTrace_3577186 : CollatzResearch.WordTrace tailWord_3577186 prefixEnd_3577186 1836815808534346477023827 := by
  unfold tailWord_3577186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617673004618382893727853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86980461345649021049940941 32617673004618382893727853)
  ·
    refine ⟨12231627376731893585147945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32617673004618382893727853 12231627376731893585147945)
    ·
      refine ⟨9173720532548920188860959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12231627376731893585147945 9173720532548920188860959)
      ·
        refine ⟨13760580798823380283291439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173720532548920188860959 13760580798823380283291439)
        ·
          refine ⟨20640871198235070424937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760580798823380283291439 20640871198235070424937159)
          ·
            refine ⟨30961306797352605637405739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20640871198235070424937159 30961306797352605637405739)
            ·
              refine ⟨46441960196028908456108609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30961306797352605637405739 46441960196028908456108609)
              ·
                refine ⟨34831470147021681342081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46441960196028908456108609 34831470147021681342081457)
                ·
                  refine ⟨26123602610266261006561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34831470147021681342081457 26123602610266261006561093)
                  ·
                    refine ⟨4898175489424923938730205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26123602610266261006561093 4898175489424923938730205)
                    ·
                      refine ⟨1836815808534346477023827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898175489424923938730205 1836815808534346477023827)
                      ·
                        rfl

theorem cell23_3577186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3577186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577186 prefixEnd_3577186 := by exact prefixLift 3577186
  have htrace : WordTrace (prefixWord ++ tailWord_3577186) baseStart_3577186 baseEnd_3577186 := by
    simpa [prefixWord, tailWord_3577186, baseEnd_3577186] using wordTrace_append hprefix tailTrace_3577186
  have hstable : (prefixWord ++ tailWord_3577186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577186).length < 2 ^ (prefixWord ++ tailWord_3577186).sum := by decide
  have hdescent : baseEnd_3577186 < baseStart_3577186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577189 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 7]
def baseStart_3577189 : Nat := 118140960795 + 3577189 * 2 ^ 59
def prefixEnd_3577189 : Nat := 4983230072969 + 3 ^ 40 * 3577189 * 2
def baseEnd_3577189 : Nat := 204090816552923329476257

theorem tailTrace_3577189 : CollatzResearch.WordTrace tailWord_3577189 prefixEnd_3577189 204090816552923329476257 := by
  unfold tailWord_3577189
  simp only [CollatzResearch.WordTrace]
  refine ⟨130470801437462663087270621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86980534291641775391513747 130470801437462663087270621)
  ·
    refine ⟨48926550539048498657726483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130470801437462663087270621 48926550539048498657726483)
    ·
      refine ⟨73389825808572747986589725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48926550539048498657726483 73389825808572747986589725)
      ·
        refine ⟨27521184678214780494971147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73389825808572747986589725 27521184678214780494971147)
        ·
          refine ⟨41281777017322170742456721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27521184678214780494971147 41281777017322170742456721)
          ·
            refine ⟨30961332762991628056842541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41281777017322170742456721 30961332762991628056842541)
            ·
              refine ⟨11610499786121860521315953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30961332762991628056842541 11610499786121860521315953)
              ·
                refine ⟨8707874839591395390986965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11610499786121860521315953 8707874839591395390986965)
                ·
                  refine ⟨204090816552923329476257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8707874839591395390986965 204090816552923329476257)
                  ·
                    rfl

theorem cell23_3577189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_3577189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577189 prefixEnd_3577189 := by exact prefixLift 3577189
  have htrace : WordTrace (prefixWord ++ tailWord_3577189) baseStart_3577189 baseEnd_3577189 := by
    simpa [prefixWord, tailWord_3577189, baseEnd_3577189] using wordTrace_append hprefix tailTrace_3577189
  have hstable : (prefixWord ++ tailWord_3577189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577189).length < 2 ^ (prefixWord ++ tailWord_3577189).sum := by decide
  have hdescent : baseEnd_3577189 < baseStart_3577189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577199 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_3577199 : Nat := 118140960795 + 3577199 * 2 ^ 59
def prefixEnd_3577199 : Nat := 4983230072969 + 3 ^ 40 * 3577199 * 2
def baseEnd_3577199 : Nat := 1836822483782854926161267

theorem tailTrace_3577199 : CollatzResearch.WordTrace tailWord_3577199 prefixEnd_3577199 1836822483782854926161267 := by
  unfold tailWord_3577199
  simp only [CollatzResearch.WordTrace]
  refine ⟨130471166167426434795134651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86980777444950956530089767 130471166167426434795134651)
  ·
    refine ⟨195706749251139652192701977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130471166167426434795134651 195706749251139652192701977)
    ·
      refine ⟨146780061938354739144526483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195706749251139652192701977 146780061938354739144526483)
      ·
        refine ⟨220170092907532108716789725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146780061938354739144526483 220170092907532108716789725)
        ·
          refine ⟨82563784840324540768796147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220170092907532108716789725 82563784840324540768796147)
          ·
            refine ⟨123845677260486811153194221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82563784840324540768796147 123845677260486811153194221)
            ·
              refine ⟨46442128972682554182447833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123845677260486811153194221 46442128972682554182447833)
              ·
                refine ⟨34831596729511915636835875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46442128972682554182447833 34831596729511915636835875)
                ·
                  refine ⟨52247395094267873455253813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34831596729511915636835875 52247395094267873455253813)
                  ·
                    refine ⟨4898193290087613136430045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52247395094267873455253813 4898193290087613136430045)
                    ·
                      refine ⟨1836822483782854926161267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4898193290087613136430045 1836822483782854926161267)
                      ·
                        rfl

theorem cell23_3577199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_3577199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577199 prefixEnd_3577199 := by exact prefixLift 3577199
  have htrace : WordTrace (prefixWord ++ tailWord_3577199) baseStart_3577199 baseEnd_3577199 := by
    simpa [prefixWord, tailWord_3577199, baseEnd_3577199] using wordTrace_append hprefix tailTrace_3577199
  have hstable : (prefixWord ++ tailWord_3577199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577199).length < 2 ^ (prefixWord ++ tailWord_3577199).sum := by decide
  have hdescent : baseEnd_3577199 < baseStart_3577199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577234 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3577234 : Nat := 118140960795 + 3577234 * 2 ^ 59
def prefixEnd_3577234 : Nat := 4983230072969 + 3 ^ 40 * 3577234 * 2
def baseEnd_3577234 : Nat := 1836840455605762289223607

theorem tailTrace_3577234 : CollatzResearch.WordTrace tailWord_3577234 prefixEnd_3577234 1836840455605762289223607 := by
  unfold tailWord_3577234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618110680574908943164689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86981628481533090515105837 32618110680574908943164689)
  ·
    refine ⟨24463583010431181707373517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32618110680574908943164689 24463583010431181707373517)
    ·
      refine ⟨9173843628911693140265069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24463583010431181707373517 9173843628911693140265069)
      ·
        refine ⟨3440191360841884927599401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9173843628911693140265069 3440191360841884927599401)
        ·
          refine ⟨2580143520631413695699551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440191360841884927599401 2580143520631413695699551)
          ·
            refine ⟨3870215280947120543549327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580143520631413695699551 3870215280947120543549327)
            ·
              refine ⟨5805322921420680815323991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870215280947120543549327 5805322921420680815323991)
              ·
                refine ⟨8707984382131021222985987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805322921420680815323991 8707984382131021222985987)
                ·
                  refine ⟨13061976573196531834478981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707984382131021222985987 13061976573196531834478981)
                  ·
                    refine ⟨2449120607474349718964809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13061976573196531834478981 2449120607474349718964809)
                    ·
                      refine ⟨1836840455605762289223607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2449120607474349718964809 1836840455605762289223607)
                      ·
                        rfl

theorem cell23_3577234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3577234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3577234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3577234 prefixEnd_3577234 := by exact prefixLift 3577234
  have htrace : WordTrace (prefixWord ++ tailWord_3577234) baseStart_3577234 baseEnd_3577234 := by
    simpa [prefixWord, tailWord_3577234, baseEnd_3577234] using wordTrace_append hprefix tailTrace_3577234
  have hstable : (prefixWord ++ tailWord_3577234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577234).length < 2 ^ (prefixWord ++ tailWord_3577234).sum := by decide
  have hdescent : baseEnd_3577234 < baseStart_3577234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
