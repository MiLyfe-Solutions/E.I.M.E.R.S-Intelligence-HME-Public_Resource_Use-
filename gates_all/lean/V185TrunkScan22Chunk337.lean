import V185TrunkScan22Chunk336

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3006162 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3006162 : Nat := 118140960795 + 3006162 * 2 ^ 59
def prefixEnd_3006162 : Nat := 4983230072969 + 3 ^ 40 * 3006162 * 2
def baseEnd_3006162 : Nat := 1029070687520915074033279

theorem tailTrace_3006162 : CollatzResearch.WordTrace tailWord_3006162 prefixEnd_3006162 1029070687520915074033279 := by
  unfold tailWord_3006162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410933933798990109981185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73095823823463973626616493 27410933933798990109981185)
  ·
    refine ⟨20558200450349242582485889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27410933933798990109981185 20558200450349242582485889)
    ·
      refine ⟨15418650337761931936864417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20558200450349242582485889 15418650337761931936864417)
      ·
        refine ⟨11563987753321448952648313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15418650337761931936864417 11563987753321448952648313)
        ·
          refine ⟨8672990814991086714486235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563987753321448952648313 8672990814991086714486235)
          ·
            refine ⟨13009486222486630071729353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672990814991086714486235 13009486222486630071729353)
            ·
              refine ⟨9757114666864972553797015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13009486222486630071729353 9757114666864972553797015)
              ·
                refine ⟨14635672000297458830695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757114666864972553797015 14635672000297458830695523)
                ·
                  refine ⟨21953508000446188246043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14635672000297458830695523 21953508000446188246043285)
                  ·
                    refine ⟨1029070687520915074033279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21953508000446188246043285 1029070687520915074033279)
                    ·
                      rfl

theorem cell22_3006162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3006162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006162 prefixEnd_3006162 := by exact prefixLift 3006162
  have htrace : WordTrace (prefixWord ++ tailWord_3006162) baseStart_3006162 baseEnd_3006162 := by
    simpa [prefixWord, tailWord_3006162, baseEnd_3006162] using wordTrace_append hprefix tailTrace_3006162
  have hstable : (prefixWord ++ tailWord_3006162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006162).length < 2 ^ (prefixWord ++ tailWord_3006162).sum := by decide
  have hdescent : baseEnd_3006162 < baseStart_3006162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006164 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3006164 : Nat := 118140960795 + 3006164 * 2 ^ 59
def prefixEnd_3006164 : Nat := 4983230072969 + 3 ^ 40 * 3006164 * 2
def baseEnd_3006164 : Nat := 1029071372161787735483273

theorem tailTrace_3006164 : CollatzResearch.WordTrace tailWord_3006164 prefixEnd_3006164 1029071372161787735483273 := by
  unfold tailWord_3006164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821904340594357390748773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73095872454125809854331697 54821904340594357390748773)
  ·
    refine ⟨10279107063861442010765395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54821904340594357390748773 10279107063861442010765395)
    ·
      refine ⟨15418660595792163016148093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279107063861442010765395 15418660595792163016148093)
      ·
        refine ⟨5781997723422061131055535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15418660595792163016148093 5781997723422061131055535)
        ·
          refine ⟨8672996585133091696583303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781997723422061131055535 8672996585133091696583303)
          ·
            refine ⟨13009494877699637544874955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672996585133091696583303 13009494877699637544874955)
            ·
              refine ⟨19514242316549456317312433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009494877699637544874955 19514242316549456317312433)
              ·
                refine ⟨14635681737412092237984325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19514242316549456317312433 14635681737412092237984325)
                ·
                  refine ⟨2744190325764767294622061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14635681737412092237984325 2744190325764767294622061)
                  ·
                    refine ⟨1029071372161787735483273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744190325764767294622061 1029071372161787735483273)
                    ·
                      rfl

theorem cell22_3006164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3006164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006164 prefixEnd_3006164 := by exact prefixLift 3006164
  have htrace : WordTrace (prefixWord ++ tailWord_3006164) baseStart_3006164 baseEnd_3006164 := by
    simpa [prefixWord, tailWord_3006164, baseEnd_3006164] using wordTrace_append hprefix tailTrace_3006164
  have hstable : (prefixWord ++ tailWord_3006164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006164).length < 2 ^ (prefixWord ++ tailWord_3006164).sum := by decide
  have hdescent : baseEnd_3006164 < baseStart_3006164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006177 : List Nat := [1, 2, 3, 1, 5, 2, 8]
def baseStart_3006177 : Nat := 118140960795 + 3006177 * 2 ^ 59
def prefixEnd_3006177 : Nat := 4983230072969 + 3 ^ 40 * 3006177 * 2
def baseEnd_3006177 : Nat := 38113919345461482774379

theorem tailTrace_3006177 : CollatzResearch.WordTrace tailWord_3006177 prefixEnd_3006177 38113919345461482774379 := by
  unfold tailWord_3006177
  simp only [CollatzResearch.WordTrace]
  refine ⟨109644282830141618001720785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73096188553427745334480523 109644282830141618001720785)
  ·
    refine ⟨82233212122606213501290589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109644282830141618001720785 82233212122606213501290589)
    ·
      refine ⟨30837454545977330062983971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82233212122606213501290589 30837454545977330062983971)
      ·
        refine ⟨46256181818965995094475957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30837454545977330062983971 46256181818965995094475957)
        ·
          refine ⟨4336517045528062040107121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46256181818965995094475957 4336517045528062040107121)
          ·
            refine ⟨3252387784146046530080341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4336517045528062040107121 3252387784146046530080341)
            ·
              refine ⟨38113919345461482774379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3252387784146046530080341 38113919345461482774379)
              ·
                rfl

theorem cell22_3006177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 8].length) (baseStart_3006177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006177 prefixEnd_3006177 := by exact prefixLift 3006177
  have htrace : WordTrace (prefixWord ++ tailWord_3006177) baseStart_3006177 baseEnd_3006177 := by
    simpa [prefixWord, tailWord_3006177, baseEnd_3006177] using wordTrace_append hprefix tailTrace_3006177
  have hstable : (prefixWord ++ tailWord_3006177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006177).length < 2 ^ (prefixWord ++ tailWord_3006177).sum := by decide
  have hdescent : baseEnd_3006177 < baseStart_3006177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006179 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_3006179 : Nat := 118140960795 + 3006179 * 2 ^ 59
def prefixEnd_3006179 : Nat := 4983230072969 + 3 ^ 40 * 3006179 * 2
def baseEnd_3006179 : Nat := 1029076506968332696358227

theorem tailTrace_3006179 : CollatzResearch.WordTrace tailWord_3006179 prefixEnd_3006179 1029076506968332696358227 := by
  unfold tailWord_3006179
  simp only [CollatzResearch.WordTrace]
  refine ⟨109644355776134372343293591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73096237184089581562195727 109644355776134372343293591)
  ·
    refine ⟨164466533664201558514940387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109644355776134372343293591 164466533664201558514940387)
    ·
      refine ⟨246699800496302337772410581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164466533664201558514940387 246699800496302337772410581)
      ·
        refine ⟨5782026574132086041540873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 246699800496302337772410581 5782026574132086041540873)
        ·
          refine ⟨4336519930599064531155655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5782026574132086041540873 4336519930599064531155655)
          ·
            refine ⟨6504779895898596796733483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336519930599064531155655 6504779895898596796733483)
            ·
              refine ⟨9757169843847895195100225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504779895898596796733483 9757169843847895195100225)
              ·
                refine ⟨7317877382885921396325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9757169843847895195100225 7317877382885921396325169)
                ·
                  refine ⟨5488408037164441047243877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317877382885921396325169 5488408037164441047243877)
                  ·
                    refine ⟨1029076506968332696358227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488408037164441047243877 1029076506968332696358227)
                    ·
                      rfl

theorem cell22_3006179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_3006179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006179 prefixEnd_3006179 := by exact prefixLift 3006179
  have htrace : WordTrace (prefixWord ++ tailWord_3006179) baseStart_3006179 baseEnd_3006179 := by
    simpa [prefixWord, tailWord_3006179, baseEnd_3006179] using wordTrace_append hprefix tailTrace_3006179
  have hstable : (prefixWord ++ tailWord_3006179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006179).length < 2 ^ (prefixWord ++ tailWord_3006179).sum := by decide
  have hdescent : baseEnd_3006179 < baseStart_3006179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006183 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 4]
def baseStart_3006183 : Nat := 118140960795 + 3006183 * 2 ^ 59
def prefixEnd_3006183 : Nat := 4983230072969 + 3 ^ 40 * 3006183 * 2
def baseEnd_3006183 : Nat := 343025958750026006419405

theorem tailTrace_3006183 : CollatzResearch.WordTrace tailWord_3006183 prefixEnd_3006183 343025958750026006419405 := by
  unfold tailWord_3006183
  simp only [CollatzResearch.WordTrace]
  refine ⟨109644501668119881026439203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73096334445413254017626135 109644501668119881026439203)
  ·
    refine ⟨164466752502179821539658805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109644501668119881026439203 164466752502179821539658805)
    ·
      refine ⟨15418758047079358269343013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164466752502179821539658805 15418758047079358269343013)
      ·
        refine ⟨2891017133827379675501815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15418758047079358269343013 2891017133827379675501815)
        ·
          refine ⟨4336525700741069513252723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891017133827379675501815 4336525700741069513252723)
          ·
            refine ⟨6504788551111604269879085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336525700741069513252723 6504788551111604269879085)
            ·
              refine ⟨2439295706666851601204657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6504788551111604269879085 2439295706666851601204657)
              ·
                refine ⟨1829471780000138700903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439295706666851601204657 1829471780000138700903493)
                ·
                  refine ⟨343025958750026006419405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829471780000138700903493 343025958750026006419405)
                  ·
                    rfl

theorem cell22_3006183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 4].length) (baseStart_3006183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006183 prefixEnd_3006183 := by exact prefixLift 3006183
  have htrace : WordTrace (prefixWord ++ tailWord_3006183) baseStart_3006183 baseEnd_3006183 := by
    simpa [prefixWord, tailWord_3006183, baseEnd_3006183] using wordTrace_append hprefix tailTrace_3006183
  have hstable : (prefixWord ++ tailWord_3006183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006183).length < 2 ^ (prefixWord ++ tailWord_3006183).sum := by decide
  have hdescent : baseEnd_3006183 < baseStart_3006183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006192 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_3006192 : Nat := 118140960795 + 3006192 * 2 ^ 59
def prefixEnd_3006192 : Nat := 4983230072969 + 3 ^ 40 * 3006192 * 2
def baseEnd_3006192 : Nat := 1029080957134004995783187

theorem tailTrace_3006192 : CollatzResearch.WordTrace tailWord_3006192 prefixEnd_3006192 1029080957134004995783187 := by
  unfold tailWord_3006192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54822414962543637781758415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73096553283391517042344553 54822414962543637781758415)
  ·
    refine ⟨82233622443815456672637623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54822414962543637781758415 82233622443815456672637623)
    ·
      refine ⟨123350433665723185008956435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82233622443815456672637623 123350433665723185008956435)
      ·
        refine ⟨185025650498584777513434653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123350433665723185008956435 185025650498584777513434653)
        ·
          refine ⟨69384618936969291567537995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185025650498584777513434653 69384618936969291567537995)
          ·
            refine ⟨104076928405453937351306993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69384618936969291567537995 104076928405453937351306993)
            ·
              refine ⟨78057696304090453013480245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104076928405453937351306993 78057696304090453013480245)
              ·
                refine ⟨7317909028508479970013773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78057696304090453013480245 7317909028508479970013773)
                ·
                  refine ⟨2744215885690679988755165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7317909028508479970013773 2744215885690679988755165)
                  ·
                    refine ⟨1029080957134004995783187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744215885690679988755165 1029080957134004995783187)
                    ·
                      rfl

theorem cell22_3006192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_3006192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006192 prefixEnd_3006192 := by exact prefixLift 3006192
  have htrace : WordTrace (prefixWord ++ tailWord_3006192) baseStart_3006192 baseEnd_3006192 := by
    simpa [prefixWord, tailWord_3006192, baseEnd_3006192] using wordTrace_append hprefix tailTrace_3006192
  have hstable : (prefixWord ++ tailWord_3006192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006192).length < 2 ^ (prefixWord ++ tailWord_3006192).sum := by decide
  have hdescent : baseEnd_3006192 < baseStart_3006192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006198 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3006198 : Nat := 118140960795 + 3006198 * 2 ^ 59
def prefixEnd_3006198 : Nat := 4983230072969 + 3 ^ 40 * 3006198 * 2
def baseEnd_3006198 : Nat := 1029083011056622980133169

theorem tailTrace_3006198 : CollatzResearch.WordTrace tailWord_3006198 prefixEnd_3006198 1029083011056622980133169 := by
  unfold tailWord_3006198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852815547691596161764703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73096699175377025725490165 6852815547691596161764703)
  ·
    refine ⟨10279223321537394242647055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6852815547691596161764703 10279223321537394242647055)
    ·
      refine ⟨15418834982306091363970583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279223321537394242647055 15418834982306091363970583)
      ·
        refine ⟨23128252473459137045955875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15418834982306091363970583 23128252473459137045955875)
        ·
          refine ⟨34692378710188705568933813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23128252473459137045955875 34692378710188705568933813)
          ·
            refine ⟨3252410504080191147087545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34692378710188705568933813 3252410504080191147087545)
            ·
              refine ⟨2439307878060143360315659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252410504080191147087545 2439307878060143360315659)
              ·
                refine ⟨3658961817090215040473489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439307878060143360315659 3658961817090215040473489)
                ·
                  refine ⟨2744221362817661280355117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658961817090215040473489 2744221362817661280355117)
                  ·
                    refine ⟨1029083011056622980133169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744221362817661280355117 1029083011056622980133169)
                    ·
                      rfl

theorem cell22_3006198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3006198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006198 prefixEnd_3006198 := by exact prefixLift 3006198
  have htrace : WordTrace (prefixWord ++ tailWord_3006198) baseStart_3006198 baseEnd_3006198 := by
    simpa [prefixWord, tailWord_3006198, baseEnd_3006198] using wordTrace_append hprefix tailTrace_3006198
  have hstable : (prefixWord ++ tailWord_3006198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006198).length < 2 ^ (prefixWord ++ tailWord_3006198).sum := by decide
  have hdescent : baseEnd_3006198 < baseStart_3006198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006205 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3006205 : Nat := 118140960795 + 3006205 * 2 ^ 59
def prefixEnd_3006205 : Nat := 4983230072969 + 3 ^ 40 * 3006205 * 2
def baseEnd_3006205 : Nat := 343028469099892431736049

theorem tailTrace_3006205 : CollatzResearch.WordTrace tailWord_3006205 prefixEnd_3006205 343028469099892431736049 := by
  unfold tailWord_3006205
  simp only [CollatzResearch.WordTrace]
  refine ⟨109645304074040178783740069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73096869382693452522493379 109645304074040178783740069)
  ·
    refine ⟨20558494513882533521951263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109645304074040178783740069 20558494513882533521951263)
    ·
      refine ⟨30837741770823800282926895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20558494513882533521951263 30837741770823800282926895)
      ·
        refine ⟨46256612656235700424390343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30837741770823800282926895 46256612656235700424390343)
        ·
          refine ⟨69384918984353550636585515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46256612656235700424390343 69384918984353550636585515)
          ·
            refine ⟨104077378476530325954878273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69384918984353550636585515 104077378476530325954878273)
            ·
              refine ⟨78058033857397744466158705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104077378476530325954878273 78058033857397744466158705)
              ·
                refine ⟨58543525393048308349619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78058033857397744466158705 58543525393048308349619029)
                ·
                  refine ⟨343028469099892431736049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58543525393048308349619029 343028469099892431736049)
                  ·
                    rfl

theorem cell22_3006205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3006205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006205 prefixEnd_3006205 := by exact prefixLift 3006205
  have htrace : WordTrace (prefixWord ++ tailWord_3006205) baseStart_3006205 baseEnd_3006205 := by
    simpa [prefixWord, tailWord_3006205, baseEnd_3006205] using wordTrace_append hprefix tailTrace_3006205
  have hstable : (prefixWord ++ tailWord_3006205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006205).length < 2 ^ (prefixWord ++ tailWord_3006205).sum := by decide
  have hdescent : baseEnd_3006205 < baseStart_3006205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006252 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_3006252 : Nat := 118140960795 + 3006252 * 2 ^ 59
def prefixEnd_3006252 : Nat := 4983230072969 + 3 ^ 40 * 3006252 * 2
def baseEnd_3006252 : Nat := 1029101496360184839283003

theorem tailTrace_3006252 : CollatzResearch.WordTrace tailWord_3006252 prefixEnd_3006252 1029101496360184839283003 := by
  unfold tailWord_3006252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54823509152434952905350505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73098012203246603873800673 54823509152434952905350505)
  ·
    refine ⟨41117631864326214679012879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54823509152434952905350505 41117631864326214679012879)
    ·
      refine ⟨61676447796489322018519319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41117631864326214679012879 61676447796489322018519319)
      ·
        refine ⟨92514671694733983027778979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61676447796489322018519319 92514671694733983027778979)
        ·
          refine ⟨138772007542100974541668469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92514671694733983027778979 138772007542100974541668469)
          ·
            refine ⟨13009875707071966363281419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138772007542100974541668469 13009875707071966363281419)
            ·
              refine ⟨19514813560607949544922129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009875707071966363281419 19514813560607949544922129)
              ·
                refine ⟨14636110170455962158691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19514813560607949544922129 14636110170455962158691597)
                ·
                  refine ⟨5488541313920985809509349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14636110170455962158691597 5488541313920985809509349)
                  ·
                    refine ⟨1029101496360184839283003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488541313920985809509349 1029101496360184839283003)
                    ·
                      rfl

theorem cell22_3006252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_3006252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006252 prefixEnd_3006252 := by exact prefixLift 3006252
  have htrace : WordTrace (prefixWord ++ tailWord_3006252) baseStart_3006252 baseEnd_3006252 := by
    simpa [prefixWord, tailWord_3006252, baseEnd_3006252] using wordTrace_append hprefix tailTrace_3006252
  have hstable : (prefixWord ++ tailWord_3006252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006252).length < 2 ^ (prefixWord ++ tailWord_3006252).sum := by decide
  have hdescent : baseEnd_3006252 < baseStart_3006252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006269 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3006269 : Nat := 118140960795 + 3006269 * 2 ^ 59
def prefixEnd_3006269 : Nat := 4983230072969 + 3 ^ 40 * 3006269 * 2
def baseEnd_3006269 : Nat := 1029107315807602461607951

theorem tailTrace_3006269 : CollatzResearch.WordTrace tailWord_3006269 prefixEnd_3006269 1029107315807602461607951 := by
  unfold tailWord_3006269
  simp only [CollatzResearch.WordTrace]
  refine ⟨109647638345808317714069861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73098425563872211809379907 109647638345808317714069861)
  ·
    refine ⟨20558932189839059571388099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109647638345808317714069861 20558932189839059571388099)
    ·
      refine ⟨30838398284758589357082149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20558932189839059571388099 30838398284758589357082149)
      ·
        refine ⟨5782199678392235504452903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30838398284758589357082149 5782199678392235504452903)
        ·
          refine ⟨8673299517588353256679355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782199678392235504452903 8673299517588353256679355)
          ·
            refine ⟨13009949276382529885019033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673299517588353256679355 13009949276382529885019033)
            ·
              refine ⟨9757461957286897413764275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13009949276382529885019033 9757461957286897413764275)
              ·
                refine ⟨14636192935930346120646413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757461957286897413764275 14636192935930346120646413)
                ·
                  refine ⟨5488572350973879795242405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14636192935930346120646413 5488572350973879795242405)
                  ·
                    refine ⟨1029107315807602461607951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488572350973879795242405 1029107315807602461607951)
                    ·
                      rfl

theorem cell22_3006269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3006269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006269 prefixEnd_3006269 := by exact prefixLift 3006269
  have htrace : WordTrace (prefixWord ++ tailWord_3006269) baseStart_3006269 baseEnd_3006269 := by
    simpa [prefixWord, tailWord_3006269, baseEnd_3006269] using wordTrace_append hprefix tailTrace_3006269
  have hstable : (prefixWord ++ tailWord_3006269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006269).length < 2 ^ (prefixWord ++ tailWord_3006269).sum := by decide
  have hdescent : baseEnd_3006269 < baseStart_3006269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006282 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3006282 : Nat := 118140960795 + 3006282 * 2 ^ 59
def prefixEnd_3006282 : Nat := 4983230072969 + 3 ^ 40 * 3006282 * 2
def baseEnd_3006282 : Nat := 1029111765973274761032911

theorem tailTrace_3006282 : CollatzResearch.WordTrace tailWord_3006282 prefixEnd_3006282 1029111765973274761032911 := by
  unfold tailWord_3006282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412028123690305233573275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73098741663174147289528733 27412028123690305233573275)
  ·
    refine ⟨41118042185535457850359913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412028123690305233573275 41118042185535457850359913)
    ·
      refine ⟨30838531639151593387769935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41118042185535457850359913 30838531639151593387769935)
      ·
        refine ⟨46257797458727390081654903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30838531639151593387769935 46257797458727390081654903)
        ·
          refine ⟨69386696188091085122482355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46257797458727390081654903 69386696188091085122482355)
          ·
            refine ⟨104080044282136627683723533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69386696188091085122482355 104080044282136627683723533)
            ·
              refine ⟨39030016605801235381396325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104080044282136627683723533 39030016605801235381396325)
              ·
                refine ⟨7318128113587731634011811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39030016605801235381396325 7318128113587731634011811)
                ·
                  refine ⟨10977192170381597451017717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7318128113587731634011811 10977192170381597451017717)
                  ·
                    refine ⟨1029111765973274761032911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10977192170381597451017717 1029111765973274761032911)
                    ·
                      rfl

theorem cell22_3006282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3006282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006282 prefixEnd_3006282 := by exact prefixLift 3006282
  have htrace : WordTrace (prefixWord ++ tailWord_3006282) baseStart_3006282 baseEnd_3006282 := by
    simpa [prefixWord, tailWord_3006282, baseEnd_3006282] using wordTrace_append hprefix tailTrace_3006282
  have hstable : (prefixWord ++ tailWord_3006282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006282).length < 2 ^ (prefixWord ++ tailWord_3006282).sum := by decide
  have hdescent : baseEnd_3006282 < baseStart_3006282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006297 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_3006297 : Nat := 118140960795 + 3006297 * 2 ^ 59
def prefixEnd_3006297 : Nat := 4983230072969 + 3 ^ 40 * 3006297 * 2
def baseEnd_3006297 : Nat := 1029116900779819721907865

theorem tailTrace_3006297 : CollatzResearch.WordTrace tailWord_3006297 prefixEnd_3006297 1029116900779819721907865 := by
  unfold tailWord_3006297
  simp only [CollatzResearch.WordTrace]
  refine ⟨109648659589706878496089145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73099106393137918997392763 109648659589706878496089145)
  ·
    refine ⟨82236494692280158872066859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109648659589706878496089145 82236494692280158872066859)
    ·
      refine ⟨123354742038420238308100289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82236494692280158872066859 123354742038420238308100289)
      ·
        refine ⟨92516056528815178731075217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123354742038420238308100289 92516056528815178731075217)
        ·
          refine ⟨69387042396611384048306413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92516056528815178731075217 69387042396611384048306413)
          ·
            refine ⟨26020140898729269018114905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69387042396611384048306413 26020140898729269018114905)
            ·
              refine ⟨19515105674046951763586179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26020140898729269018114905 19515105674046951763586179)
              ·
                refine ⟨29272658511070427645379269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19515105674046951763586179 29272658511070427645379269)
                ·
                  refine ⟨5488623470825705183508613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29272658511070427645379269 5488623470825705183508613)
                  ·
                    refine ⟨1029116900779819721907865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488623470825705183508613 1029116900779819721907865)
                    ·
                      rfl

theorem cell22_3006297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_3006297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006297 prefixEnd_3006297 := by exact prefixLift 3006297
  have htrace : WordTrace (prefixWord ++ tailWord_3006297) baseStart_3006297 baseEnd_3006297 := by
    simpa [prefixWord, tailWord_3006297, baseEnd_3006297] using wordTrace_append hprefix tailTrace_3006297
  have hstable : (prefixWord ++ tailWord_3006297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006297).length < 2 ^ (prefixWord ++ tailWord_3006297).sum := by decide
  have hdescent : baseEnd_3006297 < baseStart_3006297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006312 : List Nat := [2, 1, 4, 2, 1, 1, 2, 9]
def baseStart_3006312 : Nat := 118140960795 + 3006312 * 2 ^ 59
def prefixEnd_3006312 : Nat := 4983230072969 + 3 ^ 40 * 3006312 * 2
def baseEnd_3006312 : Nat := 114346892842929409198091

theorem tailTrace_3006312 : CollatzResearch.WordTrace tailWord_3006312 prefixEnd_3006312 114346892842929409198091 := by
  unfold tailWord_3006312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54824603342326268028942595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73099471123101690705256793 54824603342326268028942595)
  ·
    refine ⟨82236905013489402043413893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54824603342326268028942595 82236905013489402043413893)
    ·
      refine ⟨15419419690029262883140105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82236905013489402043413893 15419419690029262883140105)
      ·
        refine ⟨11564564767521947162355079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15419419690029262883140105 11564564767521947162355079)
        ·
          refine ⟨17346847151282920743532619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564564767521947162355079 17346847151282920743532619)
          ·
            refine ⟨26020270726924381115298929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17346847151282920743532619 26020270726924381115298929)
            ·
              refine ⟨19515203045193285836474197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26020270726924381115298929 19515203045193285836474197)
              ·
                refine ⟨114346892842929409198091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19515203045193285836474197 114346892842929409198091)
                ·
                  rfl

theorem cell22_3006312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_3006312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006312 prefixEnd_3006312 := by exact prefixLift 3006312
  have htrace : WordTrace (prefixWord ++ tailWord_3006312) baseStart_3006312 baseEnd_3006312 := by
    simpa [prefixWord, tailWord_3006312, baseEnd_3006312] using wordTrace_append hprefix tailTrace_3006312
  have hstable : (prefixWord ++ tailWord_3006312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006312).length < 2 ^ (prefixWord ++ tailWord_3006312).sum := by decide
  have hdescent : baseEnd_3006312 < baseStart_3006312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006346 : List Nat := [3, 1, 2, 4, 3, 1, 8]
def baseStart_3006346 : Nat := 118140960795 + 3006346 * 2 ^ 59
def prefixEnd_3006346 : Nat := 4983230072969 + 3 ^ 40 * 3006346 * 2
def baseEnd_3006346 : Nat := 38116062017822219534545

theorem tailTrace_3006346 : CollatzResearch.WordTrace tailWord_3006346 prefixEnd_3006346 38116062017822219534545 := by
  unfold tailWord_3006346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412611691632339966155723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73100297844352906576415261 27412611691632339966155723)
  ·
    refine ⟨41118917537448509949233585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412611691632339966155723 41118917537448509949233585)
    ·
      refine ⟨30839188153086382461925189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41118917537448509949233585 30839188153086382461925189)
      ·
        refine ⟨5782347778703696711610973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30839188153086382461925189 5782347778703696711610973)
        ·
          refine ⟨2168380417013886266854115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5782347778703696711610973 2168380417013886266854115)
          ·
            refine ⟨3252570625520829400281173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168380417013886266854115 3252570625520829400281173)
            ·
              refine ⟨38116062017822219534545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3252570625520829400281173 38116062017822219534545)
              ·
                rfl

theorem cell22_3006346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 8].length) (baseStart_3006346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006346 prefixEnd_3006346 := by exact prefixLift 3006346
  have htrace : WordTrace (prefixWord ++ tailWord_3006346) baseStart_3006346 baseEnd_3006346 := by
    simpa [prefixWord, tailWord_3006346, baseEnd_3006346] using wordTrace_append hprefix tailTrace_3006346
  have hstable : (prefixWord ++ tailWord_3006346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006346).length < 2 ^ (prefixWord ++ tailWord_3006346).sum := by decide
  have hdescent : baseEnd_3006346 < baseStart_3006346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006357 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 7]
def baseStart_3006357 : Nat := 118140960795 + 3006357 * 2 ^ 59
def prefixEnd_3006357 : Nat := 4983230072969 + 3 ^ 40 * 3006357 * 2
def baseEnd_3006357 : Nat := 343045813335333188469227

theorem tailTrace_3006357 : CollatzResearch.WordTrace tailWord_3006357 prefixEnd_3006357 343045813335333188469227 := by
  unfold tailWord_3006357
  simp only [CollatzResearch.WordTrace]
  refine ⟨109650847969489508743273325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73100565312993005828848883 109650847969489508743273325)
  ·
    refine ⟨41119067988558565778727497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109650847969489508743273325 41119067988558565778727497)
    ·
      refine ⟨30839300991418924334045623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41119067988558565778727497 30839300991418924334045623)
      ·
        refine ⟨46258951487128386501068435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30839300991418924334045623 46258951487128386501068435)
        ·
          refine ⟨69388427230692579751602653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46258951487128386501068435 69388427230692579751602653)
          ·
            refine ⟨26020660211509717406850995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69388427230692579751602653 26020660211509717406850995)
            ·
              refine ⟨39030990317264576110276493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26020660211509717406850995 39030990317264576110276493)
              ·
                refine ⟨14636621368974216041353685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39030990317264576110276493 14636621368974216041353685)
                ·
                  refine ⟨343045813335333188469227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14636621368974216041353685 343045813335333188469227)
                  ·
                    rfl

theorem cell22_3006357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_3006357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006357 prefixEnd_3006357 := by exact prefixLift 3006357
  have htrace : WordTrace (prefixWord ++ tailWord_3006357) baseStart_3006357 baseEnd_3006357 := by
    simpa [prefixWord, tailWord_3006357, baseEnd_3006357] using wordTrace_append hprefix tailTrace_3006357
  have hstable : (prefixWord ++ tailWord_3006357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006357).length < 2 ^ (prefixWord ++ tailWord_3006357).sum := by decide
  have hdescent : baseEnd_3006357 < baseStart_3006357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006361 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_3006361 : Nat := 118140960795 + 3006361 * 2 ^ 59
def prefixEnd_3006361 : Nat := 4983230072969 + 3 ^ 40 * 3006361 * 2
def baseEnd_3006361 : Nat := 1029138809287744888307669

theorem tailTrace_3006361 : CollatzResearch.WordTrace tailWord_3006361 prefixEnd_3006361 1029138809287744888307669 := by
  unfold tailWord_3006361
  simp only [CollatzResearch.WordTrace]
  refine ⟨109650993861475017426418937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73100662574316678284279291 109650993861475017426418937)
  ·
    refine ⟨82238245396106263069814203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109650993861475017426418937 82238245396106263069814203)
    ·
      refine ⟨123357368094159394604721305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82238245396106263069814203 123357368094159394604721305)
      ·
        refine ⟨92518026070619545953540979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123357368094159394604721305 92518026070619545953540979)
        ·
          refine ⟨138777039105929318930311469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92518026070619545953540979 138777039105929318930311469)
          ·
            refine ⟨52041389664723494598866801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138777039105929318930311469 52041389664723494598866801)
            ·
              refine ⟨39031042248542620949150101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52041389664723494598866801 39031042248542620949150101)
              ·
                refine ⟨1829580105400435356991411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39031042248542620949150101 1829580105400435356991411)
                ·
                  refine ⟨2744370158100653035487117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829580105400435356991411 2744370158100653035487117)
                  ·
                    refine ⟨1029138809287744888307669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744370158100653035487117 1029138809287744888307669)
                    ·
                      rfl

theorem cell22_3006361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_3006361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006361 prefixEnd_3006361 := by exact prefixLift 3006361
  have htrace : WordTrace (prefixWord ++ tailWord_3006361) baseStart_3006361 baseEnd_3006361 := by
    simpa [prefixWord, tailWord_3006361, baseEnd_3006361] using wordTrace_append hprefix tailTrace_3006361
  have hstable : (prefixWord ++ tailWord_3006361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006361).length < 2 ^ (prefixWord ++ tailWord_3006361).sum := by decide
  have hdescent : baseEnd_3006361 < baseStart_3006361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006485 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_3006485 : Nat := 118140960795 + 3006485 * 2 ^ 59
def prefixEnd_3006485 : Nat := 4983230072969 + 3 ^ 40 * 3006485 * 2
def baseEnd_3006485 : Nat := 1029181257021849898207289

theorem tailTrace_3006485 : CollatzResearch.WordTrace tailWord_3006485 prefixEnd_3006485 1029181257021849898207289 := by
  unfold tailWord_3006485
  simp only [CollatzResearch.WordTrace]
  refine ⟨109655516513025786603932909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73103677675350524402621939 109655516513025786603932909)
  ·
    refine ⟨41120818692384669976474841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109655516513025786603932909 41120818692384669976474841)
    ·
      refine ⟨30840614019288502482356131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41120818692384669976474841 30840614019288502482356131)
      ·
        refine ⟨46260921028932753723534197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30840614019288502482356131 46260921028932753723534197)
        ·
          refine ⟨4336961346462445661581331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46260921028932753723534197 4336961346462445661581331)
          ·
            refine ⟨6505442019693668492371997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336961346462445661581331 6505442019693668492371997)
            ·
              refine ⟨2439540757385125684639499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6505442019693668492371997 2439540757385125684639499)
              ·
                refine ⟨3659311136077688526959249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439540757385125684639499 3659311136077688526959249)
                ·
                  refine ⟨2744483352058266395219437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659311136077688526959249 2744483352058266395219437)
                  ·
                    refine ⟨1029181257021849898207289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744483352058266395219437 1029181257021849898207289)
                    ·
                      rfl

theorem cell22_3006485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_3006485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006485 prefixEnd_3006485 := by exact prefixLift 3006485
  have htrace : WordTrace (prefixWord ++ tailWord_3006485) baseStart_3006485 baseEnd_3006485 := by
    simpa [prefixWord, tailWord_3006485, baseEnd_3006485] using wordTrace_append hprefix tailTrace_3006485
  have hstable : (prefixWord ++ tailWord_3006485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006485).length < 2 ^ (prefixWord ++ tailWord_3006485).sum := by decide
  have hdescent : baseEnd_3006485 < baseStart_3006485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_3006539 : Nat := 118140960795 + 3006539 * 2 ^ 59
def prefixEnd_3006539 : Nat := 4983230072969 + 3 ^ 40 * 3006539 * 2
def baseEnd_3006539 : Nat := 1029199742325411757357123

theorem tailTrace_3006539 : CollatzResearch.WordTrace tailWord_3006539 prefixEnd_3006539 1029199742325411757357123 := by
  unfold tailWord_3006539
  simp only [CollatzResearch.WordTrace]
  refine ⟨109657486054830153826398671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73104990703220102550932447 109657486054830153826398671)
  ·
    refine ⟨164486229082245230739598007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109657486054830153826398671 164486229082245230739598007)
    ·
      refine ⟨246729343623367846109397011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164486229082245230739598007 246729343623367846109397011)
      ·
        refine ⟨370094015435051769164095517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246729343623367846109397011 370094015435051769164095517)
        ·
          refine ⟨138785255788144413436535819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370094015435051769164095517 138785255788144413436535819)
          ·
            refine ⟨208177883682216620154803729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138785255788144413436535819 208177883682216620154803729)
            ·
              refine ⟨156133412761662465116102797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208177883682216620154803729 156133412761662465116102797)
              ·
                refine ⟨58550029785623424418538549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156133412761662465116102797 58550029785623424418538549)
                ·
                  refine ⟨5489065292402196039237989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58550029785623424418538549 5489065292402196039237989)
                  ·
                    refine ⟨1029199742325411757357123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489065292402196039237989 1029199742325411757357123)
                    ·
                      rfl

theorem cell22_3006539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_3006539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006539 prefixEnd_3006539 := by exact prefixLift 3006539
  have htrace : WordTrace (prefixWord ++ tailWord_3006539) baseStart_3006539 baseEnd_3006539 := by
    simpa [prefixWord, tailWord_3006539, baseEnd_3006539] using wordTrace_append hprefix tailTrace_3006539
  have hstable : (prefixWord ++ tailWord_3006539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006539).length < 2 ^ (prefixWord ++ tailWord_3006539).sum := by decide
  have hdescent : baseEnd_3006539 < baseStart_3006539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006541 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3006541 : Nat := 118140960795 + 3006541 * 2 ^ 59
def prefixEnd_3006541 : Nat := 4983230072969 + 3 ^ 40 * 3006541 * 2
def baseEnd_3006541 : Nat := 1029200426966284418807117

theorem tailTrace_3006541 : CollatzResearch.WordTrace tailWord_3006541 prefixEnd_3006541 1029200426966284418807117 := by
  unfold tailWord_3006541
  simp only [CollatzResearch.WordTrace]
  refine ⟨109657559000822908167971477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73105039333881938778647651 109657559000822908167971477)
  ·
    refine ⟨5140198078163573820373663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109657559000822908167971477 5140198078163573820373663)
    ·
      refine ⟨7710297117245360730560495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140198078163573820373663 7710297117245360730560495)
      ·
        refine ⟨11565445675868041095840743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7710297117245360730560495 11565445675868041095840743)
        ·
          refine ⟨17348168513802061643761115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565445675868041095840743 17348168513802061643761115)
          ·
            refine ⟨26022252770703092465641673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17348168513802061643761115 26022252770703092465641673)
            ·
              refine ⟨19516689578027319349231255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26022252770703092465641673 19516689578027319349231255)
              ·
                refine ⟨29275034367040979023846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19516689578027319349231255 29275034367040979023846883)
                ·
                  refine ⟨43912551550561468535770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29275034367040979023846883 43912551550561468535770325)
                  ·
                    refine ⟨1029200426966284418807117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43912551550561468535770325 1029200426966284418807117)
                    ·
                      rfl

theorem cell22_3006541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3006541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006541 prefixEnd_3006541 := by exact prefixLift 3006541
  have htrace : WordTrace (prefixWord ++ tailWord_3006541) baseStart_3006541 baseEnd_3006541 := by
    simpa [prefixWord, tailWord_3006541, baseEnd_3006541] using wordTrace_append hprefix tailTrace_3006541
  have hstable : (prefixWord ++ tailWord_3006541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006541).length < 2 ^ (prefixWord ++ tailWord_3006541).sum := by decide
  have hdescent : baseEnd_3006541 < baseStart_3006541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006554 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_3006554 : Nat := 118140960795 + 3006554 * 2 ^ 59
def prefixEnd_3006554 : Nat := 4983230072969 + 3 ^ 40 * 3006554 * 2
def baseEnd_3006554 : Nat := 343068292377318906077359

theorem tailTrace_3006554 : CollatzResearch.WordTrace tailWord_3006554 prefixEnd_3006554 343068292377318906077359 := by
  unfold tailWord_3006554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27414508287443952847048679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73105355433183874258796477 27414508287443952847048679)
  ·
    refine ⟨41121762431165929270573019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27414508287443952847048679 41121762431165929270573019)
    ·
      refine ⟨61682643646748893905859529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41121762431165929270573019 61682643646748893905859529)
      ·
        refine ⟨46261982735061670429394647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61682643646748893905859529 46261982735061670429394647)
        ·
          refine ⟨69392974102592505644091971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46261982735061670429394647 69392974102592505644091971)
          ·
            refine ⟨104089461153888758466137957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69392974102592505644091971 104089461153888758466137957)
            ·
              refine ⟨19516773966354142212400867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104089461153888758466137957 19516773966354142212400867)
              ·
                refine ⟨29275160949531213318601301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19516773966354142212400867 29275160949531213318601301)
                ·
                  refine ⟨343068292377318906077359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29275160949531213318601301 343068292377318906077359)
                  ·
                    rfl

theorem cell22_3006554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_3006554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006554 prefixEnd_3006554 := by exact prefixLift 3006554
  have htrace : WordTrace (prefixWord ++ tailWord_3006554) baseStart_3006554 baseEnd_3006554 := by
    simpa [prefixWord, tailWord_3006554, baseEnd_3006554] using wordTrace_append hprefix tailTrace_3006554
  have hstable : (prefixWord ++ tailWord_3006554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006554).length < 2 ^ (prefixWord ++ tailWord_3006554).sum := by decide
  have hdescent : baseEnd_3006554 < baseStart_3006554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006584 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3006584 : Nat := 118140960795 + 3006584 * 2 ^ 59
def prefixEnd_3006584 : Nat := 4983230072969 + 3 ^ 40 * 3006584 * 2
def baseEnd_3006584 : Nat := 1029215146745046639981985

theorem tailTrace_3006584 : CollatzResearch.WordTrace tailWord_3006584 prefixEnd_3006584 1029215146745046639981985 := by
  unfold tailWord_3006584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54829563669833563255893403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73106084893111417674524537 54829563669833563255893403)
  ·
    refine ⟨82244345504750344883840105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54829563669833563255893403 82244345504750344883840105)
    ·
      refine ⟨61683259128562758662880079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82244345504750344883840105 61683259128562758662880079)
      ·
        refine ⟨92524888692844137994320119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61683259128562758662880079 92524888692844137994320119)
        ·
          refine ⟨138787333039266206991480179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92524888692844137994320119 138787333039266206991480179)
          ·
            refine ⟨208180999558899310487220269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138787333039266206991480179 208180999558899310487220269)
            ·
              refine ⟨78067874834587241432707601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208180999558899310487220269 78067874834587241432707601)
              ·
                refine ⟨58550906125940431074530701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78067874834587241432707601 58550906125940431074530701)
                ·
                  refine ⟨21956589797227661652949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58550906125940431074530701 21956589797227661652949013)
                  ·
                    refine ⟨1029215146745046639981985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21956589797227661652949013 1029215146745046639981985)
                    ·
                      rfl

theorem cell22_3006584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3006584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006584 prefixEnd_3006584 := by exact prefixLift 3006584
  have htrace : WordTrace (prefixWord ++ tailWord_3006584) baseStart_3006584 baseEnd_3006584 := by
    simpa [prefixWord, tailWord_3006584, baseEnd_3006584] using wordTrace_append hprefix tailTrace_3006584
  have hstable : (prefixWord ++ tailWord_3006584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006584).length < 2 ^ (prefixWord ++ tailWord_3006584).sum := by decide
  have hdescent : baseEnd_3006584 < baseStart_3006584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006588 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_3006588 : Nat := 118140960795 + 3006588 * 2 ^ 59
def prefixEnd_3006588 : Nat := 4983230072969 + 3 ^ 40 * 3006588 * 2
def baseEnd_3006588 : Nat := 343072172008930654293991

theorem tailTrace_3006588 : CollatzResearch.WordTrace tailWord_3006588 prefixEnd_3006588 343072172008930654293991 := by
  unfold tailWord_3006588
  simp only [CollatzResearch.WordTrace]
  refine ⟨54829636615826317597466209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73106182154435090129954945 54829636615826317597466209)
  ·
    refine ⟨41122227461869738198099657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54829636615826317597466209 41122227461869738198099657)
    ·
      refine ⟨30841670596402303648574743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41122227461869738198099657 30841670596402303648574743)
      ·
        refine ⟨46262505894603455472862115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30841670596402303648574743 46262505894603455472862115)
        ·
          refine ⟨69393758841905183209293173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46262505894603455472862115 69393758841905183209293173)
          ·
            refine ⟨6505664891428610925871235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69393758841905183209293173 6505664891428610925871235)
            ·
              refine ⟨9758497337142916388806853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505664891428610925871235 9758497337142916388806853)
              ·
                refine ⟨1829718250714296822901285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9758497337142916388806853 1829718250714296822901285)
                ·
                  refine ⟨343072172008930654293991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829718250714296822901285 343072172008930654293991)
                  ·
                    rfl

theorem cell22_3006588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_3006588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006588 prefixEnd_3006588 := by exact prefixLift 3006588
  have htrace : WordTrace (prefixWord ++ tailWord_3006588) baseStart_3006588 baseEnd_3006588 := by
    simpa [prefixWord, tailWord_3006588, baseEnd_3006588] using wordTrace_append hprefix tailTrace_3006588
  have hstable : (prefixWord ++ tailWord_3006588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006588).length < 2 ^ (prefixWord ++ tailWord_3006588).sum := by decide
  have hdescent : baseEnd_3006588 < baseStart_3006588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006618 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_3006618 : Nat := 118140960795 + 3006618 * 2 ^ 59
def prefixEnd_3006618 : Nat := 4983230072969 + 3 ^ 40 * 3006618 * 2
def baseEnd_3006618 : Nat := 1029226785639881884631881

theorem tailTrace_3006618 : CollatzResearch.WordTrace tailWord_3006618 prefixEnd_3006618 1029226785639881884631881 := by
  unfold tailWord_3006618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27415091855385987579631127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73106911614362633545683005 27415091855385987579631127)
  ·
    refine ⟨41122637783078981369446691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27415091855385987579631127 41122637783078981369446691)
    ·
      refine ⟨61683956674618472054170037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41122637783078981369446691 61683956674618472054170037)
      ·
        refine ⟨5782870938245481755078441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61683956674618472054170037 5782870938245481755078441)
        ·
          refine ⟨4337153203684111316308831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5782870938245481755078441 4337153203684111316308831)
          ·
            refine ⟨6505729805526166974463247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337153203684111316308831 6505729805526166974463247)
            ·
              refine ⟨9758594708289250461694871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505729805526166974463247 9758594708289250461694871)
              ·
                refine ⟨14637892062433875692542307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9758594708289250461694871 14637892062433875692542307)
                ·
                  refine ⟨21956838093650813538813461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14637892062433875692542307 21956838093650813538813461)
                  ·
                    refine ⟨1029226785639881884631881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21956838093650813538813461 1029226785639881884631881)
                    ·
                      rfl

theorem cell22_3006618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_3006618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006618 prefixEnd_3006618 := by exact prefixLift 3006618
  have htrace : WordTrace (prefixWord ++ tailWord_3006618) baseStart_3006618 baseEnd_3006618 := by
    simpa [prefixWord, tailWord_3006618, baseEnd_3006618] using wordTrace_append hprefix tailTrace_3006618
  have hstable : (prefixWord ++ tailWord_3006618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006618).length < 2 ^ (prefixWord ++ tailWord_3006618).sum := by decide
  have hdescent : baseEnd_3006618 < baseStart_3006618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006622 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3006622 : Nat := 118140960795 + 3006622 * 2 ^ 59
def prefixEnd_3006622 : Nat := 4983230072969 + 3 ^ 40 * 3006622 * 2
def baseEnd_3006622 : Nat := 343076051640542402510623

theorem tailTrace_3006622 : CollatzResearch.WordTrace tailWord_3006622 prefixEnd_3006622 343076051640542402510623 := by
  unfold tailWord_3006622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13707564164191182375208765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73107008875686306001113413 13707564164191182375208765)
  ·
    refine ⟨5140336561571693390703287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13707564164191182375208765 5140336561571693390703287)
    ·
      refine ⟨7710504842357540086054931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140336561571693390703287 7710504842357540086054931)
      ·
        refine ⟨11565757263536310129082397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7710504842357540086054931 11565757263536310129082397)
        ·
          refine ⟨4337158973826116298405899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11565757263536310129082397 4337158973826116298405899)
          ·
            refine ⟨6505738460739174447608849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337158973826116298405899 6505738460739174447608849)
            ·
              refine ⟨4879303845554380835706637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505738460739174447608849 4879303845554380835706637)
              ·
                refine ⟨1829738942082892813389989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879303845554380835706637 1829738942082892813389989)
                ·
                  refine ⟨343076051640542402510623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829738942082892813389989 343076051640542402510623)
                  ·
                    rfl

theorem cell22_3006622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3006622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006622 prefixEnd_3006622 := by exact prefixLift 3006622
  have htrace : WordTrace (prefixWord ++ tailWord_3006622) baseStart_3006622 baseEnd_3006622 := by
    simpa [prefixWord, tailWord_3006622, baseEnd_3006622] using wordTrace_append hprefix tailTrace_3006622
  have hstable : (prefixWord ++ tailWord_3006622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006622).length < 2 ^ (prefixWord ++ tailWord_3006622).sum := by decide
  have hdescent : baseEnd_3006622 < baseStart_3006622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006637 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3006637 : Nat := 118140960795 + 3006637 * 2 ^ 59
def prefixEnd_3006637 : Nat := 4983230072969 + 3 ^ 40 * 3006637 * 2
def baseEnd_3006637 : Nat := 1029233289728172168406823

theorem tailTrace_3006637 : CollatzResearch.WordTrace tailWord_3006637 prefixEnd_3006637 1029233289728172168406823 := by
  unfold tailWord_3006637
  simp only [CollatzResearch.WordTrace]
  refine ⟨109661060408475116563466165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73107373605650077708977443 109661060408475116563466165)
  ·
    refine ⟨10280724413294542177824953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109661060408475116563466165 10280724413294542177824953)
    ·
      refine ⟨7710543309970906633368715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10280724413294542177824953 7710543309970906633368715)
      ·
        refine ⟨11565814964956359950053073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7710543309970906633368715 11565814964956359950053073)
        ·
          refine ⟨8674361223717269962539805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11565814964956359950053073 8674361223717269962539805)
          ·
            refine ⟨3252885458893976235952427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8674361223717269962539805 3252885458893976235952427)
            ·
              refine ⟨4879328188340964353928641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252885458893976235952427 4879328188340964353928641)
              ·
                refine ⟨3659496141255723265446481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879328188340964353928641 3659496141255723265446481)
                ·
                  refine ⟨2744622105941792449084861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659496141255723265446481 2744622105941792449084861)
                  ·
                    refine ⟨1029233289728172168406823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744622105941792449084861 1029233289728172168406823)
                    ·
                      rfl

theorem cell22_3006637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3006637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006637 prefixEnd_3006637 := by exact prefixLift 3006637
  have htrace : WordTrace (prefixWord ++ tailWord_3006637) baseStart_3006637 baseEnd_3006637 := by
    simpa [prefixWord, tailWord_3006637, baseEnd_3006637] using wordTrace_append hprefix tailTrace_3006637
  have hstable : (prefixWord ++ tailWord_3006637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006637).length < 2 ^ (prefixWord ++ tailWord_3006637).sum := by decide
  have hdescent : baseEnd_3006637 < baseStart_3006637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006648 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_3006648 : Nat := 118140960795 + 3006648 * 2 ^ 59
def prefixEnd_3006648 : Nat := 4983230072969 + 3 ^ 40 * 3006648 * 2
def baseEnd_3006648 : Nat := 1029237055252971806381789

theorem tailTrace_3006648 : CollatzResearch.WordTrace tailWord_3006648 prefixEnd_3006648 1029237055252971806381789 := by
  unfold tailWord_3006648
  simp only [CollatzResearch.WordTrace]
  refine ⟨54830730805717632721058299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73107641074290176961411065 54830730805717632721058299)
  ·
    refine ⟨82246096208576449081587449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54830730805717632721058299 82246096208576449081587449)
    ·
      refine ⟨61684572156432336811190587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82246096208576449081587449 61684572156432336811190587)
      ·
        refine ⟨92526858234648505216785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61684572156432336811190587 92526858234648505216785881)
        ·
          refine ⟨69395143675986378912589411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92526858234648505216785881 69395143675986378912589411)
          ·
            refine ⟨104092715513979568368884117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69395143675986378912589411 104092715513979568368884117)
            ·
              refine ⟨4879346039717792267291443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104092715513979568368884117 4879346039717792267291443)
              ·
                refine ⟨7319019059576688400937165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879346039717792267291443 7319019059576688400937165)
                ·
                  refine ⟨2744632147341258150351437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7319019059576688400937165 2744632147341258150351437)
                  ·
                    refine ⟨1029237055252971806381789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744632147341258150351437 1029237055252971806381789)
                    ·
                      rfl

theorem cell22_3006648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_3006648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006648 prefixEnd_3006648 := by exact prefixLift 3006648
  have htrace : WordTrace (prefixWord ++ tailWord_3006648) baseStart_3006648 baseEnd_3006648 := by
    simpa [prefixWord, tailWord_3006648, baseEnd_3006648] using wordTrace_append hprefix tailTrace_3006648
  have hstable : (prefixWord ++ tailWord_3006648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006648).length < 2 ^ (prefixWord ++ tailWord_3006648).sum := by decide
  have hdescent : baseEnd_3006648 < baseStart_3006648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006661 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 5]
def baseStart_3006661 : Nat := 118140960795 + 3006661 * 2 ^ 59
def prefixEnd_3006661 : Nat := 4983230072969 + 3 ^ 40 * 3006661 * 2
def baseEnd_3006661 : Nat := 343080501806214701935583

theorem tailTrace_3006661 : CollatzResearch.WordTrace tailWord_3006661 prefixEnd_3006661 343080501806214701935583 := by
  unfold tailWord_3006661
  simp only [CollatzResearch.WordTrace]
  refine ⟨109661935760388168662339837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73107957173592112441559891 109661935760388168662339837)
  ·
    refine ⟨41123225910145563248377439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109661935760388168662339837 41123225910145563248377439)
    ·
      refine ⟨61684838865218344872566159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41123225910145563248377439 61684838865218344872566159)
      ·
        refine ⟨92527258297827517308849239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61684838865218344872566159 92527258297827517308849239)
        ·
          refine ⟨138790887446741275963273859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92527258297827517308849239 138790887446741275963273859)
          ·
            refine ⟨208186331170111913944910789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138790887446741275963273859 208186331170111913944910789)
            ·
              refine ⟨39034937094395983864670773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208186331170111913944910789 39034937094395983864670773)
              ·
                refine ⟨3659525352599623487312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39034937094395983864670773 3659525352599623487312885)
                ·
                  refine ⟨343080501806214701935583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3659525352599623487312885 343080501806214701935583)
                  ·
                    rfl

theorem cell22_3006661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_3006661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006661 prefixEnd_3006661 := by exact prefixLift 3006661
  have htrace : WordTrace (prefixWord ++ tailWord_3006661) baseStart_3006661 baseEnd_3006661 := by
    simpa [prefixWord, tailWord_3006661, baseEnd_3006661] using wordTrace_append hprefix tailTrace_3006661
  have hstable : (prefixWord ++ tailWord_3006661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006661).length < 2 ^ (prefixWord ++ tailWord_3006661).sum := by decide
  have hdescent : baseEnd_3006661 < baseStart_3006661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006751 : List Nat := [1, 1, 2, 4, 3, 11]
def baseStart_3006751 : Nat := 118140960795 + 3006751 * 2 ^ 59
def prefixEnd_3006751 : Nat := 4983230072969 + 3 ^ 40 * 3006751 * 2
def baseEnd_3006751 : Nat := 12707065608122393469833

theorem tailTrace_3006751 : CollatzResearch.WordTrace tailWord_3006751 prefixEnd_3006751 12707065608122393469833 := by
  unfold tailWord_3006751
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665218330062114033116107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73110145553374742688744071 109665218330062114033116107)
  ·
    refine ⟨164497827495093171049674161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109665218330062114033116107 164497827495093171049674161)
    ·
      refine ⟨123373370621319878287255621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164497827495093171049674161 123373370621319878287255621)
      ·
        refine ⟨23132506991497477178860429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123373370621319878287255621 23132506991497477178860429)
        ·
          refine ⟨8674690121811553942072661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23132506991497477178860429 8674690121811553942072661)
          ·
            refine ⟨12707065608122393469833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8674690121811553942072661 12707065608122393469833)
            ·
              rfl

theorem cell22_3006751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 11].length) (baseStart_3006751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006751 prefixEnd_3006751 := by exact prefixLift 3006751
  have htrace : WordTrace (prefixWord ++ tailWord_3006751) baseStart_3006751 baseEnd_3006751 := by
    simpa [prefixWord, tailWord_3006751, baseEnd_3006751] using wordTrace_append hprefix tailTrace_3006751
  have hstable : (prefixWord ++ tailWord_3006751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006751).length < 2 ^ (prefixWord ++ tailWord_3006751).sum := by decide
  have hdescent : baseEnd_3006751 < baseStart_3006751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006753 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3006753 : Nat := 118140960795 + 3006753 * 2 ^ 59
def prefixEnd_3006753 : Nat := 4983230072969 + 3 ^ 40 * 3006753 * 2
def baseEnd_3006753 : Nat := 1029272998898786532506467

theorem tailTrace_3006753 : CollatzResearch.WordTrace tailWord_3006753 prefixEnd_3006753 1029272998898786532506467 := by
  unfold tailWord_3006753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665291276054868374688913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73110194184036578916459275 109665291276054868374688913)
  ·
    refine ⟨82248968457041151281016685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109665291276054868374688913 82248968457041151281016685)
    ·
      refine ⟨30843363171390431730381257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82248968457041151281016685 30843363171390431730381257)
      ·
        refine ⟨23132522378542823797785943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30843363171390431730381257 23132522378542823797785943)
        ·
          refine ⟨34698783567814235696678915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23132522378542823797785943 34698783567814235696678915)
          ·
            refine ⟨52048175351721353545018373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34698783567814235696678915 52048175351721353545018373)
            ·
              refine ⟨9759032878447753789690945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52048175351721353545018373 9759032878447753789690945)
              ·
                refine ⟨7319274658835815342268209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9759032878447753789690945 7319274658835815342268209)
                ·
                  refine ⟨5489455994126861506701157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7319274658835815342268209 5489455994126861506701157)
                  ·
                    refine ⟨1029272998898786532506467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489455994126861506701157 1029272998898786532506467)
                    ·
                      rfl

theorem cell22_3006753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3006753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006753 prefixEnd_3006753 := by exact prefixLift 3006753
  have htrace : WordTrace (prefixWord ++ tailWord_3006753) baseStart_3006753 baseEnd_3006753 := by
    simpa [prefixWord, tailWord_3006753, baseEnd_3006753] using wordTrace_append hprefix tailTrace_3006753
  have hstable : (prefixWord ++ tailWord_3006753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006753).length < 2 ^ (prefixWord ++ tailWord_3006753).sum := by decide
  have hdescent : baseEnd_3006753 < baseStart_3006753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006755 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 2, 3]
def baseStart_3006755 : Nat := 118140960795 + 3006755 * 2 ^ 59
def prefixEnd_3006755 : Nat := 4983230072969 + 3 ^ 40 * 3006755 * 2
def baseEnd_3006755 : Nat := 1029273683539659193956461

theorem tailTrace_3006755 : CollatzResearch.WordTrace tailWord_3006755 prefixEnd_3006755 1029273683539659193956461 := by
  unfold tailWord_3006755
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665364222047622716261719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73110242814698415144174479 109665364222047622716261719)
  ·
    refine ⟨164498046333071434074392579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109665364222047622716261719 164498046333071434074392579)
    ·
      refine ⟨246747069499607151111588869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164498046333071434074392579 246747069499607151111588869)
      ·
        refine ⟨46265075531176340833422913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246747069499607151111588869 46265075531176340833422913)
        ·
          refine ⟨34698806648382255625067185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46265075531176340833422913 34698806648382255625067185)
          ·
            refine ⟨26024104986286691718800389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34698806648382255625067185 26024104986286691718800389)
            ·
              refine ⟨4879519684928754697275073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26024104986286691718800389 4879519684928754697275073)
              ·
                refine ⟨3659639763696566022956305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879519684928754697275073 3659639763696566022956305)
                ·
                  refine ⟨2744729822772424517217229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659639763696566022956305 2744729822772424517217229)
                  ·
                    refine ⟨1029273683539659193956461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744729822772424517217229 1029273683539659193956461)
                    ·
                      rfl

theorem cell22_3006755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].length) (baseStart_3006755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006755 prefixEnd_3006755 := by exact prefixLift 3006755
  have htrace : WordTrace (prefixWord ++ tailWord_3006755) baseStart_3006755 baseEnd_3006755 := by
    simpa [prefixWord, tailWord_3006755, baseEnd_3006755] using wordTrace_append hprefix tailTrace_3006755
  have hstable : (prefixWord ++ tailWord_3006755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006755).length < 2 ^ (prefixWord ++ tailWord_3006755).sum := by decide
  have hdescent : baseEnd_3006755 < baseStart_3006755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006772 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3006772 : Nat := 118140960795 + 3006772 * 2 ^ 59
def prefixEnd_3006772 : Nat := 4983230072969 + 3 ^ 40 * 3006772 * 2
def baseEnd_3006772 : Nat := 1029279502987076816281409

theorem tailTrace_3006772 : CollatzResearch.WordTrace tailWord_3006772 prefixEnd_3006772 1029279502987076816281409 := by
  unfold tailWord_3006772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54832992131493017309815285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73110656175324023079753713 54832992131493017309815285)
  ·
    refine ⟨5140593012327470372795183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54832992131493017309815285 5140593012327470372795183)
    ·
      refine ⟨7710889518491205559192775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140593012327470372795183 7710889518491205559192775)
      ·
        refine ⟨11566334277736808338789163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7710889518491205559192775 11566334277736808338789163)
        ·
          refine ⟨17349501416605212508183745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566334277736808338789163 17349501416605212508183745)
          ·
            refine ⟨13012126062453909381137809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17349501416605212508183745 13012126062453909381137809)
            ·
              refine ⟨9759094546840432035853357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13012126062453909381137809 9759094546840432035853357)
              ·
                refine ⟨3659660455065162013445009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9759094546840432035853357 3659660455065162013445009)
                ·
                  refine ⟨2744745341298871510083757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659660455065162013445009 2744745341298871510083757)
                  ·
                    refine ⟨1029279502987076816281409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744745341298871510083757 1029279502987076816281409)
                    ·
                      rfl

theorem cell22_3006772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3006772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006772 prefixEnd_3006772 := by exact prefixLift 3006772
  have htrace : WordTrace (prefixWord ++ tailWord_3006772) baseStart_3006772 baseEnd_3006772 := by
    simpa [prefixWord, tailWord_3006772, baseEnd_3006772] using wordTrace_append hprefix tailTrace_3006772
  have hstable : (prefixWord ++ tailWord_3006772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006772).length < 2 ^ (prefixWord ++ tailWord_3006772).sum := by decide
  have hdescent : baseEnd_3006772 < baseStart_3006772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006851 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 1, 3]
def baseStart_3006851 : Nat := 118140960795 + 3006851 * 2 ^ 59
def prefixEnd_3006851 : Nat := 4983230072969 + 3 ^ 40 * 3006851 * 2
def baseEnd_3006851 : Nat := 1029306546301546943556167

theorem tailTrace_3006851 : CollatzResearch.WordTrace tailWord_3006851 prefixEnd_3006851 1029306546301546943556167 := by
  unfold tailWord_3006851
  simp only [CollatzResearch.WordTrace]
  refine ⟨109668865629699831111756407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73112577086466554074504271 109668865629699831111756407)
  ·
    refine ⟨164503298444549746667634611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109668865629699831111756407 164503298444549746667634611)
    ·
      refine ⟨246754947666824620001451917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164503298444549746667634611 246754947666824620001451917)
      ·
        refine ⟨92533105375059232500544469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246754947666824620001451917 92533105375059232500544469)
        ·
          refine ⟨2168744657227950761731511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92533105375059232500544469 2168744657227950761731511)
          ·
            refine ⟨3253116985841926142597267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168744657227950761731511 3253116985841926142597267)
            ·
              refine ⟨4879675478762889213895901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253116985841926142597267 4879675478762889213895901)
              ·
                refine ⟨1829878304536083455210963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879675478762889213895901 1829878304536083455210963)
                ·
                  refine ⟨2744817456804125182816445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829878304536083455210963 2744817456804125182816445)
                  ·
                    refine ⟨1029306546301546943556167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744817456804125182816445 1029306546301546943556167)
                    ·
                      rfl

theorem cell22_3006851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 3].length) (baseStart_3006851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006851 prefixEnd_3006851 := by exact prefixLift 3006851
  have htrace : WordTrace (prefixWord ++ tailWord_3006851) baseStart_3006851 baseEnd_3006851 := by
    simpa [prefixWord, tailWord_3006851, baseEnd_3006851] using wordTrace_append hprefix tailTrace_3006851
  have hstable : (prefixWord ++ tailWord_3006851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006851).length < 2 ^ (prefixWord ++ tailWord_3006851).sum := by decide
  have hdescent : baseEnd_3006851 < baseStart_3006851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006860 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_3006860 : Nat := 118140960795 + 3006860 * 2 ^ 59
def prefixEnd_3006860 : Nat := 4983230072969 + 3 ^ 40 * 3006860 * 2
def baseEnd_3006860 : Nat := 1029309627185473920081139

theorem tailTrace_3006860 : CollatzResearch.WordTrace tailWord_3006860 prefixEnd_3006860 1029309627185473920081139 := by
  unfold tailWord_3006860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54834596943333612824417017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73112795924444817099222689 54834596943333612824417017)
  ·
    refine ⟨41125947707500209618312763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54834596943333612824417017 41125947707500209618312763)
    ·
      refine ⟨61688921561250314427469145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41125947707500209618312763 61688921561250314427469145)
      ·
        refine ⟨46266691170937735820601859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61688921561250314427469145 46266691170937735820601859)
        ·
          refine ⟨69400036756406603730902789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46266691170937735820601859 69400036756406603730902789)
          ·
            refine ⟨13012506891826238199544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69400036756406603730902789 13012506891826238199544273)
            ·
              refine ⟨9759380168869678649658205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13012506891826238199544273 9759380168869678649658205)
              ·
                refine ⟨3659767563326129493621827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9759380168869678649658205 3659767563326129493621827)
                ·
                  refine ⟨5489651344989194240432741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659767563326129493621827 5489651344989194240432741)
                  ·
                    refine ⟨1029309627185473920081139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489651344989194240432741 1029309627185473920081139)
                    ·
                      rfl

theorem cell22_3006860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_3006860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006860 prefixEnd_3006860 := by exact prefixLift 3006860
  have htrace : WordTrace (prefixWord ++ tailWord_3006860) baseStart_3006860 baseEnd_3006860 := by
    simpa [prefixWord, tailWord_3006860, baseEnd_3006860] using wordTrace_append hprefix tailTrace_3006860
  have hstable : (prefixWord ++ tailWord_3006860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006860).length < 2 ^ (prefixWord ++ tailWord_3006860).sum := by decide
  have hdescent : baseEnd_3006860 < baseStart_3006860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006881 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 5]
def baseStart_3006881 : Nat := 118140960795 + 3006881 * 2 ^ 59
def prefixEnd_3006881 : Nat := 4983230072969 + 3 ^ 40 * 3006881 * 2
def baseEnd_3006881 : Nat := 343105605304878955102025

theorem tailTrace_3006881 : CollatzResearch.WordTrace tailWord_3006881 prefixEnd_3006881 343105605304878955102025 := by
  unfold tailWord_3006881
  simp only [CollatzResearch.WordTrace]
  refine ⟨109669959819591146235348497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73113306546394097490232331 109669959819591146235348497)
  ·
    refine ⟨82252469864693359676511373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109669959819591146235348497 82252469864693359676511373)
    ·
      refine ⟨30844676199260009878691765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82252469864693359676511373 30844676199260009878691765)
      ·
        refine ⟨2891688393680625926127353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30844676199260009878691765 2891688393680625926127353)
        ·
          refine ⟨2168766295260469444595515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2891688393680625926127353 2168766295260469444595515)
          ·
            refine ⟨3253149442890704166893273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168766295260469444595515 3253149442890704166893273)
            ·
              refine ⟨2439862082168028125169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253149442890704166893273 2439862082168028125169955)
              ·
                refine ⟨3659793123252042187754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439862082168028125169955 3659793123252042187754933)
                ·
                  refine ⟨343105605304878955102025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3659793123252042187754933 343105605304878955102025)
                  ·
                    rfl

theorem cell22_3006881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_3006881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006881 prefixEnd_3006881 := by exact prefixLift 3006881
  have htrace : WordTrace (prefixWord ++ tailWord_3006881) baseStart_3006881 baseEnd_3006881 := by
    simpa [prefixWord, tailWord_3006881, baseEnd_3006881] using wordTrace_append hprefix tailTrace_3006881
  have hstable : (prefixWord ++ tailWord_3006881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006881).length < 2 ^ (prefixWord ++ tailWord_3006881).sum := by decide
  have hdescent : baseEnd_3006881 < baseStart_3006881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006903 : List Nat := [1, 1, 3, 1, 3, 3, 2, 8]
def baseStart_3006903 : Nat := 118140960795 + 3006903 * 2 ^ 59
def prefixEnd_3006903 : Nat := 4983230072969 + 3 ^ 40 * 3006903 * 2
def baseEnd_3006903 : Nat := 114369371884915126806223

theorem tailTrace_3006903 : CollatzResearch.WordTrace tailWord_3006903 prefixEnd_3006903 114369371884915126806223 := by
  unfold tailWord_3006903
  simp only [CollatzResearch.WordTrace]
  refine ⟨109670762225511443992649363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73113841483674295995099575 109670762225511443992649363)
  ·
    refine ⟨164506143338267165988974045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109670762225511443992649363 164506143338267165988974045)
    ·
      refine ⟨61689803751850187245865267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164506143338267165988974045 61689803751850187245865267)
      ·
        refine ⟨92534705627775280868797901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61689803751850187245865267 92534705627775280868797901)
        ·
          refine ⟨34700514610415730325799213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92534705627775280868797901 34700514610415730325799213)
          ·
            refine ⟨13012692978905898872174705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34700514610415730325799213 13012692978905898872174705)
            ·
              refine ⟨9759519734179424154131029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13012692978905898872174705 9759519734179424154131029)
              ·
                refine ⟨114369371884915126806223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9759519734179424154131029 114369371884915126806223)
                ·
                  rfl

theorem cell22_3006903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 8].length) (baseStart_3006903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006903 prefixEnd_3006903 := by exact prefixLift 3006903
  have htrace : WordTrace (prefixWord ++ tailWord_3006903) baseStart_3006903 baseEnd_3006903 := by
    simpa [prefixWord, tailWord_3006903, baseEnd_3006903] using wordTrace_append hprefix tailTrace_3006903
  have hstable : (prefixWord ++ tailWord_3006903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006903).length < 2 ^ (prefixWord ++ tailWord_3006903).sum := by decide
  have hdescent : baseEnd_3006903 < baseStart_3006903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006905 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_3006905 : Nat := 118140960795 + 3006905 * 2 ^ 59
def prefixEnd_3006905 : Nat := 4983230072969 + 3 ^ 40 * 3006905 * 2
def baseEnd_3006905 : Nat := 1029325031605108802706001

theorem tailTrace_3006905 : CollatzResearch.WordTrace tailWord_3006905 prefixEnd_3006905 1029325031605108802706001 := by
  unfold tailWord_3006905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109670835171504198334222169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73113890114336132222814779 109670835171504198334222169)
  ·
    refine ⟨82253126378628148750666627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109670835171504198334222169 82253126378628148750666627)
    ·
      refine ⟨123379689567942223125999941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82253126378628148750666627 123379689567942223125999941)
      ·
        refine ⟨23133691793989166836124989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123379689567942223125999941 23133691793989166836124989)
        ·
          refine ⟨8675134422745937563546871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23133691793989166836124989 8675134422745937563546871)
          ·
            refine ⟨13012701634118906345320307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675134422745937563546871 13012701634118906345320307)
            ·
              refine ⟨19519052451178359517980461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13012701634118906345320307 19519052451178359517980461)
              ·
                refine ⟨7319644669191884819242673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19519052451178359517980461 7319644669191884819242673)
                ·
                  refine ⟨5489733501893913614432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7319644669191884819242673 5489733501893913614432005)
                  ·
                    refine ⟨1029325031605108802706001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489733501893913614432005 1029325031605108802706001)
                    ·
                      rfl

theorem cell22_3006905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_3006905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006905 prefixEnd_3006905 := by exact prefixLift 3006905
  have htrace : WordTrace (prefixWord ++ tailWord_3006905) baseStart_3006905 baseEnd_3006905 := by
    simpa [prefixWord, tailWord_3006905, baseEnd_3006905] using wordTrace_append hprefix tailTrace_3006905
  have hstable : (prefixWord ++ tailWord_3006905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006905).length < 2 ^ (prefixWord ++ tailWord_3006905).sum := by decide
  have hdescent : baseEnd_3006905 < baseStart_3006905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006924 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_3006924 : Nat := 118140960795 + 3006924 * 2 ^ 59
def prefixEnd_3006924 : Nat := 4983230072969 + 3 ^ 40 * 3006924 * 2
def baseEnd_3006924 : Nat := 1029331535693399086480943

theorem tailTrace_3006924 : CollatzResearch.WordTrace tailWord_3006924 prefixEnd_3006924 1029331535693399086480943 := by
  unfold tailWord_3006924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54835764079217682289581913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73114352105623576386109217 54835764079217682289581913)
  ·
    refine ⟨41126823059413261717186435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54835764079217682289581913 41126823059413261717186435)
    ·
      refine ⟨61690234589119892575779653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41126823059413261717186435 61690234589119892575779653)
      ·
        refine ⟨11566918985459979857958685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61690234589119892575779653 11566918985459979857958685)
        ·
          refine ⟨4337594619547492446734507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11566918985459979857958685 4337594619547492446734507)
          ·
            refine ⟨6506391929321238670101761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337594619547492446734507 6506391929321238670101761)
            ·
              refine ⟨4879793946990929002576321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6506391929321238670101761 4879793946990929002576321)
              ·
                refine ⟨3659845460243196751932241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879793946990929002576321 3659845460243196751932241)
                ·
                  refine ⟨2744884095182397563949181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659845460243196751932241 2744884095182397563949181)
                  ·
                    refine ⟨1029331535693399086480943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744884095182397563949181 1029331535693399086480943)
                    ·
                      rfl

theorem cell22_3006924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_3006924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006924 prefixEnd_3006924 := by exact prefixLift 3006924
  have htrace : WordTrace (prefixWord ++ tailWord_3006924) baseStart_3006924 baseEnd_3006924 := by
    simpa [prefixWord, tailWord_3006924, baseEnd_3006924] using wordTrace_append hprefix tailTrace_3006924
  have hstable : (prefixWord ++ tailWord_3006924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006924).length < 2 ^ (prefixWord ++ tailWord_3006924).sum := by decide
  have hdescent : baseEnd_3006924 < baseStart_3006924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006948 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3006948 : Nat := 118140960795 + 3006948 * 2 ^ 59
def prefixEnd_3006948 : Nat := 4983230072969 + 3 ^ 40 * 3006948 * 2
def baseEnd_3006948 : Nat := 343113250461290341293623

theorem tailTrace_3006948 : CollatzResearch.WordTrace tailWord_3006948 prefixEnd_3006948 343113250461290341293623 := by
  unfold tailWord_3006948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54836201755174208339018749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73114935673565611118691665 54836201755174208339018749)
  ·
    refine ⟨20563575658190328127132031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54836201755174208339018749 20563575658190328127132031)
    ·
      refine ⟨30845363487285492190698047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20563575658190328127132031 30845363487285492190698047)
      ·
        refine ⟨46268045230928238286047071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30845363487285492190698047 46268045230928238286047071)
        ·
          refine ⟨69402067846392357429070607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46268045230928238286047071 69402067846392357429070607)
          ·
            refine ⟨104103101769588536143605911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69402067846392357429070607 104103101769588536143605911)
            ·
              refine ⟨156154652654382804215408867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104103101769588536143605911 156154652654382804215408867)
              ·
                refine ⟨234231978981574206323113301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156154652654382804215408867 234231978981574206323113301)
                ·
                  refine ⟨343113250461290341293623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 234231978981574206323113301 343113250461290341293623)
                  ·
                    rfl

theorem cell22_3006948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3006948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006948 prefixEnd_3006948 := by exact prefixLift 3006948
  have htrace : WordTrace (prefixWord ++ tailWord_3006948) baseStart_3006948 baseEnd_3006948 := by
    simpa [prefixWord, tailWord_3006948, baseEnd_3006948] using wordTrace_append hprefix tailTrace_3006948
  have hstable : (prefixWord ++ tailWord_3006948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006948).length < 2 ^ (prefixWord ++ tailWord_3006948).sum := by decide
  have hdescent : baseEnd_3006948 < baseStart_3006948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006952 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3006952 : Nat := 118140960795 + 3006952 * 2 ^ 59
def prefixEnd_3006952 : Nat := 4983230072969 + 3 ^ 40 * 3006952 * 2
def baseEnd_3006952 : Nat := 1029341120665616346780857

theorem tailTrace_3006952 : CollatzResearch.WordTrace tailWord_3006952 prefixEnd_3006952 1029341120665616346780857 := by
  unfold tailWord_3006952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54836274701166962680591555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73115032934889283574122073 54836274701166962680591555)
  ·
    refine ⟨82254412051750444020887333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54836274701166962680591555 82254412051750444020887333)
    ·
      refine ⟨15422702259703208253916375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82254412051750444020887333 15422702259703208253916375)
      ·
        refine ⟨23134053389554812380874563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422702259703208253916375 23134053389554812380874563)
        ·
          refine ⟨34701080084332218571311845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23134053389554812380874563 34701080084332218571311845)
          ·
            refine ⟨6506452515812290982120971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34701080084332218571311845 6506452515812290982120971)
            ·
              refine ⟨9759678773718436473181457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506452515812290982120971 9759678773718436473181457)
              ·
                refine ⟨7319759080288827354886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9759678773718436473181457 7319759080288827354886093)
                ·
                  refine ⟨2744909655108310258082285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7319759080288827354886093 2744909655108310258082285)
                  ·
                    refine ⟨1029341120665616346780857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744909655108310258082285 1029341120665616346780857)
                    ·
                      rfl

theorem cell22_3006952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3006952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006952 prefixEnd_3006952 := by exact prefixLift 3006952
  have htrace : WordTrace (prefixWord ++ tailWord_3006952) baseStart_3006952 baseEnd_3006952 := by
    simpa [prefixWord, tailWord_3006952, baseEnd_3006952] using wordTrace_append hprefix tailTrace_3006952
  have hstable : (prefixWord ++ tailWord_3006952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006952).length < 2 ^ (prefixWord ++ tailWord_3006952).sum := by decide
  have hdescent : baseEnd_3006952 < baseStart_3006952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006963 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_3006963 : Nat := 118140960795 + 3006963 * 2 ^ 59
def prefixEnd_3006963 : Nat := 4983230072969 + 3 ^ 40 * 3006963 * 2
def baseEnd_3006963 : Nat := 1029344886190415984755823

theorem tailTrace_3006963 : CollatzResearch.WordTrace tailWord_3006963 prefixEnd_3006963 1029344886190415984755823 := by
  unfold tailWord_3006963
  simp only [CollatzResearch.WordTrace]
  refine ⟨109672950605294074239833543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73115300403529382826555695 109672950605294074239833543)
  ·
    refine ⟨164509425907941111359750315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109672950605294074239833543 164509425907941111359750315)
    ·
      refine ⟨246764138861911667039625473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164509425907941111359750315 246764138861911667039625473)
      ·
        refine ⟨185073104146433750279719105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246764138861911667039625473 185073104146433750279719105)
        ·
          refine ⟨138804828109825312709789329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185073104146433750279719105 138804828109825312709789329)
          ·
            refine ⟨104103621082368984532341997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138804828109825312709789329 104103621082368984532341997)
            ·
              refine ⟨39038857905888369199628249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104103621082368984532341997 39038857905888369199628249)
              ·
                refine ⟨29279143429416276899721187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39038857905888369199628249 29279143429416276899721187)
                ·
                  refine ⟨43918715144124415349581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29279143429416276899721187 43918715144124415349581781)
                  ·
                    refine ⟨1029344886190415984755823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43918715144124415349581781 1029344886190415984755823)
                    ·
                      rfl

theorem cell22_3006963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_3006963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006963 prefixEnd_3006963 := by exact prefixLift 3006963
  have htrace : WordTrace (prefixWord ++ tailWord_3006963) baseStart_3006963 baseEnd_3006963 := by
    simpa [prefixWord, tailWord_3006963, baseEnd_3006963] using wordTrace_append hprefix tailTrace_3006963
  have hstable : (prefixWord ++ tailWord_3006963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006963).length < 2 ^ (prefixWord ++ tailWord_3006963).sum := by decide
  have hdescent : baseEnd_3006963 < baseStart_3006963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007025 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3007025 : Nat := 118140960795 + 3007025 * 2 ^ 59
def prefixEnd_3007025 : Nat := 4983230072969 + 3 ^ 40 * 3007025 * 2
def baseEnd_3007025 : Nat := 1029366110057468489705633

theorem tailTrace_3007025 : CollatzResearch.WordTrace tailWord_3007025 prefixEnd_3007025 1029366110057468489705633 := by
  unfold tailWord_3007025
  simp only [CollatzResearch.WordTrace]
  refine ⟨109675211931069458828590529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73116807954046305885727019 109675211931069458828590529)
  ·
    refine ⟨82256408948302094121442897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109675211931069458828590529 82256408948302094121442897)
    ·
      refine ⟨61692306711226570591082173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82256408948302094121442897 61692306711226570591082173)
      ·
        refine ⟨23134615016709963971655815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61692306711226570591082173 23134615016709963971655815)
        ·
          refine ⟨34701922525064945957483723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23134615016709963971655815 34701922525064945957483723)
          ·
            refine ⟨52052883787597418936225585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34701922525064945957483723 52052883787597418936225585)
            ·
              refine ⟨39039662840698064202169189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52052883787597418936225585 39039662840698064202169189)
              ·
                refine ⟨7319936782630887037906723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39039662840698064202169189 7319936782630887037906723)
                ·
                  refine ⟨10979905173946330556860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319936782630887037906723 10979905173946330556860085)
                  ·
                    refine ⟨1029366110057468489705633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10979905173946330556860085 1029366110057468489705633)
                    ·
                      rfl

theorem cell22_3007025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3007025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007025 prefixEnd_3007025 := by exact prefixLift 3007025
  have htrace : WordTrace (prefixWord ++ tailWord_3007025) baseStart_3007025 baseEnd_3007025 := by
    simpa [prefixWord, tailWord_3007025, baseEnd_3007025] using wordTrace_append hprefix tailTrace_3007025
  have hstable : (prefixWord ++ tailWord_3007025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007025).length < 2 ^ (prefixWord ++ tailWord_3007025).sum := by decide
  have hdescent : baseEnd_3007025 < baseStart_3007025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007040 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_3007040 : Nat := 118140960795 + 3007040 * 2 ^ 59
def prefixEnd_3007040 : Nat := 4983230072969 + 3 ^ 40 * 3007040 * 2
def baseEnd_3007040 : Nat := 1029371244864013450580587

theorem tailTrace_3007040 : CollatzResearch.WordTrace tailWord_3007040 prefixEnd_3007040 1029371244864013450580587 := by
  unfold tailWord_3007040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54837879513007558195193287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73117172684010077593591049 54837879513007558195193287)
  ·
    refine ⟨82256819269511337292789931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54837879513007558195193287 82256819269511337292789931)
    ·
      refine ⟨123385228904267005939184897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82256819269511337292789931 123385228904267005939184897)
      ·
        refine ⟨92538921678200254454388673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123385228904267005939184897 92538921678200254454388673)
        ·
          refine ⟨69404191258650190840791505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92538921678200254454388673 69404191258650190840791505)
          ·
            refine ⟨52053143443987643130593629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69404191258650190840791505 52053143443987643130593629)
            ·
              refine ⟨19519928791495366173972611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52053143443987643130593629 19519928791495366173972611)
              ·
                refine ⟨29279893187243049260958917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19519928791495366173972611 29279893187243049260958917)
                ·
                  refine ⟨5489979972608071736429797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29279893187243049260958917 5489979972608071736429797)
                  ·
                    refine ⟨1029371244864013450580587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489979972608071736429797 1029371244864013450580587)
                    ·
                      rfl

theorem cell22_3007040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_3007040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007040 prefixEnd_3007040 := by exact prefixLift 3007040
  have htrace : WordTrace (prefixWord ++ tailWord_3007040) baseStart_3007040 baseEnd_3007040 := by
    simpa [prefixWord, tailWord_3007040, baseEnd_3007040] using wordTrace_append hprefix tailTrace_3007040
  have hstable : (prefixWord ++ tailWord_3007040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007040).length < 2 ^ (prefixWord ++ tailWord_3007040).sum := by decide
  have hdescent : baseEnd_3007040 < baseStart_3007040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007100 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_3007100 : Nat := 118140960795 + 3007100 * 2 ^ 59
def prefixEnd_3007100 : Nat := 4983230072969 + 3 ^ 40 * 3007100 * 2
def baseEnd_3007100 : Nat := 343130594696731098026801

theorem tailTrace_3007100 : CollatzResearch.WordTrace tailWord_3007100 prefixEnd_3007100 343130594696731098026801 := by
  unfold tailWord_3007100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54838973702898873318785377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73118631603865164425047169 54838973702898873318785377)
  ·
    refine ⟨41129230277174154989089033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54838973702898873318785377 41129230277174154989089033)
    ·
      refine ⟨30846922707880616241816775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41129230277174154989089033 30846922707880616241816775)
      ·
        refine ⟨46270384061820924362725163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30846922707880616241816775 46270384061820924362725163)
        ·
          refine ⟨69405576092731386544087745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46270384061820924362725163 69405576092731386544087745)
          ·
            refine ⟨52054182069548539908065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69405576092731386544087745 52054182069548539908065809)
            ·
              refine ⟨39040636552161404931049357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52054182069548539908065809 39040636552161404931049357)
              ·
                refine ⟨14640238707060526849143509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39040636552161404931049357 14640238707060526849143509)
                ·
                  refine ⟨343130594696731098026801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14640238707060526849143509 343130594696731098026801)
                  ·
                    rfl

theorem cell22_3007100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_3007100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007100 prefixEnd_3007100 := by exact prefixLift 3007100
  have htrace : WordTrace (prefixWord ++ tailWord_3007100) baseStart_3007100 baseEnd_3007100 := by
    simpa [prefixWord, tailWord_3007100, baseEnd_3007100] using wordTrace_append hprefix tailTrace_3007100
  have hstable : (prefixWord ++ tailWord_3007100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007100).length < 2 ^ (prefixWord ++ tailWord_3007100).sum := by decide
  have hdescent : baseEnd_3007100 < baseStart_3007100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007160 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3007160 : Nat := 118140960795 + 3007160 * 2 ^ 59
def prefixEnd_3007160 : Nat := 4983230072969 + 3 ^ 40 * 3007160 * 2
def baseEnd_3007160 : Nat := 1029412323316373137580219

theorem tailTrace_3007160 : CollatzResearch.WordTrace tailWord_3007160 prefixEnd_3007160 1029412323316373137580219 := by
  unfold tailWord_3007160
  simp only [CollatzResearch.WordTrace]
  refine ⟨54840067892790188442377467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73120090523720251256503289 54840067892790188442377467)
  ·
    refine ⟨82260101839185282663566201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54840067892790188442377467 82260101839185282663566201)
    ·
      refine ⟨61695076379388961997674651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82260101839185282663566201 61695076379388961997674651)
      ·
        refine ⟨92542614569083442996511977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61695076379388961997674651 92542614569083442996511977)
        ·
          refine ⟨69406960926812582247383983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92542614569083442996511977 69406960926812582247383983)
          ·
            refine ⟨104110441390218873371075975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69406960926812582247383983 104110441390218873371075975)
            ·
              refine ⟨156165662085328310056613963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104110441390218873371075975 156165662085328310056613963)
              ·
                refine ⟨234248493127992465084920945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156165662085328310056613963 234248493127992465084920945)
                ·
                  refine ⟨175686369845994348813690709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234248493127992465084920945 175686369845994348813690709)
                  ·
                    refine ⟨1029412323316373137580219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175686369845994348813690709 1029412323316373137580219)
                    ·
                      rfl

theorem cell22_3007160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3007160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007160 prefixEnd_3007160 := by exact prefixLift 3007160
  have htrace : WordTrace (prefixWord ++ tailWord_3007160) baseStart_3007160 baseEnd_3007160 := by
    simpa [prefixWord, tailWord_3007160, baseEnd_3007160] using wordTrace_append hprefix tailTrace_3007160
  have hstable : (prefixWord ++ tailWord_3007160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007160).length < 2 ^ (prefixWord ++ tailWord_3007160).sum := by decide
  have hdescent : baseEnd_3007160 < baseStart_3007160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007162 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_3007162 : Nat := 118140960795 + 3007162 * 2 ^ 59
def prefixEnd_3007162 : Nat := 4983230072969 + 3 ^ 40 * 3007162 * 2
def baseEnd_3007162 : Nat := 343137669319081933010071

theorem tailTrace_3007162 : CollatzResearch.WordTrace tailWord_3007162 prefixEnd_3007162 343137669319081933010071 := by
  unfold tailWord_3007162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27420052182893282806581935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73120139154382087484218493 27420052182893282806581935)
  ·
    refine ⟨41130078274339924209872903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27420052182893282806581935 41130078274339924209872903)
    ·
      refine ⟨61695117411509886314809355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41130078274339924209872903 61695117411509886314809355)
      ·
        refine ⟨92542676117264829472214033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61695117411509886314809355 92542676117264829472214033)
        ·
          refine ⟨69407007087948622104160525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92542676117264829472214033 69407007087948622104160525)
          ·
            refine ⟨26027627657980733289060197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69407007087948622104160525 26027627657980733289060197)
            ·
              refine ⟨4880180185871387491698787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26027627657980733289060197 4880180185871387491698787)
              ·
                refine ⟨7320270278807081237548181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880180185871387491698787 7320270278807081237548181)
                ·
                  refine ⟨343137669319081933010071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7320270278807081237548181 343137669319081933010071)
                  ·
                    rfl

theorem cell22_3007162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_3007162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007162 prefixEnd_3007162 := by exact prefixLift 3007162
  have htrace : WordTrace (prefixWord ++ tailWord_3007162) baseStart_3007162 baseEnd_3007162 := by
    simpa [prefixWord, tailWord_3007162, baseEnd_3007162] using wordTrace_append hprefix tailTrace_3007162
  have hstable : (prefixWord ++ tailWord_3007162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007162).length < 2 ^ (prefixWord ++ tailWord_3007162).sum := by decide
  have hdescent : baseEnd_3007162 < baseStart_3007162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007192 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3007192 : Nat := 118140960795 + 3007192 * 2 ^ 59
def prefixEnd_3007192 : Nat := 4983230072969 + 3 ^ 40 * 3007192 * 2
def baseEnd_3007192 : Nat := 1029423277570335720780121

theorem tailTrace_3007192 : CollatzResearch.WordTrace tailWord_3007192 prefixEnd_3007192 1029423277570335720780121 := by
  unfold tailWord_3007192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54840651460732223174959915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73120868614309630899946553 54840651460732223174959915)
  ·
    refine ⟨82260977191098334762439873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54840651460732223174959915 82260977191098334762439873)
    ·
      refine ⟨61695732893323751071829905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82260977191098334762439873 61695732893323751071829905)
      ·
        refine ⟨46271799669992813303872429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61695732893323751071829905 46271799669992813303872429)
        ·
          refine ⟨17351924876247304988952161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46271799669992813303872429 17351924876247304988952161)
          ·
            refine ⟨13013943657185478741714121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17351924876247304988952161 13013943657185478741714121)
            ·
              refine ⟨9760457742889109056285591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13013943657185478741714121 9760457742889109056285591)
              ·
                refine ⟨14640686614333663584428387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760457742889109056285591 14640686614333663584428387)
                ·
                  refine ⟨21961029921500495376642581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14640686614333663584428387 21961029921500495376642581)
                  ·
                    refine ⟨1029423277570335720780121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21961029921500495376642581 1029423277570335720780121)
                    ·
                      rfl

theorem cell22_3007192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3007192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007192 prefixEnd_3007192 := by exact prefixLift 3007192
  have htrace : WordTrace (prefixWord ++ tailWord_3007192) baseStart_3007192 baseEnd_3007192 := by
    simpa [prefixWord, tailWord_3007192, baseEnd_3007192] using wordTrace_append hprefix tailTrace_3007192
  have hstable : (prefixWord ++ tailWord_3007192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007192).length < 2 ^ (prefixWord ++ tailWord_3007192).sum := by decide
  have hdescent : baseEnd_3007192 < baseStart_3007192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007228 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3007228 : Nat := 118140960795 + 3007228 * 2 ^ 59
def prefixEnd_3007228 : Nat := 4983230072969 + 3 ^ 40 * 3007228 * 2
def baseEnd_3007228 : Nat := 1029435601106043626880011

theorem tailTrace_3007228 : CollatzResearch.WordTrace tailWord_3007228 prefixEnd_3007228 1029435601106043626880011 := by
  unfold tailWord_3007228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54841307974667012249115169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73121743966222682998820225 54841307974667012249115169)
  ·
    refine ⟨41130980981000259186836377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54841307974667012249115169 41130980981000259186836377)
    ·
      refine ⟨30848235735750194390127283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41130980981000259186836377 30848235735750194390127283)
      ·
        refine ⟨46272353603625291585190925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30848235735750194390127283 46272353603625291585190925)
        ·
          refine ⟨17352132601359484344446597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46272353603625291585190925 17352132601359484344446597)
          ·
            refine ⟨3253524862754903314583737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17352132601359484344446597 3253524862754903314583737)
            ·
              refine ⟨2440143647066177485937803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253524862754903314583737 2440143647066177485937803)
              ·
                refine ⟨3660215470599266228906705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440143647066177485937803 3660215470599266228906705)
                ·
                  refine ⟨2745161602949449671680029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660215470599266228906705 2745161602949449671680029)
                  ·
                    refine ⟨1029435601106043626880011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745161602949449671680029 1029435601106043626880011)
                    ·
                      rfl

theorem cell22_3007228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3007228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007228 prefixEnd_3007228 := by exact prefixLift 3007228
  have htrace : WordTrace (prefixWord ++ tailWord_3007228) baseStart_3007228 baseEnd_3007228 := by
    simpa [prefixWord, tailWord_3007228, baseEnd_3007228] using wordTrace_append hprefix tailTrace_3007228
  have hstable : (prefixWord ++ tailWord_3007228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007228).length < 2 ^ (prefixWord ++ tailWord_3007228).sum := by decide
  have hdescent : baseEnd_3007228 < baseStart_3007228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007256 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_3007256 : Nat := 118140960795 + 3007256 * 2 ^ 59
def prefixEnd_3007256 : Nat := 4983230072969 + 3 ^ 40 * 3007256 * 2
def baseEnd_3007256 : Nat := 1029445186078260887179925

theorem tailTrace_3007256 : CollatzResearch.WordTrace tailWord_3007256 prefixEnd_3007256 1029445186078260887179925 := by
  unfold tailWord_3007256
  simp only [CollatzResearch.WordTrace]
  refine ⟨54841818596616292640124811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73122424795488390186833081 54841818596616292640124811)
  ·
    refine ⟨82262727894924438960187217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54841818596616292640124811 82262727894924438960187217)
    ·
      refine ⟨61697045921193329220140413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82262727894924438960187217 61697045921193329220140413)
      ·
        refine ⟨23136392220447498457552655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61697045921193329220140413 23136392220447498457552655)
        ·
          refine ⟨34704588330671247686328983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23136392220447498457552655 34704588330671247686328983)
          ·
            refine ⟨52056882496006871529493475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34704588330671247686328983 52056882496006871529493475)
            ·
              refine ⟨78085323744010307294240213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52056882496006871529493475 78085323744010307294240213)
              ·
                refine ⟨1830124775250241577208755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78085323744010307294240213 1830124775250241577208755)
                ·
                  refine ⟨2745187162875362365813133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830124775250241577208755 2745187162875362365813133)
                  ·
                    refine ⟨1029445186078260887179925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745187162875362365813133 1029445186078260887179925)
                    ·
                      rfl

theorem cell22_3007256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_3007256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007256 prefixEnd_3007256 := by exact prefixLift 3007256
  have htrace : WordTrace (prefixWord ++ tailWord_3007256) baseStart_3007256 baseEnd_3007256 := by
    simpa [prefixWord, tailWord_3007256, baseEnd_3007256] using wordTrace_append hprefix tailTrace_3007256
  have hstable : (prefixWord ++ tailWord_3007256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007256).length < 2 ^ (prefixWord ++ tailWord_3007256).sum := by decide
  have hdescent : baseEnd_3007256 < baseStart_3007256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007267 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_3007267 : Nat := 118140960795 + 3007267 * 2 ^ 59
def prefixEnd_3007267 : Nat := 4983230072969 + 3 ^ 40 * 3007267 * 2
def baseEnd_3007267 : Nat := 1029448951603060525154891

theorem tailTrace_3007267 : CollatzResearch.WordTrace tailWord_3007267 prefixEnd_3007267 1029448951603060525154891 := by
  unfold tailWord_3007267
  simp only [CollatzResearch.WordTrace]
  refine ⟨109684038396192734158900055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73122692264128489439266703 109684038396192734158900055)
  ·
    refine ⟨164526057594289101238350083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109684038396192734158900055 164526057594289101238350083)
    ·
      refine ⟨246789086391433651857525125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164526057594289101238350083 246789086391433651857525125)
      ·
        refine ⟨46272953698393809723285961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246789086391433651857525125 46272953698393809723285961)
        ·
          refine ⟨34704715273795357292464471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46272953698393809723285961 34704715273795357292464471)
          ·
            refine ⟨52057072910693035938696707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34704715273795357292464471 52057072910693035938696707)
            ·
              refine ⟨78085609366039553908045061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52057072910693035938696707 78085609366039553908045061)
              ·
                refine ⟨14641051756132416357758449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78085609366039553908045061 14641051756132416357758449)
                ·
                  refine ⟨10980788817099312268318837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14641051756132416357758449 10980788817099312268318837)
                  ·
                    refine ⟨1029448951603060525154891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10980788817099312268318837 1029448951603060525154891)
                    ·
                      rfl

theorem cell22_3007267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_3007267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007267 prefixEnd_3007267 := by exact prefixLift 3007267
  have htrace : WordTrace (prefixWord ++ tailWord_3007267) baseStart_3007267 baseEnd_3007267 := by
    simpa [prefixWord, tailWord_3007267, baseEnd_3007267] using wordTrace_append hprefix tailTrace_3007267
  have hstable : (prefixWord ++ tailWord_3007267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007267).length < 2 ^ (prefixWord ++ tailWord_3007267).sum := by decide
  have hdescent : baseEnd_3007267 < baseStart_3007267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007269 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 5]
def baseStart_3007269 : Nat := 118140960795 + 3007269 * 2 ^ 59
def prefixEnd_3007269 : Nat := 4983230072969 + 3 ^ 40 * 3007269 * 2
def baseEnd_3007269 : Nat := 343149878747977728868295

theorem tailTrace_3007269 : CollatzResearch.WordTrace tailWord_3007269 prefixEnd_3007269 343149878747977728868295 := by
  unfold tailWord_3007269
  simp only [CollatzResearch.WordTrace]
  refine ⟨109684111342185488500472861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73122740894790325666981907 109684111342185488500472861)
  ·
    refine ⟨41131541753319558187677323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109684111342185488500472861 41131541753319558187677323)
    ·
      refine ⟨61697312629979337281515985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41131541753319558187677323 61697312629979337281515985)
      ·
        refine ⟨46272984472484502961136989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61697312629979337281515985 46272984472484502961136989)
        ·
          refine ⟨17352369177181688610426371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46272984472484502961136989 17352369177181688610426371)
          ·
            refine ⟨26028553765772532915639557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17352369177181688610426371 26028553765772532915639557)
            ·
              refine ⟨4880353831082349921682417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26028553765772532915639557 4880353831082349921682417)
              ·
                refine ⟨3660265373311762441261813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880353831082349921682417 3660265373311762441261813)
                ·
                  refine ⟨343149878747977728868295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660265373311762441261813 343149878747977728868295)
                  ·
                    rfl

theorem cell22_3007269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_3007269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007269 prefixEnd_3007269 := by exact prefixLift 3007269
  have htrace : WordTrace (prefixWord ++ tailWord_3007269) baseStart_3007269 baseEnd_3007269 := by
    simpa [prefixWord, tailWord_3007269, baseEnd_3007269] using wordTrace_append hprefix tailTrace_3007269
  have hstable : (prefixWord ++ tailWord_3007269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007269).length < 2 ^ (prefixWord ++ tailWord_3007269).sum := by decide
  have hdescent : baseEnd_3007269 < baseStart_3007269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007299 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 1, 4]
def baseStart_3007299 : Nat := 118140960795 + 3007299 * 2 ^ 59
def prefixEnd_3007299 : Nat := 4983230072969 + 3 ^ 40 * 3007299 * 2
def baseEnd_3007299 : Nat := 1029459905857023108354793

theorem tailTrace_3007299 : CollatzResearch.WordTrace tailWord_3007299 prefixEnd_3007299 1029459905857023108354793 := by
  unfold tailWord_3007299
  simp only [CollatzResearch.WordTrace]
  refine ⟨109685205532076803624064951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73123470354717869082709967 109685205532076803624064951)
  ·
    refine ⟨164527808298115205436097427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109685205532076803624064951 164527808298115205436097427)
    ·
      refine ⟨246791712447172808154146141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164527808298115205436097427 246791712447172808154146141)
      ·
        refine ⟨92546892167689803057804803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246791712447172808154146141 92546892167689803057804803)
        ·
          refine ⟨138820338251534704586707205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92546892167689803057804803 138820338251534704586707205)
          ·
            refine ⟨26028813422162757110007601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138820338251534704586707205 26028813422162757110007601)
            ·
              refine ⟨19521610066622067832505701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26028813422162757110007601 19521610066622067832505701)
              ·
                refine ⟨3660301887491637718594819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19521610066622067832505701 3660301887491637718594819)
                ·
                  refine ⟨5490452831237456577892229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660301887491637718594819 5490452831237456577892229)
                  ·
                    refine ⟨1029459905857023108354793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5490452831237456577892229 1029459905857023108354793)
                    ·
                      rfl

theorem cell22_3007299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_3007299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007299 prefixEnd_3007299 := by exact prefixLift 3007299
  have htrace : WordTrace (prefixWord ++ tailWord_3007299) baseStart_3007299 baseEnd_3007299 := by
    simpa [prefixWord, tailWord_3007299, baseEnd_3007299] using wordTrace_append hprefix tailTrace_3007299
  have hstable : (prefixWord ++ tailWord_3007299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007299).length < 2 ^ (prefixWord ++ tailWord_3007299).sum := by decide
  have hdescent : baseEnd_3007299 < baseStart_3007299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007331 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 4]
def baseStart_3007331 : Nat := 118140960795 + 3007331 * 2 ^ 59
def prefixEnd_3007331 : Nat := 4983230072969 + 3 ^ 40 * 3007331 * 2
def baseEnd_3007331 : Nat := 343156953370328563851565

theorem tailTrace_3007331 : CollatzResearch.WordTrace tailWord_3007331 prefixEnd_3007331 343156953370328563851565 := by
  unfold tailWord_3007331
  simp only [CollatzResearch.WordTrace]
  refine ⟨109686372667960873089229847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73124248445307248726153231 109686372667960873089229847)
  ·
    refine ⟨164529559001941309633844771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109686372667960873089229847 164529559001941309633844771)
    ·
      refine ⟨246794338502911964450767157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164529559001941309633844771 246794338502911964450767157)
      ·
        refine ⟨23136969234647996667259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246794338502911964450767157 23136969234647996667259421)
        ·
          refine ⟨8676363462992998750222283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23136969234647996667259421 8676363462992998750222283)
          ·
            refine ⟨13014545194489498125333425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676363462992998750222283 13014545194489498125333425)
            ·
              refine ⟨9760908895867123594000069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13014545194489498125333425 9760908895867123594000069)
              ·
                refine ⟨1830170417975085673875013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9760908895867123594000069 1830170417975085673875013)
                ·
                  refine ⟨343156953370328563851565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830170417975085673875013 343156953370328563851565)
                  ·
                    rfl

theorem cell22_3007331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 4].length) (baseStart_3007331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007331 prefixEnd_3007331 := by exact prefixLift 3007331
  have htrace : WordTrace (prefixWord ++ tailWord_3007331) baseStart_3007331 baseEnd_3007331 := by
    simpa [prefixWord, tailWord_3007331, baseEnd_3007331] using wordTrace_append hprefix tailTrace_3007331
  have hstable : (prefixWord ++ tailWord_3007331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007331).length < 2 ^ (prefixWord ++ tailWord_3007331).sum := by decide
  have hdescent : baseEnd_3007331 < baseStart_3007331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007346 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3007346 : Nat := 118140960795 + 3007346 * 2 ^ 59
def prefixEnd_3007346 : Nat := 4983230072969 + 3 ^ 40 * 3007346 * 2
def baseEnd_3007346 : Nat := 1029475994917530652429649

theorem tailTrace_3007346 : CollatzResearch.WordTrace tailWord_3007346 prefixEnd_3007346 1029475994917530652429649 := by
  unfold tailWord_3007346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27421729940726632662756473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73124613175271020434017261 27421729940726632662756473)
  ·
    refine ⟨20566297455544974497067355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27421729940726632662756473 20566297455544974497067355)
    ·
      refine ⟨30849446183317461745601033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20566297455544974497067355 30849446183317461745601033)
      ·
        refine ⟨23137084637488096309200775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30849446183317461745601033 23137084637488096309200775)
        ·
          refine ⟨34705626956232144463801163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23137084637488096309200775 34705626956232144463801163)
          ·
            refine ⟨52058440434348216695701745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34705626956232144463801163 52058440434348216695701745)
            ·
              refine ⟨39043830325761162521776309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52058440434348216695701745 39043830325761162521776309)
              ·
                refine ⟨3660359093040108986416529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39043830325761162521776309 3660359093040108986416529)
                ·
                  refine ⟨2745269319780081739812397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660359093040108986416529 2745269319780081739812397)
                  ·
                    refine ⟨1029475994917530652429649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745269319780081739812397 1029475994917530652429649)
                    ·
                      rfl

theorem cell22_3007346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3007346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007346 prefixEnd_3007346 := by exact prefixLift 3007346
  have htrace : WordTrace (prefixWord ++ tailWord_3007346) baseStart_3007346 baseEnd_3007346 := by
    simpa [prefixWord, tailWord_3007346, baseEnd_3007346] using wordTrace_append hprefix tailTrace_3007346
  have hstable : (prefixWord ++ tailWord_3007346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007346).length < 2 ^ (prefixWord ++ tailWord_3007346).sum := by decide
  have hdescent : baseEnd_3007346 < baseStart_3007346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007359 : List Nat := [1, 1, 2, 2, 1, 1, 8, 6]
def baseStart_3007359 : Nat := 118140960795 + 3007359 * 2 ^ 59
def prefixEnd_3007359 : Nat := 4983230072969 + 3 ^ 40 * 3007359 * 2
def baseEnd_3007359 : Nat := 114386716120355883539401

theorem tailTrace_3007359 : CollatzResearch.WordTrace tailWord_3007359 prefixEnd_3007359 114386716120355883539401 := by
  unfold tailWord_3007359
  simp only [CollatzResearch.WordTrace]
  refine ⟨109687393911859433871249131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73124929274572955914166087 109687393911859433871249131)
  ·
    refine ⟨164531090867789150806873697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109687393911859433871249131 164531090867789150806873697)
    ·
      refine ⟨123398318150841863105155273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164531090867789150806873697 123398318150841863105155273)
      ·
        refine ⟨92548738613131397328866455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123398318150841863105155273 92548738613131397328866455)
        ·
          refine ⟨138823107919697095993299683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92548738613131397328866455 138823107919697095993299683)
          ·
            refine ⟨208234661879545643989949525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138823107919697095993299683 208234661879545643989949525)
            ·
              refine ⟨2440249943900925515507221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 208234661879545643989949525 2440249943900925515507221)
              ·
                refine ⟨114386716120355883539401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2440249943900925515507221 114386716120355883539401)
                ·
                  rfl

theorem cell22_3007359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 6].length) (baseStart_3007359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007359 prefixEnd_3007359 := by exact prefixLift 3007359
  have htrace : WordTrace (prefixWord ++ tailWord_3007359) baseStart_3007359 baseEnd_3007359 := by
    simpa [prefixWord, tailWord_3007359, baseEnd_3007359] using wordTrace_append hprefix tailTrace_3007359
  have hstable : (prefixWord ++ tailWord_3007359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007359).length < 2 ^ (prefixWord ++ tailWord_3007359).sum := by decide
  have hdescent : baseEnd_3007359 < baseStart_3007359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007378 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3007378 : Nat := 118140960795 + 3007378 * 2 ^ 59
def prefixEnd_3007378 : Nat := 4983230072969 + 3 ^ 40 * 3007378 * 2
def baseEnd_3007378 : Nat := 1029486949171493235629551

theorem tailTrace_3007378 : CollatzResearch.WordTrace tailWord_3007378 prefixEnd_3007378 1029486949171493235629551 := by
  unfold tailWord_3007378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422021724697650029047697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73125391265860400077460525 27422021724697650029047697)
  ·
    refine ⟨20566516293523237521785773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27422021724697650029047697 20566516293523237521785773)
    ·
      refine ⟨7712443610071214070669665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20566516293523237521785773 7712443610071214070669665)
      ·
        refine ⟨5784332707553410553002249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7712443610071214070669665 5784332707553410553002249)
        ·
          refine ⟨4338249530665057914751687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5784332707553410553002249 4338249530665057914751687)
          ·
            refine ⟨6507374295997586872127531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338249530665057914751687 6507374295997586872127531)
            ·
              refine ⟨9761061443996380308191297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507374295997586872127531 9761061443996380308191297)
              ·
                refine ⟨7320796082997285231143473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761061443996380308191297 7320796082997285231143473)
                ·
                  refine ⟨5490597062247963923357605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320796082997285231143473 5490597062247963923357605)
                  ·
                    refine ⟨1029486949171493235629551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5490597062247963923357605 1029486949171493235629551)
                    ·
                      rfl

theorem cell22_3007378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3007378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007378 prefixEnd_3007378 := by exact prefixLift 3007378
  have htrace : WordTrace (prefixWord ++ tailWord_3007378) baseStart_3007378 baseEnd_3007378 := by
    simpa [prefixWord, tailWord_3007378, baseEnd_3007378] using wordTrace_append hprefix tailTrace_3007378
  have hstable : (prefixWord ++ tailWord_3007378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007378).length < 2 ^ (prefixWord ++ tailWord_3007378).sum := by decide
  have hdescent : baseEnd_3007378 < baseStart_3007378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007389 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3007389 : Nat := 118140960795 + 3007389 * 2 ^ 59
def prefixEnd_3007389 : Nat := 4983230072969 + 3 ^ 40 * 3007389 * 2
def baseEnd_3007389 : Nat := 1029490714696292873604517

theorem tailTrace_3007389 : CollatzResearch.WordTrace tailWord_3007389 prefixEnd_3007389 1029490714696292873604517 := by
  unfold tailWord_3007389
  simp only [CollatzResearch.WordTrace]
  refine ⟨109688488101750748994841221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73125658734500499329894147 109688488101750748994841221)
  ·
    refine ⟨20566591519078265436532729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109688488101750748994841221 20566591519078265436532729)
    ·
      refine ⟨15424943639308699077399547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20566591519078265436532729 15424943639308699077399547)
      ·
        refine ⟨23137415458963048616099321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15424943639308699077399547 23137415458963048616099321)
        ·
          refine ⟨17353061594222286462074491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23137415458963048616099321 17353061594222286462074491)
          ·
            refine ⟨26029592391333429693111737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17353061594222286462074491 26029592391333429693111737)
            ·
              refine ⟨19522194293500072269833803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26029592391333429693111737 19522194293500072269833803)
              ·
                refine ⟨29283291440250108404750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19522194293500072269833803 29283291440250108404750705)
                ·
                  refine ⟨21962468580187581303563029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29283291440250108404750705 21962468580187581303563029)
                  ·
                    refine ⟨1029490714696292873604517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21962468580187581303563029 1029490714696292873604517)
                    ·
                      rfl

theorem cell22_3007389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3007389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007389 prefixEnd_3007389 := by exact prefixLift 3007389
  have htrace : WordTrace (prefixWord ++ tailWord_3007389) baseStart_3007389 baseEnd_3007389 := by
    simpa [prefixWord, tailWord_3007389, baseEnd_3007389] using wordTrace_append hprefix tailTrace_3007389
  have hstable : (prefixWord ++ tailWord_3007389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007389).length < 2 ^ (prefixWord ++ tailWord_3007389).sum := by decide
  have hdescent : baseEnd_3007389 < baseStart_3007389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007404 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_3007404 : Nat := 118140960795 + 3007404 * 2 ^ 59
def prefixEnd_3007404 : Nat := 4983230072969 + 3 ^ 40 * 3007404 * 2
def baseEnd_3007404 : Nat := 343165283167612611493157

theorem tailTrace_3007404 : CollatzResearch.WordTrace tailWord_3007404 prefixEnd_3007404 343165283167612611493157 := by
  unfold tailWord_3007404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54844517598348203278318633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73126023464464271037758177 54844517598348203278318633)
  ·
    refine ⟨41133388198761152458738975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54844517598348203278318633 41133388198761152458738975)
    ·
      refine ⟨61700082298141728688108463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41133388198761152458738975 61700082298141728688108463)
      ·
        refine ⟨92550123447212593032162695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61700082298141728688108463 92550123447212593032162695)
        ·
          refine ⟨138825185170818889548244043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92550123447212593032162695 138825185170818889548244043)
          ·
            refine ⟨208237777756228334322366065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138825185170818889548244043 208237777756228334322366065)
            ·
              refine ⟨156178333317171250741774549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208237777756228334322366065 156178333317171250741774549)
              ·
                refine ⟨3660429687121201189260341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156178333317171250741774549 3660429687121201189260341)
                ·
                  refine ⟨343165283167612611493157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660429687121201189260341 343165283167612611493157)
                  ·
                    rfl

theorem cell22_3007404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_3007404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007404 prefixEnd_3007404 := by exact prefixLift 3007404
  have htrace : WordTrace (prefixWord ++ tailWord_3007404) baseStart_3007404 baseEnd_3007404 := by
    simpa [prefixWord, tailWord_3007404, baseEnd_3007404] using wordTrace_append hprefix tailTrace_3007404
  have hstable : (prefixWord ++ tailWord_3007404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007404).length < 2 ^ (prefixWord ++ tailWord_3007404).sum := by decide
  have hdescent : baseEnd_3007404 < baseStart_3007404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007442 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3007442 : Nat := 118140960795 + 3007442 * 2 ^ 59
def prefixEnd_3007442 : Nat := 4983230072969 + 3 ^ 40 * 3007442 * 2
def baseEnd_3007442 : Nat := 1029508857679418402029355

theorem tailTrace_3007442 : CollatzResearch.WordTrace tailWord_3007442 prefixEnd_3007442 1029508857679418402029355 := by
  unfold tailWord_3007442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422605292639684761630145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73126947447039159364347053 27422605292639684761630145)
  ·
    refine ⟨20566953969479763571222609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27422605292639684761630145 20566953969479763571222609)
    ·
      refine ⟨15425215477109822678416957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20566953969479763571222609 15425215477109822678416957)
      ·
        refine ⟨5784455803916183504406359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15425215477109822678416957 5784455803916183504406359)
        ·
          refine ⟨8676683705874275256609539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784455803916183504406359 8676683705874275256609539)
          ·
            refine ⟨13015025558811412884914309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676683705874275256609539 13015025558811412884914309)
            ·
              refine ⟨2440317292277139915921433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13015025558811412884914309 2440317292277139915921433)
              ·
                refine ⟨1830237969207854936941075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440317292277139915921433 1830237969207854936941075)
                ·
                  refine ⟨2745356953811782405411613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830237969207854936941075 2745356953811782405411613)
                  ·
                    refine ⟨1029508857679418402029355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745356953811782405411613 1029508857679418402029355)
                    ·
                      rfl

theorem cell22_3007442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3007442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007442 prefixEnd_3007442 := by exact prefixLift 3007442
  have htrace : WordTrace (prefixWord ++ tailWord_3007442) baseStart_3007442 baseEnd_3007442 := by
    simpa [prefixWord, tailWord_3007442, baseEnd_3007442] using wordTrace_append hprefix tailTrace_3007442
  have hstable : (prefixWord ++ tailWord_3007442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007442).length < 2 ^ (prefixWord ++ tailWord_3007442).sum := by decide
  have hdescent : baseEnd_3007442 < baseStart_3007442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007466 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_3007466 : Nat := 118140960795 + 3007466 * 2 ^ 59
def prefixEnd_3007466 : Nat := 4983230072969 + 3 ^ 40 * 3007466 * 2
def baseEnd_3007466 : Nat := 343172357789963446476427

theorem tailTrace_3007466 : CollatzResearch.WordTrace tailWord_3007466 prefixEnd_3007466 343172357789963446476427 := by
  unfold tailWord_3007466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422824130617947786348563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73127531014981194096929501 27422824130617947786348563)
  ·
    refine ⟨41134236195926921679522845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27422824130617947786348563 41134236195926921679522845)
    ·
      refine ⟨15425338573472595629821067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41134236195926921679522845 15425338573472595629821067)
      ·
        refine ⟨23138007860208893444731601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15425338573472595629821067 23138007860208893444731601)
        ·
          refine ⟨17353505895156670083548701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23138007860208893444731601 17353505895156670083548701)
          ·
            refine ⟨6507564710683751281330763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17353505895156670083548701 6507564710683751281330763)
            ·
              refine ⟨9761347066025626921996145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507564710683751281330763 9761347066025626921996145)
              ·
                refine ⟨7321010299519220191497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761347066025626921996145 7321010299519220191497109)
                ·
                  refine ⟨343172357789963446476427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7321010299519220191497109 343172357789963446476427)
                  ·
                    rfl

theorem cell22_3007466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_3007466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007466 prefixEnd_3007466 := by exact prefixLift 3007466
  have htrace : WordTrace (prefixWord ++ tailWord_3007466) baseStart_3007466 baseEnd_3007466 := by
    simpa [prefixWord, tailWord_3007466, baseEnd_3007466] using wordTrace_append hprefix tailTrace_3007466
  have hstable : (prefixWord ++ tailWord_3007466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007466).length < 2 ^ (prefixWord ++ tailWord_3007466).sum := by decide
  have hdescent : baseEnd_3007466 < baseStart_3007466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007481 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_3007481 : Nat := 118140960795 + 3007481 * 2 ^ 59
def prefixEnd_3007481 : Nat := 4983230072969 + 3 ^ 40 * 3007481 * 2
def baseEnd_3007481 : Nat := 1029522208176435300304235

theorem tailTrace_3007481 : CollatzResearch.WordTrace tailWord_3007481 prefixEnd_3007481 1029522208176435300304235 := by
  unfold tailWord_3007481
  simp only [CollatzResearch.WordTrace]
  refine ⟨109691843617417448707190297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73127895744944965804793531 109691843617417448707190297)
  ·
    refine ⟨82268882713063086530392723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109691843617417448707190297 82268882713063086530392723)
    ·
      refine ⟨123403324069594629795589085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82268882713063086530392723 123403324069594629795589085)
      ·
        refine ⟨46276246526097986173345907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123403324069594629795589085 46276246526097986173345907)
        ·
          refine ⟨69414369789146979260018861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46276246526097986173345907 69414369789146979260018861)
          ·
            refine ⟨26030388670930117222507073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69414369789146979260018861 26030388670930117222507073)
            ·
              refine ⟨19522791503197587916880305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26030388670930117222507073 19522791503197587916880305)
              ·
                refine ⟨14642093627398190937660229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19522791503197587916880305 14642093627398190937660229)
                ·
                  refine ⟨2745392555137160800811293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14642093627398190937660229 2745392555137160800811293)
                  ·
                    refine ⟨1029522208176435300304235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745392555137160800811293 1029522208176435300304235)
                    ·
                      rfl

theorem cell22_3007481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_3007481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007481 prefixEnd_3007481 := by exact prefixLift 3007481
  have htrace : WordTrace (prefixWord ++ tailWord_3007481) baseStart_3007481 baseEnd_3007481 := by
    simpa [prefixWord, tailWord_3007481, baseEnd_3007481] using wordTrace_append hprefix tailTrace_3007481
  have hstable : (prefixWord ++ tailWord_3007481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007481).length < 2 ^ (prefixWord ++ tailWord_3007481).sum := by decide
  have hdescent : baseEnd_3007481 < baseStart_3007481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007498 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_3007498 : Nat := 118140960795 + 3007498 * 2 ^ 59
def prefixEnd_3007498 : Nat := 4983230072969 + 3 ^ 40 * 3007498 * 2
def baseEnd_3007498 : Nat := 1029528027623852922629183

theorem tailTrace_3007498 : CollatzResearch.WordTrace tailWord_3007498 prefixEnd_3007498 1029528027623852922629183 := by
  unfold tailWord_3007498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423115914588965152639787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73128309105570573740372765 27423115914588965152639787)
  ·
    refine ⟨41134673871883447728959681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423115914588965152639787 41134673871883447728959681)
    ·
      refine ⟨30851005403912585796719761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41134673871883447728959681 30851005403912585796719761)
      ·
        refine ⟨23138254052934439347539821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30851005403912585796719761 23138254052934439347539821)
        ·
          refine ⟨8676845269850414755327433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23138254052934439347539821 8676845269850414755327433)
          ·
            refine ⟨6507633952387811066495575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8676845269850414755327433 6507633952387811066495575)
            ·
              refine ⟨9761450928581716599743363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507633952387811066495575 9761450928581716599743363)
              ·
                refine ⟨14642176392872574899615045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761450928581716599743363 14642176392872574899615045)
                ·
                  refine ⟨2745408073663607793677821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14642176392872574899615045 2745408073663607793677821)
                  ·
                    refine ⟨1029528027623852922629183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745408073663607793677821 1029528027623852922629183)
                    ·
                      rfl

theorem cell22_3007498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_3007498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007498 prefixEnd_3007498 := by exact prefixLift 3007498
  have htrace : WordTrace (prefixWord ++ tailWord_3007498) baseStart_3007498 baseEnd_3007498 := by
    simpa [prefixWord, tailWord_3007498, baseEnd_3007498] using wordTrace_append hprefix tailTrace_3007498
  have hstable : (prefixWord ++ tailWord_3007498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007498).length < 2 ^ (prefixWord ++ tailWord_3007498).sum := by decide
  have hdescent : baseEnd_3007498 < baseStart_3007498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007684 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3007684 : Nat := 118140960795 + 3007684 * 2 ^ 59
def prefixEnd_3007684 : Nat := 4983230072969 + 3 ^ 40 * 3007684 * 2
def baseEnd_3007684 : Nat := 1029591699225010437478613

theorem tailTrace_3007684 : CollatzResearch.WordTrace tailWord_3007684 prefixEnd_3007684 1029591699225010437478613 := by
  unfold tailWord_3007684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54849623817841007188415053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73132831757121342917886737 54849623817841007188415053)
  ·
    refine ⟨20568608931690377695655645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54849623817841007188415053 20568608931690377695655645)
    ·
      refine ⟨7713228349383891635870867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20568608931690377695655645 7713228349383891635870867)
      ·
        refine ⟨11569842524075837453806301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713228349383891635870867 11569842524075837453806301)
        ·
          refine ⟨4338690946528439045177363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11569842524075837453806301 4338690946528439045177363)
          ·
            refine ⟨6508036419792658567766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338690946528439045177363 6508036419792658567766045)
            ·
              refine ⟨2440513657422246962912267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508036419792658567766045 2440513657422246962912267)
              ·
                refine ⟨3660770486133370444368401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440513657422246962912267 3660770486133370444368401)
                ·
                  refine ⟨2745577864600027833276301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660770486133370444368401 2745577864600027833276301)
                  ·
                    refine ⟨1029591699225010437478613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745577864600027833276301 1029591699225010437478613)
                    ·
                      rfl

theorem cell22_3007684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3007684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007684 prefixEnd_3007684 := by exact prefixLift 3007684
  have htrace : WordTrace (prefixWord ++ tailWord_3007684) baseStart_3007684 baseEnd_3007684 := by
    simpa [prefixWord, tailWord_3007684, baseEnd_3007684] using wordTrace_append hprefix tailTrace_3007684
  have hstable : (prefixWord ++ tailWord_3007684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007684).length < 2 ^ (prefixWord ++ tailWord_3007684).sum := by decide
  have hdescent : baseEnd_3007684 < baseStart_3007684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007712 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_3007712 : Nat := 118140960795 + 3007712 * 2 ^ 59
def prefixEnd_3007712 : Nat := 4983230072969 + 3 ^ 40 * 3007712 * 2
def baseEnd_3007712 : Nat := 1029601284197227697778527

theorem tailTrace_3007712 : CollatzResearch.WordTrace tailWord_3007712 prefixEnd_3007712 1029601284197227697778527 := by
  unfold tailWord_3007712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54850134439790287579424695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73133512586387050105899593 54850134439790287579424695)
  ·
    refine ⟨82275201659685431369137043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54850134439790287579424695 82275201659685431369137043)
    ·
      refine ⟨123412802489528147053705565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82275201659685431369137043 123412802489528147053705565)
      ·
        refine ⟨46279800933573055145139587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123412802489528147053705565 46279800933573055145139587)
        ·
          refine ⟨69419701400359582717709381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46279800933573055145139587 69419701400359582717709381)
          ·
            refine ⟨13016194012567421759570509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69419701400359582717709381 13016194012567421759570509)
            ·
              refine ⟨4881072754712783159838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13016194012567421759570509 4881072754712783159838941)
              ·
                refine ⟨1830402283017293684939603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4881072754712783159838941 1830402283017293684939603)
                ·
                  refine ⟨2745603424525940527409405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830402283017293684939603 2745603424525940527409405)
                  ·
                    refine ⟨1029601284197227697778527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745603424525940527409405 1029601284197227697778527)
                    ·
                      rfl

theorem cell22_3007712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_3007712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007712 prefixEnd_3007712 := by exact prefixLift 3007712
  have htrace : WordTrace (prefixWord ++ tailWord_3007712) baseStart_3007712 baseEnd_3007712 := by
    simpa [prefixWord, tailWord_3007712, baseEnd_3007712] using wordTrace_append hprefix tailTrace_3007712
  have hstable : (prefixWord ++ tailWord_3007712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007712).length < 2 ^ (prefixWord ++ tailWord_3007712).sum := by decide
  have hdescent : baseEnd_3007712 < baseStart_3007712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007738 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_3007738 : Nat := 118140960795 + 3007738 * 2 ^ 59
def prefixEnd_3007738 : Nat := 4983230072969 + 3 ^ 40 * 3007738 * 2
def baseEnd_3007738 : Nat := 1029610184528572296628447

theorem tailTrace_3007738 : CollatzResearch.WordTrace tailWord_3007738 prefixEnd_3007738 1029610184528572296628447 := by
  unfold tailWord_3007738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27425304294371595399823967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73134144784990921066197245 27425304294371595399823967)
  ·
    refine ⟨41137956441557393099735951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27425304294371595399823967 41137956441557393099735951)
    ·
      refine ⟨61706934662336089649603927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41137956441557393099735951 61706934662336089649603927)
      ·
        refine ⟨92560401993504134474405891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61706934662336089649603927 92560401993504134474405891)
        ·
          refine ⟨138840602990256201711608837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92560401993504134474405891 138840602990256201711608837)
          ·
            refine ⟨26032613060673037820926657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138840602990256201711608837 26032613060673037820926657)
            ·
              refine ⟨19524459795504778365694993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26032613060673037820926657 19524459795504778365694993)
              ·
                refine ⟨14643344846628583774271245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19524459795504778365694993 14643344846628583774271245)
                ·
                  refine ⟨5491254317485718915351717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14643344846628583774271245 5491254317485718915351717)
                  ·
                    refine ⟨1029610184528572296628447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491254317485718915351717 1029610184528572296628447)
                    ·
                      rfl

theorem cell22_3007738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_3007738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007738 prefixEnd_3007738 := by exact prefixLift 3007738
  have htrace : WordTrace (prefixWord ++ tailWord_3007738) baseStart_3007738 baseEnd_3007738 := by
    simpa [prefixWord, tailWord_3007738, baseEnd_3007738] using wordTrace_append hprefix tailTrace_3007738
  have hstable : (prefixWord ++ tailWord_3007738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007738).length < 2 ^ (prefixWord ++ tailWord_3007738).sum := by decide
  have hdescent : baseEnd_3007738 < baseStart_3007738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007742 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3007742 : Nat := 118140960795 + 3007742 * 2 ^ 59
def prefixEnd_3007742 : Nat := 4983230072969 + 3 ^ 40 * 3007742 * 2
def baseEnd_3007742 : Nat := 343203851270105873176145

theorem tailTrace_3007742 : CollatzResearch.WordTrace tailWord_3007742 prefixEnd_3007742 343203851270105873176145 := by
  unfold tailWord_3007742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712670383683986285305185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73134242046314593521627653 13712670383683986285305185)
  ·
    refine ⟨10284502787762989713978889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13712670383683986285305185 10284502787762989713978889)
    ·
      refine ⟨7713377090822242285484167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10284502787762989713978889 7713377090822242285484167)
      ·
        refine ⟨11570065636233363428226251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713377090822242285484167 11570065636233363428226251)
        ·
          refine ⟨17355098454350045142339377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570065636233363428226251 17355098454350045142339377)
          ·
            refine ⟨13016323840762533856754533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17355098454350045142339377 13016323840762533856754533)
            ·
              refine ⟨2440560720142975098141475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13016323840762533856754533 2440560720142975098141475)
              ·
                refine ⟨3660841080214462647212213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440560720142975098141475 3660841080214462647212213)
                ·
                  refine ⟨343203851270105873176145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660841080214462647212213 343203851270105873176145)
                  ·
                    rfl

theorem cell22_3007742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3007742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007742 prefixEnd_3007742 := by exact prefixLift 3007742
  have htrace : WordTrace (prefixWord ++ tailWord_3007742) baseStart_3007742 baseEnd_3007742 := by
    simpa [prefixWord, tailWord_3007742, baseEnd_3007742] using wordTrace_append hprefix tailTrace_3007742
  have hstable : (prefixWord ++ tailWord_3007742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007742).length < 2 ^ (prefixWord ++ tailWord_3007742).sum := by decide
  have hdescent : baseEnd_3007742 < baseStart_3007742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007755 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 1, 4]
def baseStart_3007755 : Nat := 118140960795 + 3007755 * 2 ^ 59
def prefixEnd_3007755 : Nat := 4983230072969 + 3 ^ 40 * 3007755 * 2
def baseEnd_3007755 : Nat := 1029616003975989918953395

theorem tailTrace_3007755 : CollatzResearch.WordTrace tailWord_3007755 prefixEnd_3007755 1029616003975989918953395 := by
  unfold tailWord_3007755
  simp only [CollatzResearch.WordTrace]
  refine ⟨109701837218424793502664719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73134558145616529001776479 109701837218424793502664719)
  ·
    refine ⟨164552755827637190253997079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109701837218424793502664719 164552755827637190253997079)
    ·
      refine ⟨246829133741455785380995619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164552755827637190253997079 246829133741455785380995619)
      ·
        refine ⟨370243700612183678071493429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246829133741455785380995619 370243700612183678071493429)
        ·
          refine ⟨34710346932392219819202509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370243700612183678071493429 34710346932392219819202509)
          ·
            refine ⟨13016380099647082432200941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34710346932392219819202509 13016380099647082432200941)
            ·
              refine ⟨4881142537367655912075353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13016380099647082432200941 4881142537367655912075353)
              ·
                refine ⟨3660856903025741934056515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881142537367655912075353 3660856903025741934056515)
                ·
                  refine ⟨5491285354538612901084773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660856903025741934056515 5491285354538612901084773)
                  ·
                    refine ⟨1029616003975989918953395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491285354538612901084773 1029616003975989918953395)
                    ·
                      rfl

theorem cell22_3007755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_3007755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007755 prefixEnd_3007755 := by exact prefixLift 3007755
  have htrace : WordTrace (prefixWord ++ tailWord_3007755) baseStart_3007755 baseEnd_3007755 := by
    simpa [prefixWord, tailWord_3007755, baseEnd_3007755] using wordTrace_append hprefix tailTrace_3007755
  have hstable : (prefixWord ++ tailWord_3007755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007755).length < 2 ^ (prefixWord ++ tailWord_3007755).sum := by decide
  have hdescent : baseEnd_3007755 < baseStart_3007755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007768 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_3007768 : Nat := 118140960795 + 3007768 * 2 ^ 59
def prefixEnd_3007768 : Nat := 4983230072969 + 3 ^ 40 * 3007768 * 2
def baseEnd_3007768 : Nat := 1029620454141662218378355

theorem tailTrace_3007768 : CollatzResearch.WordTrace tailWord_3007768 prefixEnd_3007768 1029620454141662218378355 := by
  unfold tailWord_3007768
  simp only [CollatzResearch.WordTrace]
  refine ⟨54851155683688848361443979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73134874244918464481925305 54851155683688848361443979)
  ·
    refine ⟨82276733525533272542165969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54851155683688848361443979 82276733525533272542165969)
    ·
      refine ⟨61707550144149954406624477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82276733525533272542165969 61707550144149954406624477)
      ·
        refine ⟨23140331304056232902484179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61707550144149954406624477 23140331304056232902484179)
        ·
          refine ⟨34710496956084349353726269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23140331304056232902484179 34710496956084349353726269)
          ·
            refine ⟨13016436358531631007647351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34710496956084349353726269 13016436358531631007647351)
            ·
              refine ⟨19524654537797446511471027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13016436358531631007647351 19524654537797446511471027)
              ·
                refine ⟨29286981806696169767206541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19524654537797446511471027 29286981806696169767206541)
                ·
                  refine ⟨10982618177511063662702453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29286981806696169767206541 10982618177511063662702453)
                  ·
                    refine ⟨1029620454141662218378355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10982618177511063662702453 1029620454141662218378355)
                    ·
                      rfl

theorem cell22_3007768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_3007768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007768 prefixEnd_3007768 := by exact prefixLift 3007768
  have htrace : WordTrace (prefixWord ++ tailWord_3007768) baseStart_3007768 baseEnd_3007768 := by
    simpa [prefixWord, tailWord_3007768, baseEnd_3007768] using wordTrace_append hprefix tailTrace_3007768
  have hstable : (prefixWord ++ tailWord_3007768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007768).length < 2 ^ (prefixWord ++ tailWord_3007768).sum := by decide
  have hdescent : baseEnd_3007768 < baseStart_3007768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007815 : List Nat := [1, 1, 4, 1, 2, 4, 3, 6]
def baseStart_3007815 : Nat := 118140960795 + 3007815 * 2 ^ 59
def prefixEnd_3007815 : Nat := 4983230072969 + 3 ^ 40 * 3007815 * 2
def baseEnd_3007815 : Nat := 114404060355796640272579

theorem tailTrace_3007815 : CollatzResearch.WordTrace tailWord_3007815 prefixEnd_3007815 114404060355796640272579 := by
  unfold tailWord_3007815
  simp only [CollatzResearch.WordTrace]
  refine ⟨109704025598207423749848899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73136017065471615833232599 109704025598207423749848899)
  ·
    refine ⟨164556038397311135624773349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109704025598207423749848899 164556038397311135624773349)
    ·
      refine ⟨30854257199495837929645003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164556038397311135624773349 30854257199495837929645003)
      ·
        refine ⟨46281385799243756894467505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30854257199495837929645003 46281385799243756894467505)
        ·
          refine ⟨34711039349432817670850629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46281385799243756894467505 34711039349432817670850629)
          ·
            refine ⟨6508319878018653313284493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34711039349432817670850629 6508319878018653313284493)
            ·
              refine ⟨2440619954256994992481685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508319878018653313284493 2440619954256994992481685)
              ·
                refine ⟨114404060355796640272579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2440619954256994992481685 114404060355796640272579)
                ·
                  rfl

theorem cell22_3007815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 6].length) (baseStart_3007815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007815 prefixEnd_3007815 := by exact prefixLift 3007815
  have htrace : WordTrace (prefixWord ++ tailWord_3007815) baseStart_3007815 baseEnd_3007815 := by
    simpa [prefixWord, tailWord_3007815, baseEnd_3007815] using wordTrace_append hprefix tailTrace_3007815
  have hstable : (prefixWord ++ tailWord_3007815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007815).length < 2 ^ (prefixWord ++ tailWord_3007815).sum := by decide
  have hdescent : baseEnd_3007815 < baseStart_3007815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007821 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3007821 : Nat := 118140960795 + 3007821 * 2 ^ 59
def prefixEnd_3007821 : Nat := 4983230072969 + 3 ^ 40 * 3007821 * 2
def baseEnd_3007821 : Nat := 343212865708262582267731

theorem tailTrace_3007821 : CollatzResearch.WordTrace tailWord_3007821 prefixEnd_3007821 343212865708262582267731 := by
  unfold tailWord_3007821
  simp only [CollatzResearch.WordTrace]
  refine ⟨109704244436185686774567317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73136162957457124516378211 109704244436185686774567317)
  ·
    refine ⟨5142386457946204067557843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109704244436185686774567317 5142386457946204067557843)
    ·
      refine ⟨7713579686919306101336765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142386457946204067557843 7713579686919306101336765)
      ·
        refine ⟨2892592382594739788001287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7713579686919306101336765 2892592382594739788001287)
        ·
          refine ⟨4338888573892109682001931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892592382594739788001287 4338888573892109682001931)
          ·
            refine ⟨6508332860838164523002897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338888573892109682001931 6508332860838164523002897)
            ·
              refine ⟨4881249645628623392252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508332860838164523002897 4881249645628623392252173)
              ·
                refine ⟨1830468617110733772094565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4881249645628623392252173 1830468617110733772094565)
                ·
                  refine ⟨343212865708262582267731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830468617110733772094565 343212865708262582267731)
                  ·
                    rfl

theorem cell22_3007821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3007821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007821 prefixEnd_3007821 := by exact prefixLift 3007821
  have htrace : WordTrace (prefixWord ++ tailWord_3007821) baseStart_3007821 baseEnd_3007821 := by
    simpa [prefixWord, tailWord_3007821, baseEnd_3007821] using wordTrace_append hprefix tailTrace_3007821
  have hstable : (prefixWord ++ tailWord_3007821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007821).length < 2 ^ (prefixWord ++ tailWord_3007821).sum := by decide
  have hdescent : baseEnd_3007821 < baseStart_3007821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007881 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_3007881 : Nat := 118140960795 + 3007881 * 2 ^ 59
def prefixEnd_3007881 : Nat := 4983230072969 + 3 ^ 40 * 3007881 * 2
def baseEnd_3007881 : Nat := 1029659136350967590303009

theorem tailTrace_3007881 : CollatzResearch.WordTrace tailWord_3007881 prefixEnd_3007881 1029659136350967590303009 := by
  unfold tailWord_3007881
  simp only [CollatzResearch.WordTrace]
  refine ⟨109706432815968317021751497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73137621877312211347834331 109706432815968317021751497)
  ·
    refine ⟨82279824611976237766313623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109706432815968317021751497 82279824611976237766313623)
    ·
      refine ⟨123419736917964356649470435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82279824611976237766313623 123419736917964356649470435)
      ·
        refine ⟨185129605376946534974205653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123419736917964356649470435 185129605376946534974205653)
        ·
          refine ⟨4338975126022184413457945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 185129605376946534974205653 4338975126022184413457945)
          ·
            refine ⟨3254231344516638310093459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338975126022184413457945 3254231344516638310093459)
            ·
              refine ⟨4881347016774957465140189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254231344516638310093459 4881347016774957465140189)
              ·
                refine ⟨1830505131290609049427571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4881347016774957465140189 1830505131290609049427571)
                ·
                  refine ⟨2745757696935913574141357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830505131290609049427571 2745757696935913574141357)
                  ·
                    refine ⟨1029659136350967590303009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745757696935913574141357 1029659136350967590303009)
                    ·
                      rfl

theorem cell22_3007881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_3007881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007881 prefixEnd_3007881 := by exact prefixLift 3007881
  have htrace : WordTrace (prefixWord ++ tailWord_3007881) baseStart_3007881 baseEnd_3007881 := by
    simpa [prefixWord, tailWord_3007881, baseEnd_3007881] using wordTrace_append hprefix tailTrace_3007881
  have hstable : (prefixWord ++ tailWord_3007881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007881).length < 2 ^ (prefixWord ++ tailWord_3007881).sum := by decide
  have hdescent : baseEnd_3007881 < baseStart_3007881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007920 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_3007920 : Nat := 118140960795 + 3007920 * 2 ^ 59
def prefixEnd_3007920 : Nat := 4983230072969 + 3 ^ 40 * 3007920 * 2
def baseEnd_3007920 : Nat := 1029672486847984488577889

theorem tailTrace_3007920 : CollatzResearch.WordTrace tailWord_3007920 prefixEnd_3007920 1029672486847984488577889 := by
  unfold tailWord_3007920
  simp only [CollatzResearch.WordTrace]
  refine ⟨54853927631413513341210607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73138570175218017788280809 54853927631413513341210607)
  ·
    refine ⟨82280891447120270011815911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54853927631413513341210607 82280891447120270011815911)
    ·
      refine ⟨123421337170680405017723867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82280891447120270011815911 123421337170680405017723867)
      ·
        refine ⟨185132005756020607526585801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123421337170680405017723867 185132005756020607526585801)
        ·
          refine ⟨138849004317015455644939351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185132005756020607526585801 138849004317015455644939351)
          ·
            refine ⟨208273506475523183467409027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138849004317015455644939351 208273506475523183467409027)
            ·
              refine ⟨312410259713284775201113541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208273506475523183467409027 312410259713284775201113541)
              ·
                refine ⟨58576923696240895350208789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312410259713284775201113541 58576923696240895350208789)
                ·
                  refine ⟨2745793298261291969541037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58576923696240895350208789 2745793298261291969541037)
                  ·
                    refine ⟨1029672486847984488577889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745793298261291969541037 1029672486847984488577889)
                    ·
                      rfl

theorem cell22_3007920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_3007920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3007920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3007920 prefixEnd_3007920 := by exact prefixLift 3007920
  have htrace : WordTrace (prefixWord ++ tailWord_3007920) baseStart_3007920 baseEnd_3007920 := by
    simpa [prefixWord, tailWord_3007920, baseEnd_3007920] using wordTrace_append hprefix tailTrace_3007920
  have hstable : (prefixWord ++ tailWord_3007920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007920).length < 2 ^ (prefixWord ++ tailWord_3007920).sum := by decide
  have hdescent : baseEnd_3007920 < baseStart_3007920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008012 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_3008012 : Nat := 118140960795 + 3008012 * 2 ^ 59
def prefixEnd_3008012 : Nat := 4983230072969 + 3 ^ 40 * 3008012 * 2
def baseEnd_3008012 : Nat := 343234660109375638425869

theorem tailTrace_3008012 : CollatzResearch.WordTrace tailWord_3008012 prefixEnd_3008012 343234660109375638425869 := by
  unfold tailWord_3008012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855605389246863197385145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73140807185662484263180193 54855605389246863197385145)
  ·
    refine ⟨41141704041935147398038859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54855605389246863197385145 41141704041935147398038859)
    ·
      refine ⟨61712556062902721097058289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41141704041935147398038859 61712556062902721097058289)
      ·
        refine ⟨46284417047177040822793717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61712556062902721097058289 46284417047177040822793717)
        ·
          refine ⟨4339164098172847577136911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46284417047177040822793717 4339164098172847577136911)
          ·
            refine ⟨6508746147259271365705367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339164098172847577136911 6508746147259271365705367)
            ·
              refine ⟨9763119220888907048558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508746147259271365705367 9763119220888907048558051)
              ·
                refine ⟨14644678831333360572837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9763119220888907048558051 14644678831333360572837077)
                ·
                  refine ⟨343234660109375638425869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14644678831333360572837077 343234660109375638425869)
                  ·
                    rfl

theorem cell22_3008012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_3008012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008012 prefixEnd_3008012 := by exact prefixLift 3008012
  have htrace : WordTrace (prefixWord ++ tailWord_3008012) baseStart_3008012 baseEnd_3008012 := by
    simpa [prefixWord, tailWord_3008012, baseEnd_3008012] using wordTrace_append hprefix tailTrace_3008012
  have hstable : (prefixWord ++ tailWord_3008012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008012).length < 2 ^ (prefixWord ++ tailWord_3008012).sum := by decide
  have hdescent : baseEnd_3008012 < baseStart_3008012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008029 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 5]
def baseStart_3008029 : Nat := 118140960795 + 3008029 * 2 ^ 59
def prefixEnd_3008029 : Nat := 4983230072969 + 3 ^ 40 * 3008029 * 2
def baseEnd_3008029 : Nat := 343236599925181512534185

theorem tailTrace_3008029 : CollatzResearch.WordTrace tailWord_3008029 prefixEnd_3008029 343236599925181512534185 := by
  unfold tailWord_3008029
  simp only [CollatzResearch.WordTrace]
  refine ⟨109711830819432138298139141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73141220546288092198759427 109711830819432138298139141)
  ·
    refine ⟨20570968278643525930901089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109711830819432138298139141 20570968278643525930901089)
    ·
      refine ⟨15428226208982644448175817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20570968278643525930901089 15428226208982644448175817)
      ·
        refine ⟨11571169656736983336131863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15428226208982644448175817 11571169656736983336131863)
        ·
          refine ⟨17356754485105475004197795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571169656736983336131863 17356754485105475004197795)
          ·
            refine ⟨26035131727658212506296693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356754485105475004197795 26035131727658212506296693)
            ·
              refine ⟨2440793599467957422465315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26035131727658212506296693 2440793599467957422465315)
              ·
                refine ⟨3661190399201936133697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440793599467957422465315 3661190399201936133697973)
                ·
                  refine ⟨343236599925181512534185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3661190399201936133697973 343236599925181512534185)
                  ·
                    rfl

theorem cell22_3008029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_3008029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008029 prefixEnd_3008029 := by exact prefixLift 3008029
  have htrace : WordTrace (prefixWord ++ tailWord_3008029) baseStart_3008029 baseEnd_3008029 := by
    simpa [prefixWord, tailWord_3008029, baseEnd_3008029] using wordTrace_append hprefix tailTrace_3008029
  have hstable : (prefixWord ++ tailWord_3008029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008029).length < 2 ^ (prefixWord ++ tailWord_3008029).sum := by decide
  have hdescent : baseEnd_3008029 < baseStart_3008029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008104 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3008104 : Nat := 118140960795 + 3008104 * 2 ^ 59
def prefixEnd_3008104 : Nat := 4983230072969 + 3 ^ 40 * 3008104 * 2
def baseEnd_3008104 : Nat := 1029735473808269341977325

theorem tailTrace_3008104 : CollatzResearch.WordTrace tailWord_3008104 prefixEnd_3008104 1029735473808269341977325 := by
  unfold tailWord_3008104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54857283147080213053559683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73143044196106950738079577 54857283147080213053559683)
  ·
    refine ⟨82285924720620319580339525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54857283147080213053559683 82285924720620319580339525)
    ·
      refine ⟨15428610885116309921313661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82285924720620319580339525 15428610885116309921313661)
      ·
        refine ⟨5785729081918616220492623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15428610885116309921313661 5785729081918616220492623)
        ·
          refine ⟨8678593622877924330738935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785729081918616220492623 8678593622877924330738935)
          ·
            refine ⟨13017890434316886496108403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8678593622877924330738935 13017890434316886496108403)
            ·
              refine ⟨19526835651475329744162605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017890434316886496108403 19526835651475329744162605)
              ·
                refine ⟨7322563369303248654060977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19526835651475329744162605 7322563369303248654060977)
                ·
                  refine ⟨5491922526977436490545733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322563369303248654060977 5491922526977436490545733)
                  ·
                    refine ⟨1029735473808269341977325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491922526977436490545733 1029735473808269341977325)
                    ·
                      rfl

theorem cell22_3008104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3008104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008104 prefixEnd_3008104 := by exact prefixLift 3008104
  have htrace : WordTrace (prefixWord ++ tailWord_3008104) baseStart_3008104 baseEnd_3008104 := by
    simpa [prefixWord, tailWord_3008104, baseEnd_3008104] using wordTrace_append hprefix tailTrace_3008104
  have hstable : (prefixWord ++ tailWord_3008104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008104).length < 2 ^ (prefixWord ++ tailWord_3008104).sum := by decide
  have hdescent : baseEnd_3008104 < baseStart_3008104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008136 : List Nat := [2, 1, 3, 5, 1, 2, 1, 7]
def baseStart_3008136 : Nat := 118140960795 + 3008136 * 2 ^ 59
def prefixEnd_3008136 : Nat := 4983230072969 + 3 ^ 40 * 3008136 * 2
def baseEnd_3008136 : Nat := 114416269784692436130803

theorem tailTrace_3008136 : CollatzResearch.WordTrace tailWord_3008136 prefixEnd_3008136 114416269784692436130803 := by
  unfold tailWord_3008136
  simp only [CollatzResearch.WordTrace]
  refine ⟨54857866715022247786142131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73143822286696330381522841 54857866715022247786142131)
  ·
    refine ⟨82286800072533371679213197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54857866715022247786142131 82286800072533371679213197)
    ·
      refine ⟨30857550027200014379704949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82286800072533371679213197 30857550027200014379704949)
      ·
        refine ⟨2892895315050001348097339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30857550027200014379704949 2892895315050001348097339)
        ·
          refine ⟨4339342972575002022146009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892895315050001348097339 4339342972575002022146009)
          ·
            refine ⟨3254507229431251516609507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339342972575002022146009 3254507229431251516609507)
            ·
              refine ⟨4881760844146877274914261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254507229431251516609507 4881760844146877274914261)
              ·
                refine ⟨114416269784692436130803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4881760844146877274914261 114416269784692436130803)
                ·
                  rfl

theorem cell22_3008136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_3008136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008136 prefixEnd_3008136 := by exact prefixLift 3008136
  have htrace : WordTrace (prefixWord ++ tailWord_3008136) baseStart_3008136 baseEnd_3008136 := by
    simpa [prefixWord, tailWord_3008136, baseEnd_3008136] using wordTrace_append hprefix tailTrace_3008136
  have hstable : (prefixWord ++ tailWord_3008136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008136).length < 2 ^ (prefixWord ++ tailWord_3008136).sum := by decide
  have hdescent : baseEnd_3008136 < baseStart_3008136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008224 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_3008224 : Nat := 118140960795 + 3008224 * 2 ^ 59
def prefixEnd_3008224 : Nat := 4983230072969 + 3 ^ 40 * 3008224 * 2
def baseEnd_3008224 : Nat := 1029776552260629028976957

theorem tailTrace_3008224 : CollatzResearch.WordTrace tailWord_3008224 prefixEnd_3008224 1029776552260629028976957 := by
  unfold tailWord_3008224
  simp only [CollatzResearch.WordTrace]
  refine ⟨54859471526862843300743863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73145962035817124400991817 54859471526862843300743863)
  ·
    refine ⟨82289207290294264951115795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54859471526862843300743863 82289207290294264951115795)
    ·
      refine ⟨123433810935441397426673693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82289207290294264951115795 123433810935441397426673693)
      ·
        refine ⟨46287679100790524035002635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123433810935441397426673693 46287679100790524035002635)
        ·
          refine ⟨69431518651185786052503953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46287679100790524035002635 69431518651185786052503953)
          ·
            refine ⟨52073638988389339539377965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69431518651185786052503953 52073638988389339539377965)
            ·
              refine ⟨19527614620646002327266737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52073638988389339539377965 19527614620646002327266737)
              ·
                refine ⟨14645710965484501745450053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19527614620646002327266737 14645710965484501745450053)
                ·
                  refine ⟨2746070806028344077271885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14645710965484501745450053 2746070806028344077271885)
                  ·
                    refine ⟨1029776552260629028976957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746070806028344077271885 1029776552260629028976957)
                    ·
                      rfl

theorem cell22_3008224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_3008224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008224 prefixEnd_3008224 := by exact prefixLift 3008224
  have htrace : WordTrace (prefixWord ++ tailWord_3008224) baseStart_3008224 baseEnd_3008224 := by
    simpa [prefixWord, tailWord_3008224, baseEnd_3008224] using wordTrace_append hprefix tailTrace_3008224
  have hstable : (prefixWord ++ tailWord_3008224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008224).length < 2 ^ (prefixWord ++ tailWord_3008224).sum := by decide
  have hdescent : baseEnd_3008224 < baseStart_3008224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008239 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3008239 : Nat := 118140960795 + 3008239 * 2 ^ 59
def prefixEnd_3008239 : Nat := 4983230072969 + 3 ^ 40 * 3008239 * 2
def baseEnd_3008239 : Nat := 1029781687067173989851911

theorem tailTrace_3008239 : CollatzResearch.WordTrace tailWord_3008239 prefixEnd_3008239 1029781687067173989851911 := by
  unfold tailWord_3008239
  simp only [CollatzResearch.WordTrace]
  refine ⟨109719490148671344163283771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73146326765780896108855847 109719490148671344163283771)
  ·
    refine ⟨164579235223007016244925657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109719490148671344163283771 164579235223007016244925657)
    ·
      refine ⟨123434426417255262183694243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164579235223007016244925657 123434426417255262183694243)
      ·
        refine ⟨185151639625882893275541365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123434426417255262183694243 185151639625882893275541365)
        ·
          refine ⟨17357966214926521244582003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185151639625882893275541365 17357966214926521244582003)
          ·
            refine ⟨26036949322389781866873005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17357966214926521244582003 26036949322389781866873005)
            ·
              refine ⟨9763855995896168200077377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26036949322389781866873005 9763855995896168200077377)
              ·
                refine ⟨7322891996922126150058033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9763855995896168200077377 7322891996922126150058033)
                ·
                  refine ⟨5492168997691594612543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322891996922126150058033 5492168997691594612543525)
                  ·
                    refine ⟨1029781687067173989851911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492168997691594612543525 1029781687067173989851911)
                    ·
                      rfl

theorem cell22_3008239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3008239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008239 prefixEnd_3008239 := by exact prefixLift 3008239
  have htrace : WordTrace (prefixWord ++ tailWord_3008239) baseStart_3008239 baseEnd_3008239 := by
    simpa [prefixWord, tailWord_3008239, baseEnd_3008239] using wordTrace_append hprefix tailTrace_3008239
  have hstable : (prefixWord ++ tailWord_3008239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008239).length < 2 ^ (prefixWord ++ tailWord_3008239).sum := by decide
  have hdescent : baseEnd_3008239 < baseStart_3008239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008258 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3008258 : Nat := 118140960795 + 3008258 * 2 ^ 59
def prefixEnd_3008258 : Nat := 4983230072969 + 3 ^ 40 * 3008258 * 2
def baseEnd_3008258 : Nat := 1029788191155464273626853

theorem tailTrace_3008258 : CollatzResearch.WordTrace tailWord_3008258 prefixEnd_3008258 1029788191155464273626853 := by
  unfold tailWord_3008258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430045783900627602056357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73146788757068340272150285 27430045783900627602056357)
  ·
    refine ⟨5143133584481367675385567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27430045783900627602056357 5143133584481367675385567)
    ·
      refine ⟨7714700376722051513078351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143133584481367675385567 7714700376722051513078351)
      ·
        refine ⟨11572050565083077269617527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714700376722051513078351 11572050565083077269617527)
        ·
          refine ⟨17358075847624615904426291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572050565083077269617527 17358075847624615904426291)
          ·
            refine ⟨26037113771436923856639437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17358075847624615904426291 26037113771436923856639437)
            ·
              refine ⟨9763917664288846446239789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26037113771436923856639437 9763917664288846446239789)
              ·
                refine ⟨3661469124108317417339921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9763917664288846446239789 3661469124108317417339921)
                ·
                  refine ⟨2746101843081238063004941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661469124108317417339921 2746101843081238063004941)
                  ·
                    refine ⟨1029788191155464273626853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746101843081238063004941 1029788191155464273626853)
                    ·
                      rfl

theorem cell22_3008258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3008258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008258 prefixEnd_3008258 := by exact prefixLift 3008258
  have htrace : WordTrace (prefixWord ++ tailWord_3008258) baseStart_3008258 baseEnd_3008258 := by
    simpa [prefixWord, tailWord_3008258, baseEnd_3008258] using wordTrace_append hprefix tailTrace_3008258
  have hstable : (prefixWord ++ tailWord_3008258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008258).length < 2 ^ (prefixWord ++ tailWord_3008258).sum := by decide
  have hdescent : baseEnd_3008258 < baseStart_3008258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008314 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_3008314 : Nat := 118140960795 + 3008314 * 2 ^ 59
def prefixEnd_3008314 : Nat := 4983230072969 + 3 ^ 40 * 3008314 * 2
def baseEnd_3008314 : Nat := 1029807361099898794226681

theorem tailTrace_3008314 : CollatzResearch.WordTrace tailWord_3008314 prefixEnd_3008314 1029807361099898794226681 := by
  unfold tailWord_3008314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430556405849907993065999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73148150415599754648175997 27430556405849907993065999)
  ·
    refine ⟨41145834608774861989598999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27430556405849907993065999 41145834608774861989598999)
    ·
      refine ⟨61718751913162292984398499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41145834608774861989598999 61718751913162292984398499)
      ·
        refine ⟨92578127869743439476597749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61718751913162292984398499 92578127869743439476597749)
        ·
          refine ⟨8679199487788447450931039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92578127869743439476597749 8679199487788447450931039)
          ·
            refine ⟨13018799231682671176396559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8679199487788447450931039 13018799231682671176396559)
            ·
              refine ⟨19528198847524006764594839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13018799231682671176396559 19528198847524006764594839)
              ·
                refine ⟨29292298271286010146892259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19528198847524006764594839 29292298271286010146892259)
                ·
                  refine ⟨43938447406929015220338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29292298271286010146892259 43938447406929015220338389)
                  ·
                    refine ⟨1029807361099898794226681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43938447406929015220338389 1029807361099898794226681)
                    ·
                      rfl

theorem cell22_3008314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_3008314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008314 prefixEnd_3008314 := by exact prefixLift 3008314
  have htrace : WordTrace (prefixWord ++ tailWord_3008314) baseStart_3008314 baseEnd_3008314 := by
    simpa [prefixWord, tailWord_3008314, baseEnd_3008314] using wordTrace_append hprefix tailTrace_3008314
  have hstable : (prefixWord ++ tailWord_3008314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008314).length < 2 ^ (prefixWord ++ tailWord_3008314).sum := by decide
  have hdescent : baseEnd_3008314 < baseStart_3008314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008329 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_3008329 : Nat := 118140960795 + 3008329 * 2 ^ 59
def prefixEnd_3008329 : Nat := 4983230072969 + 3 ^ 40 * 3008329 * 2
def baseEnd_3008329 : Nat := 1029812495906443755101635

theorem tailTrace_3008329 : CollatzResearch.WordTrace tailWord_3008329 prefixEnd_3008329 1029812495906443755101635 := by
  unfold tailWord_3008329
  simp only [CollatzResearch.WordTrace]
  refine ⟨109722772718345289534060041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73148515145563526356040027 109722772718345289534060041)
  ·
    refine ⟨82292079538758967150545031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109722772718345289534060041 82292079538758967150545031)
    ·
      refine ⟨123438119308138450725817547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82292079538758967150545031 123438119308138450725817547)
      ·
        refine ⟨185157178962207676088726321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123438119308138450725817547 185157178962207676088726321)
        ·
          refine ⟨138867884221655757066544741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185157178962207676088726321 138867884221655757066544741)
          ·
            refine ⟨26037728291560454449977139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138867884221655757066544741 26037728291560454449977139)
            ·
              refine ⟨39056592437340681674965709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26037728291560454449977139 39056592437340681674965709)
              ·
                refine ⟨14646222164002755628112141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39056592437340681674965709 14646222164002755628112141)
                ·
                  refine ⟨5492333311501033360542053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14646222164002755628112141 5492333311501033360542053)
                  ·
                    refine ⟨1029812495906443755101635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492333311501033360542053 1029812495906443755101635)
                    ·
                      rfl

theorem cell22_3008329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_3008329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008329 prefixEnd_3008329 := by exact prefixLift 3008329
  have htrace : WordTrace (prefixWord ++ tailWord_3008329) baseStart_3008329 baseEnd_3008329 := by
    simpa [prefixWord, tailWord_3008329, baseEnd_3008329] using wordTrace_append hprefix tailTrace_3008329
  have hstable : (prefixWord ++ tailWord_3008329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008329).length < 2 ^ (prefixWord ++ tailWord_3008329).sum := by decide
  have hdescent : baseEnd_3008329 < baseStart_3008329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008346 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_3008346 : Nat := 118140960795 + 3008346 * 2 ^ 59
def prefixEnd_3008346 : Nat := 4983230072969 + 3 ^ 40 * 3008346 * 2
def baseEnd_3008346 : Nat := 1029818315353861377426583

theorem tailTrace_3008346 : CollatzResearch.WordTrace tailWord_3008346 prefixEnd_3008346 1029818315353861377426583 := by
  unfold tailWord_3008346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430848189820925359357223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73148928506189134291619261 27430848189820925359357223)
  ·
    refine ⟨41146272284731388039035835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27430848189820925359357223 41146272284731388039035835)
    ·
      refine ⟨61719408427097082058553753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41146272284731388039035835 61719408427097082058553753)
      ·
        refine ⟨46289556320322811543915315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61719408427097082058553753 46289556320322811543915315)
        ·
          refine ⟨69434334480484217315872973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46289556320322811543915315 69434334480484217315872973)
          ·
            refine ⟨26037875430181581493452365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69434334480484217315872973 26037875430181581493452365)
            ·
              refine ⟨9764203286318093060044637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26037875430181581493452365 9764203286318093060044637)
              ·
                refine ⟨3661576232369284897516739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9764203286318093060044637 3661576232369284897516739)
                ·
                  refine ⟨5492364348553927346275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661576232369284897516739 5492364348553927346275109)
                  ·
                    refine ⟨1029818315353861377426583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492364348553927346275109 1029818315353861377426583)
                    ·
                      rfl

theorem cell22_3008346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_3008346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008346 prefixEnd_3008346 := by exact prefixLift 3008346
  have htrace : WordTrace (prefixWord ++ tailWord_3008346) baseStart_3008346 baseEnd_3008346 := by
    simpa [prefixWord, tailWord_3008346, baseEnd_3008346] using wordTrace_append hprefix tailTrace_3008346
  have hstable : (prefixWord ++ tailWord_3008346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008346).length < 2 ^ (prefixWord ++ tailWord_3008346).sum := by decide
  have hdescent : baseEnd_3008346 < baseStart_3008346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008389 : List Nat := [1, 3, 1, 1, 3, 2, 3, 8]
def baseStart_3008389 : Nat := 118140960795 + 3008389 * 2 ^ 59
def prefixEnd_3008389 : Nat := 4983230072969 + 3 ^ 40 * 3008389 * 2
def baseEnd_3008389 : Nat := 114425892792513733177939

theorem tailTrace_3008389 : CollatzResearch.WordTrace tailWord_3008389 prefixEnd_3008389 114425892792513733177939 := by
  unfold tailWord_3008389
  simp only [CollatzResearch.WordTrace]
  refine ⟨109724961098127919781244221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73149974065418613187496147 109724961098127919781244221)
  ·
    refine ⟨41146860411797969917966583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109724961098127919781244221 41146860411797969917966583)
    ·
      refine ⟨61720290617696954876949875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41146860411797969917966583 61720290617696954876949875)
      ·
        refine ⟨92580435926545432315424813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61720290617696954876949875 92580435926545432315424813)
        ·
          refine ⟨34717663472454537118284305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92580435926545432315424813 34717663472454537118284305)
          ·
            refine ⟨26038247604340902838713229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34717663472454537118284305 26038247604340902838713229)
            ·
              refine ⟨9764342851627838564517461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26038247604340902838713229 9764342851627838564517461)
              ·
                refine ⟨114425892792513733177939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9764342851627838564517461 114425892792513733177939)
                ·
                  rfl

theorem cell22_3008389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 8].length) (baseStart_3008389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008389 prefixEnd_3008389 := by exact prefixLift 3008389
  have htrace : WordTrace (prefixWord ++ tailWord_3008389) baseStart_3008389 baseEnd_3008389 := by
    simpa [prefixWord, tailWord_3008389, baseEnd_3008389] using wordTrace_append hprefix tailTrace_3008389
  have hstable : (prefixWord ++ tailWord_3008389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008389).length < 2 ^ (prefixWord ++ tailWord_3008389).sum := by decide
  have hdescent : baseEnd_3008389 < baseStart_3008389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008419 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_3008419 : Nat := 118140960795 + 3008419 * 2 ^ 59
def prefixEnd_3008419 : Nat := 4983230072969 + 3 ^ 40 * 3008419 * 2
def baseEnd_3008419 : Nat := 1029843304745713520351359

theorem tailTrace_3008419 : CollatzResearch.WordTrace tailWord_3008419 prefixEnd_3008419 1029843304745713520351359 := by
  unfold tailWord_3008419
  simp only [CollatzResearch.WordTrace]
  refine ⟨109726055288019234904836311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73150703525346156603224207 109726055288019234904836311)
  ·
    refine ⟨164589082932028852357254467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109726055288019234904836311 164589082932028852357254467)
    ·
      refine ⟨246883624398043278535881701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164589082932028852357254467 246883624398043278535881701)
      ·
        refine ⟨46290679574633114725477819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246883624398043278535881701 46290679574633114725477819)
        ·
          refine ⟨69436019361949672088216729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46290679574633114725477819 69436019361949672088216729)
          ·
            refine ⟨52077014521462254066162547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69436019361949672088216729 52077014521462254066162547)
            ·
              refine ⟨78115521782193381099243821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52077014521462254066162547 78115521782193381099243821)
              ·
                refine ⟨29293320668322517912216433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78115521782193381099243821 29293320668322517912216433)
                ·
                  refine ⟨21969990501241888434162325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29293320668322517912216433 21969990501241888434162325)
                  ·
                    refine ⟨1029843304745713520351359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21969990501241888434162325 1029843304745713520351359)
                    ·
                      rfl

theorem cell22_3008419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_3008419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008419 prefixEnd_3008419 := by exact prefixLift 3008419
  have htrace : WordTrace (prefixWord ++ tailWord_3008419) baseStart_3008419 baseEnd_3008419 := by
    simpa [prefixWord, tailWord_3008419, baseEnd_3008419] using wordTrace_append hprefix tailTrace_3008419
  have hstable : (prefixWord ++ tailWord_3008419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008419).length < 2 ^ (prefixWord ++ tailWord_3008419).sum := by decide
  have hdescent : baseEnd_3008419 < baseStart_3008419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008468 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3008468 : Nat := 118140960795 + 3008468 * 2 ^ 59
def prefixEnd_3008468 : Nat := 4983230072969 + 3 ^ 40 * 3008468 * 2
def baseEnd_3008468 : Nat := 343286692815697908625403

theorem tailTrace_3008468 : CollatzResearch.WordTrace tailWord_3008468 prefixEnd_3008468 343286692815697908625403 := by
  unfold tailWord_3008468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54863921232420858136685029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73151894976561144182246705 54863921232420858136685029)
  ·
    refine ⟨10286985231078910900628443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54863921232420858136685029 10286985231078910900628443)
    ·
      refine ⟨15430477846618366350942665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10286985231078910900628443 15430477846618366350942665)
      ·
        refine ⟨11572858384963774763206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15430477846618366350942665 11572858384963774763206999)
        ·
          refine ⟨17359287577445662144810499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572858384963774763206999 17359287577445662144810499)
          ·
            refine ⟨26038931366168493217215749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17359287577445662144810499 26038931366168493217215749)
            ·
              refine ⟨4882299631156592478227953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26038931366168493217215749 4882299631156592478227953)
              ·
                refine ⟨3661724723367444358670965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882299631156592478227953 3661724723367444358670965)
                ·
                  refine ⟨343286692815697908625403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3661724723367444358670965 343286692815697908625403)
                  ·
                    rfl

theorem cell22_3008468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3008468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008468 prefixEnd_3008468 := by exact prefixLift 3008468
  have htrace : WordTrace (prefixWord ++ tailWord_3008468) baseStart_3008468 baseEnd_3008468 := by
    simpa [prefixWord, tailWord_3008468, baseEnd_3008468] using wordTrace_append hprefix tailTrace_3008468
  have hstable : (prefixWord ++ tailWord_3008468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008468).length < 2 ^ (prefixWord ++ tailWord_3008468).sum := by decide
  have hdescent : baseEnd_3008468 < baseStart_3008468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008481 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3008481 : Nat := 118140960795 + 3008481 * 2 ^ 59
def prefixEnd_3008481 : Nat := 4983230072969 + 3 ^ 40 * 3008481 * 2
def baseEnd_3008481 : Nat := 1029864528612766025301169

theorem tailTrace_3008481 : CollatzResearch.WordTrace tailWord_3008481 prefixEnd_3008481 1029864528612766025301169 := by
  unfold tailWord_3008481
  simp only [CollatzResearch.WordTrace]
  refine ⟨109728316613794619493593297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73152211075863079662395531 109728316613794619493593297)
  ·
    refine ⟨82296237460345964620194973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109728316613794619493593297 82296237460345964620194973)
    ·
      refine ⟨30861089047629736732573115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82296237460345964620194973 30861089047629736732573115)
      ·
        refine ⟨46291633571444605098859673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30861089047629736732573115 46291633571444605098859673)
        ·
          refine ⟨34718725178583453824144755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46291633571444605098859673 34718725178583453824144755)
          ·
            refine ⟨52078087767875180736217133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34718725178583453824144755 52078087767875180736217133)
            ·
              refine ⟨19529282912953192776081425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52078087767875180736217133 19529282912953192776081425)
              ·
                refine ⟨14646962184714894582061069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19529282912953192776081425 14646962184714894582061069)
                ·
                  refine ⟨5492610819268085468272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14646962184714894582061069 5492610819268085468272901)
                  ·
                    refine ⟨1029864528612766025301169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492610819268085468272901 1029864528612766025301169)
                    ·
                      rfl

theorem cell22_3008481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3008481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008481 prefixEnd_3008481 := by exact prefixLift 3008481
  have htrace : WordTrace (prefixWord ++ tailWord_3008481) baseStart_3008481 baseEnd_3008481 := by
    simpa [prefixWord, tailWord_3008481, baseEnd_3008481] using wordTrace_append hprefix tailTrace_3008481
  have hstable : (prefixWord ++ tailWord_3008481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008481).length < 2 ^ (prefixWord ++ tailWord_3008481).sum := by decide
  have hdescent : baseEnd_3008481 < baseStart_3008481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008545 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3008545 : Nat := 118140960795 + 3008545 * 2 ^ 59
def prefixEnd_3008545 : Nat := 4983230072969 + 3 ^ 40 * 3008545 * 2
def baseEnd_3008545 : Nat := 1029886437120691191700973

theorem tailTrace_3008545 : CollatzResearch.WordTrace tailWord_3008545 prefixEnd_3008545 1029886437120691191700973 := by
  unfold tailWord_3008545
  simp only [CollatzResearch.WordTrace]
  refine ⟨109730650885562758423923089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73153767257041838949282059 109730650885562758423923089)
  ·
    refine ⟨82297988164172068817942317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109730650885562758423923089 82297988164172068817942317)
    ·
      refine ⟨30861745561564525806728369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82297988164172068817942317 30861745561564525806728369)
      ·
        refine ⟨23146309171173394355046277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30861745561564525806728369 23146309171173394355046277)
        ·
          refine ⟨4339932969595011441571177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23146309171173394355046277 4339932969595011441571177)
          ·
            refine ⟨3254949727196258581178383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339932969595011441571177 3254949727196258581178383)
            ·
              refine ⟨4882424590794387871767575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254949727196258581178383 4882424590794387871767575)
              ·
                refine ⟨7323636886191581807651363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882424590794387871767575 7323636886191581807651363)
                ·
                  refine ⟨10985455329287372711477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7323636886191581807651363 10985455329287372711477045)
                  ·
                    refine ⟨1029886437120691191700973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10985455329287372711477045 1029886437120691191700973)
                    ·
                      rfl

theorem cell22_3008545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3008545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008545 prefixEnd_3008545 := by exact prefixLift 3008545
  have htrace : WordTrace (prefixWord ++ tailWord_3008545) baseStart_3008545 baseEnd_3008545 := by
    simpa [prefixWord, tailWord_3008545, baseEnd_3008545] using wordTrace_append hprefix tailTrace_3008545
  have hstable : (prefixWord ++ tailWord_3008545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008545).length < 2 ^ (prefixWord ++ tailWord_3008545).sum := by decide
  have hdescent : baseEnd_3008545 < baseStart_3008545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008558 : List Nat := [4, 1, 3, 1, 1, 3, 1, 8]
def baseStart_3008558 : Nat := 118140960795 + 3008558 * 2 ^ 59
def prefixEnd_3008558 : Nat := 4983230072969 + 3 ^ 40 * 3008558 * 2
def baseEnd_3008558 : Nat := 114432320809595943458437

theorem tailTrace_3008558 : CollatzResearch.WordTrace tailWord_3008558 prefixEnd_3008558 114432320809595943458437 := by
  unfold tailWord_3008558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716390629314457705518291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73154083356343774429430885 13716390629314457705518291)
  ·
    refine ⟨20574585943971686558277437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716390629314457705518291 20574585943971686558277437)
    ·
      refine ⟨7715469728989382459354039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20574585943971686558277437 7715469728989382459354039)
      ·
        refine ⟨11573204593484073689031059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715469728989382459354039 11573204593484073689031059)
        ·
          refine ⟨17359806890226110533546589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573204593484073689031059 17359806890226110533546589)
          ·
            refine ⟨6509927583834791450079971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17359806890226110533546589 6509927583834791450079971)
            ·
              refine ⟨9764891375752187175119957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509927583834791450079971 9764891375752187175119957)
              ·
                refine ⟨114432320809595943458437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9764891375752187175119957 114432320809595943458437)
                ·
                  rfl

theorem cell22_3008558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_3008558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008558 prefixEnd_3008558 := by exact prefixLift 3008558
  have htrace : WordTrace (prefixWord ++ tailWord_3008558) baseStart_3008558 baseEnd_3008558 := by
    simpa [prefixWord, tailWord_3008558, baseEnd_3008558] using wordTrace_append hprefix tailTrace_3008558
  have hstable : (prefixWord ++ tailWord_3008558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008558).length < 2 ^ (prefixWord ++ tailWord_3008558).sum := by decide
  have hdescent : baseEnd_3008558 < baseStart_3008558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008564 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3008564 : Nat := 118140960795 + 3008564 * 2 ^ 59
def prefixEnd_3008564 : Nat := 4983230072969 + 3 ^ 40 * 3008564 * 2
def baseEnd_3008564 : Nat := 343297647069660491825305

theorem tailTrace_3008564 : CollatzResearch.WordTrace tailWord_3008564 prefixEnd_3008564 343297647069660491825305 := by
  unfold tailWord_3008564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54865671936246962334432373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73154229248329283112576497 54865671936246962334432373)
  ·
    refine ⟨5143656744023152718853035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54865671936246962334432373 5143656744023152718853035)
    ·
      refine ⟨7715485116034729078279553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143656744023152718853035 7715485116034729078279553)
      ·
        refine ⟨5786613837026046808709665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7715485116034729078279553 5786613837026046808709665)
        ·
          refine ⟨4339960377769535106532249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5786613837026046808709665 4339960377769535106532249)
          ·
            refine ⟨3254970283327151329899187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339960377769535106532249 3254970283327151329899187)
            ·
              refine ⟨4882455424990726994848781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254970283327151329899187 4882455424990726994848781)
              ·
                refine ⟨1830920784371522623068293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882455424990726994848781 1830920784371522623068293)
                ·
                  refine ⟨343297647069660491825305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830920784371522623068293 343297647069660491825305)
                  ·
                    rfl

theorem cell22_3008564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3008564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008564 prefixEnd_3008564 := by exact prefixLift 3008564
  have htrace : WordTrace (prefixWord ++ tailWord_3008564) baseStart_3008564 baseEnd_3008564 := by
    simpa [prefixWord, tailWord_3008564, baseEnd_3008564] using wordTrace_append hprefix tailTrace_3008564
  have hstable : (prefixWord ++ tailWord_3008564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008564).length < 2 ^ (prefixWord ++ tailWord_3008564).sum := by decide
  have hdescent : baseEnd_3008564 < baseStart_3008564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008590 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3008590 : Nat := 118140960795 + 3008590 * 2 ^ 59
def prefixEnd_3008590 : Nat := 4983230072969 + 3 ^ 40 * 3008590 * 2
def baseEnd_3008590 : Nat := 1029901841540326074325835

theorem tailTrace_3008590 : CollatzResearch.WordTrace tailWord_3008590 prefixEnd_3008590 1029901841540326074325835 := by
  unfold tailWord_3008590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716536521299966388663903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73154861446933154072874149 13716536521299966388663903)
  ·
    refine ⟨20574804781949949582995855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716536521299966388663903 20574804781949949582995855)
    ·
      refine ⟨30862207172924924374493783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20574804781949949582995855 30862207172924924374493783)
      ·
        refine ⟨46293310759387386561740675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30862207172924924374493783 46293310759387386561740675)
        ·
          refine ⟨69439966139081079842611013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46293310759387386561740675 69439966139081079842611013)
          ·
            refine ⟨13019993651077702470489565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69439966139081079842611013 13019993651077702470489565)
            ·
              refine ⟨4882497619154138426433587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13019993651077702470489565 4882497619154138426433587)
              ·
                refine ⟨7323746428731207639650381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882497619154138426433587 7323746428731207639650381)
                ·
                  refine ⟨2746404910774202864868893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7323746428731207639650381 2746404910774202864868893)
                  ·
                    refine ⟨1029901841540326074325835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746404910774202864868893 1029901841540326074325835)
                    ·
                      rfl

theorem cell22_3008590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3008590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008590 prefixEnd_3008590 := by exact prefixLift 3008590
  have htrace : WordTrace (prefixWord ++ tailWord_3008590) baseStart_3008590 baseEnd_3008590 := by
    simpa [prefixWord, tailWord_3008590, baseEnd_3008590] using wordTrace_append hprefix tailTrace_3008590
  have hstable : (prefixWord ++ tailWord_3008590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008590).length < 2 ^ (prefixWord ++ tailWord_3008590).sum := by decide
  have hdescent : baseEnd_3008590 < baseStart_3008590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008601 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3008601 : Nat := 118140960795 + 3008601 * 2 ^ 59
def prefixEnd_3008601 : Nat := 4983230072969 + 3 ^ 40 * 3008601 * 2
def baseEnd_3008601 : Nat := 1029905607065125712300801

theorem tailTrace_3008601 : CollatzResearch.WordTrace tailWord_3008601 prefixEnd_3008601 1029905607065125712300801 := by
  unfold tailWord_3008601
  simp only [CollatzResearch.WordTrace]
  refine ⟨109732693373359879987961657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73155128915573253325307771 109732693373359879987961657)
  ·
    refine ⟨82299520030019909990971243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109732693373359879987961657 82299520030019909990971243)
    ·
      refine ⟨123449280045029864986456865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82299520030019909990971243 123449280045029864986456865)
      ·
        refine ⟨92586960033772398739842649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123449280045029864986456865 92586960033772398739842649)
        ·
          refine ⟨69440220025329299054881987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92586960033772398739842649 69440220025329299054881987)
          ·
            refine ⟨104160330037993948582322981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69440220025329299054881987 104160330037993948582322981)
            ·
              refine ⟨19530061882123865359185559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104160330037993948582322981 19530061882123865359185559)
              ·
                refine ⟨29295092823185798038778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19530061882123865359185559 29295092823185798038778339)
                ·
                  refine ⟨43942639234778697058167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29295092823185798038778339 43942639234778697058167509)
                  ·
                    refine ⟨1029905607065125712300801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43942639234778697058167509 1029905607065125712300801)
                    ·
                      rfl

theorem cell22_3008601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3008601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008601 prefixEnd_3008601 := by exact prefixLift 3008601
  have htrace : WordTrace (prefixWord ++ tailWord_3008601) baseStart_3008601 baseEnd_3008601 := by
    simpa [prefixWord, tailWord_3008601, baseEnd_3008601] using wordTrace_append hprefix tailTrace_3008601
  have hstable : (prefixWord ++ tailWord_3008601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008601).length < 2 ^ (prefixWord ++ tailWord_3008601).sum := by decide
  have hdescent : baseEnd_3008601 < baseStart_3008601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008641 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3008641 : Nat := 118140960795 + 3008641 * 2 ^ 59
def prefixEnd_3008641 : Nat := 4983230072969 + 3 ^ 40 * 3008641 * 2
def baseEnd_3008641 : Nat := 1029919299882578941300679

theorem tailTrace_3008641 : CollatzResearch.WordTrace tailWord_3008641 prefixEnd_3008641 1029919299882578941300679 := by
  unfold tailWord_3008641
  simp only [CollatzResearch.WordTrace]
  refine ⟨109734152293214966819417777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73156101528809977879611851 109734152293214966819417777)
  ·
    refine ⟨82300614219911225114563333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109734152293214966819417777 82300614219911225114563333)
    ·
      refine ⟨15431365166233354708980625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82300614219911225114563333 15431365166233354708980625)
      ·
        refine ⟨11573523874675016031735469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15431365166233354708980625 11573523874675016031735469)
        ·
          refine ⟨4340071453003131011900801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11573523874675016031735469 4340071453003131011900801)
          ·
            refine ⟨3255053589752348258925601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4340071453003131011900801 3255053589752348258925601)
            ·
              refine ⟨2441290192314261194194201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255053589752348258925601 2441290192314261194194201)
              ·
                refine ⟨1830967644235695895645651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441290192314261194194201 1830967644235695895645651)
                ·
                  refine ⟨2746451466353543843468477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830967644235695895645651 2746451466353543843468477)
                  ·
                    refine ⟨1029919299882578941300679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746451466353543843468477 1029919299882578941300679)
                    ·
                      rfl

theorem cell22_3008641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3008641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008641 prefixEnd_3008641 := by exact prefixLift 3008641
  have htrace : WordTrace (prefixWord ++ tailWord_3008641) baseStart_3008641 baseEnd_3008641 := by
    simpa [prefixWord, tailWord_3008641, baseEnd_3008641] using wordTrace_append hprefix tailTrace_3008641
  have hstable : (prefixWord ++ tailWord_3008641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008641).length < 2 ^ (prefixWord ++ tailWord_3008641).sum := by decide
  have hdescent : baseEnd_3008641 < baseStart_3008641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008753 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3008753 : Nat := 118140960795 + 3008753 * 2 ^ 59
def prefixEnd_3008753 : Nat := 4983230072969 + 3 ^ 40 * 3008753 * 2
def baseEnd_3008753 : Nat := 1029957639771447982500335

theorem tailTrace_3008753 : CollatzResearch.WordTrace tailWord_3008753 prefixEnd_3008753 1029957639771447982500335 := by
  unfold tailWord_3008753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109738237268809209947494913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73158824845872806631663275 109738237268809209947494913)
  ·
    refine ⟨82303677951606907460621185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109738237268809209947494913 82303677951606907460621185)
    ·
      refine ⟨61727758463705180595465889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82303677951606907460621185 61727758463705180595465889)
      ·
        refine ⟨46295818847778885446599417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61727758463705180595465889 46295818847778885446599417)
        ·
          refine ⟨34721864135834164084949563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46295818847778885446599417 34721864135834164084949563)
          ·
            refine ⟨52082796203751246127424345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34721864135834164084949563 52082796203751246127424345)
            ·
              refine ⟨39062097152813434595568259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52082796203751246127424345 39062097152813434595568259)
              ·
                refine ⟨58593145729220151893352389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39062097152813434595568259 58593145729220151893352389)
                ·
                  refine ⟨10986214824228778480003573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58593145729220151893352389 10986214824228778480003573)
                  ·
                    refine ⟨1029957639771447982500335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10986214824228778480003573 1029957639771447982500335)
                    ·
                      rfl

theorem cell22_3008753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3008753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008753 prefixEnd_3008753 := by exact prefixLift 3008753
  have htrace : WordTrace (prefixWord ++ tailWord_3008753) baseStart_3008753 baseEnd_3008753 := by
    simpa [prefixWord, tailWord_3008753, baseEnd_3008753] using wordTrace_append hprefix tailTrace_3008753
  have hstable : (prefixWord ++ tailWord_3008753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008753).length < 2 ^ (prefixWord ++ tailWord_3008753).sum := by decide
  have hdescent : baseEnd_3008753 < baseStart_3008753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008772 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3008772 : Nat := 118140960795 + 3008772 * 2 ^ 59
def prefixEnd_3008772 : Nat := 4983230072969 + 3 ^ 40 * 3008772 * 2
def baseEnd_3008772 : Nat := 343321381286579422091759

theorem tailTrace_3008772 : CollatzResearch.WordTrace tailWord_3008772 prefixEnd_3008772 343321381286579422091759 := by
  unfold tailWord_3008772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869465127870188096218285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73159286837160250794957713 54869465127870188096218285)
  ·
    refine ⟨20576049422951320536081857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54869465127870188096218285 20576049422951320536081857)
    ·
      refine ⟨15432037067213490402061393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20576049422951320536081857 15432037067213490402061393)
      ·
        refine ⟨11574027800410117801546045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15432037067213490402061393 11574027800410117801546045)
        ·
          refine ⟨4340260425153794175579767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11574027800410117801546045 4340260425153794175579767)
          ·
            refine ⟨6510390637730691263369651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340260425153794175579767 6510390637730691263369651)
            ·
              refine ⟨9765585956596036895054477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510390637730691263369651 9765585956596036895054477)
              ·
                refine ⟨3662094733723513835645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9765585956596036895054477 3662094733723513835645429)
                ·
                  refine ⟨343321381286579422091759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662094733723513835645429 343321381286579422091759)
                  ·
                    rfl

theorem cell22_3008772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3008772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008772 prefixEnd_3008772 := by exact prefixLift 3008772
  have htrace : WordTrace (prefixWord ++ tailWord_3008772) baseStart_3008772 baseEnd_3008772 := by
    simpa [prefixWord, tailWord_3008772, baseEnd_3008772] using wordTrace_append hprefix tailTrace_3008772
  have hstable : (prefixWord ++ tailWord_3008772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008772).length < 2 ^ (prefixWord ++ tailWord_3008772).sum := by decide
  have hdescent : baseEnd_3008772 < baseStart_3008772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008783 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 6]
def baseStart_3008783 : Nat := 118140960795 + 3008783 * 2 ^ 59
def prefixEnd_3008783 : Nat := 4983230072969 + 3 ^ 40 * 3008783 * 2
def baseEnd_3008783 : Nat := 343322636461512634750081

theorem tailTrace_3008783 : CollatzResearch.WordTrace tailWord_3008783 prefixEnd_3008783 343322636461512634750081 := by
  unfold tailWord_3008783
  simp only [CollatzResearch.WordTrace]
  refine ⟨109739331458700525071087003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73159554305800350047391335 109739331458700525071087003)
  ·
    refine ⟨164608997188050787606630505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109739331458700525071087003 164608997188050787606630505)
    ·
      refine ⟨123456747891038090704972879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164608997188050787606630505 123456747891038090704972879)
      ·
        refine ⟨185185121836557136057459319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123456747891038090704972879 185185121836557136057459319)
        ·
          refine ⟨277777682754835704086188979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185185121836557136057459319 277777682754835704086188979)
          ·
            refine ⟨416666524132253556129283469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277777682754835704086188979 416666524132253556129283469)
            ·
              refine ⟨156249946549595083548481301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416666524132253556129283469 156249946549595083548481301)
              ·
                refine ⟨7324216244512269541335061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156249946549595083548481301 7324216244512269541335061)
                ·
                  refine ⟨343322636461512634750081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7324216244512269541335061 343322636461512634750081)
                  ·
                    rfl

theorem cell22_3008783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_3008783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008783 prefixEnd_3008783 := by exact prefixLift 3008783
  have htrace : WordTrace (prefixWord ++ tailWord_3008783) baseStart_3008783 baseEnd_3008783 := by
    simpa [prefixWord, tailWord_3008783, baseEnd_3008783] using wordTrace_append hprefix tailTrace_3008783
  have hstable : (prefixWord ++ tailWord_3008783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008783).length < 2 ^ (prefixWord ++ tailWord_3008783).sum := by decide
  have hdescent : baseEnd_3008783 < baseStart_3008783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008785 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3008785 : Nat := 118140960795 + 3008785 * 2 ^ 59
def prefixEnd_3008785 : Nat := 4983230072969 + 3 ^ 40 * 3008785 * 2
def baseEnd_3008785 : Nat := 1029968594025410565700237

theorem tailTrace_3008785 : CollatzResearch.WordTrace tailWord_3008785 prefixEnd_3008785 1029968594025410565700237 := by
  unfold tailWord_3008785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109739404404693279412659809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73159602936462186275106539 109739404404693279412659809)
  ·
    refine ⟨82304553303519959559494857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109739404404693279412659809 82304553303519959559494857)
    ·
      refine ⟨61728414977639969669621143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82304553303519959559494857 61728414977639969669621143)
      ·
        refine ⟨92592622466459954504431715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61728414977639969669621143 92592622466459954504431715)
        ·
          refine ⟨138888933699689931756647573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92592622466459954504431715 138888933699689931756647573)
          ·
            refine ⟨6510418767172965551092855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138888933699689931756647573 6510418767172965551092855)
            ·
              refine ⟨9765628150759448326639283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510418767172965551092855 9765628150759448326639283)
              ·
                refine ⟨14648442226139172489958925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765628150759448326639283 14648442226139172489958925)
                ·
                  refine ⟨5493165834802189683734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14648442226139172489958925 5493165834802189683734597)
                  ·
                    refine ⟨1029968594025410565700237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493165834802189683734597 1029968594025410565700237)
                    ·
                      rfl

theorem cell22_3008785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3008785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008785 prefixEnd_3008785 := by exact prefixLift 3008785
  have htrace : WordTrace (prefixWord ++ tailWord_3008785) baseStart_3008785 baseEnd_3008785 := by
    simpa [prefixWord, tailWord_3008785, baseEnd_3008785] using wordTrace_append hprefix tailTrace_3008785
  have hstable : (prefixWord ++ tailWord_3008785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008785).length < 2 ^ (prefixWord ++ tailWord_3008785).sum := by decide
  have hdescent : baseEnd_3008785 < baseStart_3008785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008810 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3008810 : Nat := 118140960795 + 3008810 * 2 ^ 59
def prefixEnd_3008810 : Nat := 4983230072969 + 3 ^ 40 * 3008810 * 2
def baseEnd_3008810 : Nat := 1029977152036318833825161

theorem tailTrace_3008810 : CollatzResearch.WordTrace tailWord_3008810 prefixEnd_3008810 1029977152036318833825161 := by
  unfold tailWord_3008810
  simp only [CollatzResearch.WordTrace]
  refine ⟨27435079057400677170579971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73160210819735139121546589 27435079057400677170579971)
  ·
    refine ⟨41152618586101015755869957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27435079057400677170579971 41152618586101015755869957)
    ·
      refine ⟨7716115984893940454225617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41152618586101015755869957 7716115984893940454225617)
      ·
        refine ⟨5787086988670455340669213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7716115984893940454225617 5787086988670455340669213)
        ·
          refine ⟨2170157620751420752750955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5787086988670455340669213 2170157620751420752750955)
          ·
            refine ⟨3255236431127131129126433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170157620751420752750955 3255236431127131129126433)
            ·
              refine ⟨2441427323345348346844825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255236431127131129126433 2441427323345348346844825)
              ·
                refine ⟨1831070492509011260133619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441427323345348346844825 1831070492509011260133619)
                ·
                  refine ⟨2746605738763516890200429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831070492509011260133619 2746605738763516890200429)
                  ·
                    refine ⟨1029977152036318833825161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746605738763516890200429 1029977152036318833825161)
                    ·
                      rfl

theorem cell22_3008810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3008810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008810 prefixEnd_3008810 := by exact prefixLift 3008810
  have htrace : WordTrace (prefixWord ++ tailWord_3008810) baseStart_3008810 baseEnd_3008810 := by
    simpa [prefixWord, tailWord_3008810, baseEnd_3008810] using wordTrace_append hprefix tailTrace_3008810
  have hstable : (prefixWord ++ tailWord_3008810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008810).length < 2 ^ (prefixWord ++ tailWord_3008810).sum := by decide
  have hdescent : baseEnd_3008810 < baseStart_3008810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008815 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 4, 3]
def baseStart_3008815 : Nat := 118140960795 + 3008815 * 2 ^ 59
def prefixEnd_3008815 : Nat := 4983230072969 + 3 ^ 40 * 3008815 * 2
def baseEnd_3008815 : Nat := 1029978863638500487450145

theorem tailTrace_3008815 : CollatzResearch.WordTrace tailWord_3008815 prefixEnd_3008815 1029978863638500487450145 := by
  unfold tailWord_3008815
  simp only [CollatzResearch.WordTrace]
  refine ⟨109740498594584594536251899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73160332396389729690834599 109740498594584594536251899)
  ·
    refine ⟨164610747891876891804377849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109740498594584594536251899 164610747891876891804377849)
    ·
      refine ⟨123458060918907668853283387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164610747891876891804377849 123458060918907668853283387)
      ·
        refine ⟨185187091378361503279925081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123458060918907668853283387 185187091378361503279925081)
        ·
          refine ⟨138890318533771127459943811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185187091378361503279925081 138890318533771127459943811)
          ·
            refine ⟨208335477800656691189915717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138890318533771127459943811 208335477800656691189915717)
            ·
              refine ⟨39062902087623129598109197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208335477800656691189915717 39062902087623129598109197)
              ·
                refine ⟨14648588282858673599290949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39062902087623129598109197 14648588282858673599290949)
                ·
                  refine ⟨2746610303036001299867053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14648588282858673599290949 2746610303036001299867053)
                  ·
                    refine ⟨1029978863638500487450145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746610303036001299867053 1029978863638500487450145)
                    ·
                      rfl

theorem cell22_3008815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_3008815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008815 prefixEnd_3008815 := by exact prefixLift 3008815
  have htrace : WordTrace (prefixWord ++ tailWord_3008815) baseStart_3008815 baseEnd_3008815 := by
    simpa [prefixWord, tailWord_3008815, baseEnd_3008815] using wordTrace_append hprefix tailTrace_3008815
  have hstable : (prefixWord ++ tailWord_3008815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008815).length < 2 ^ (prefixWord ++ tailWord_3008815).sum := by decide
  have hdescent : baseEnd_3008815 < baseStart_3008815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_3008843 : Nat := 118140960795 + 3008843 * 2 ^ 59
def prefixEnd_3008843 : Nat := 4983230072969 + 3 ^ 40 * 3008843 * 2
def baseEnd_3008843 : Nat := 1029988448610717747750059

theorem tailTrace_3008843 : CollatzResearch.WordTrace tailWord_3008843 prefixEnd_3008843 1029988448610717747750059 := by
  unfold tailWord_3008843
  simp only [CollatzResearch.WordTrace]
  refine ⟨109741519838483155318271183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73161013225655436878847455 109741519838483155318271183)
  ·
    refine ⟨164612279757724732977406775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109741519838483155318271183 164612279757724732977406775)
    ·
      refine ⟨246918419636587099466110163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164612279757724732977406775 246918419636587099466110163)
      ·
        refine ⟨370377629454880649199165245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246918419636587099466110163 370377629454880649199165245)
        ·
          refine ⟨138891611045580243449686967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370377629454880649199165245 138891611045580243449686967)
          ·
            refine ⟨208337416568370365174530451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138891611045580243449686967 208337416568370365174530451)
            ·
              refine ⟨312506124852555547761795677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208337416568370365174530451 312506124852555547761795677)
              ·
                refine ⟨117189796819708330410673379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312506124852555547761795677 117189796819708330410673379)
                ·
                  refine ⟨175784695229562495616010069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117189796819708330410673379 175784695229562495616010069)
                  ·
                    refine ⟨1029988448610717747750059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175784695229562495616010069 1029988448610717747750059)
                    ·
                      rfl

theorem cell22_3008843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_3008843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008843 prefixEnd_3008843 := by exact prefixLift 3008843
  have htrace : WordTrace (prefixWord ++ tailWord_3008843) baseStart_3008843 baseEnd_3008843 := by
    simpa [prefixWord, tailWord_3008843, baseEnd_3008843] using wordTrace_append hprefix tailTrace_3008843
  have hstable : (prefixWord ++ tailWord_3008843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008843).length < 2 ^ (prefixWord ++ tailWord_3008843).sum := by decide
  have hdescent : baseEnd_3008843 < baseStart_3008843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008866 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3008866 : Nat := 118140960795 + 3008866 * 2 ^ 59
def prefixEnd_3008866 : Nat := 4983230072969 + 3 ^ 40 * 3008866 * 2
def baseEnd_3008866 : Nat := 1029996321980753354424989

theorem tailTrace_3008866 : CollatzResearch.WordTrace tailWord_3008866 prefixEnd_3008866 1029996321980753354424989 := by
  unfold tailWord_3008866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27435589679349957561589613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73161572478266553497572301 27435589679349957561589613)
  ·
    refine ⟨10288346129756234085596105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27435589679349957561589613 10288346129756234085596105)
    ·
      refine ⟨7716259597317175564197079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10288346129756234085596105 7716259597317175564197079)
      ·
        refine ⟨11574389395975763346295619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7716259597317175564197079 11574389395975763346295619)
        ·
          refine ⟨17361584093963645019443429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574389395975763346295619 17361584093963645019443429)
          ·
            refine ⟨3255297017618183441145643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17361584093963645019443429 3255297017618183441145643)
            ·
              refine ⟨4882945526427275161718465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255297017618183441145643 4882945526427275161718465)
              ·
                refine ⟨3662209144820456371288849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882945526427275161718465 3662209144820456371288849)
                ·
                  refine ⟨2746656858615342278466637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662209144820456371288849 2746656858615342278466637)
                  ·
                    refine ⟨1029996321980753354424989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746656858615342278466637 1029996321980753354424989)
                    ·
                      rfl

theorem cell22_3008866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3008866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008866 prefixEnd_3008866 := by exact prefixLift 3008866
  have htrace : WordTrace (prefixWord ++ tailWord_3008866) baseStart_3008866 baseEnd_3008866 := by
    simpa [prefixWord, tailWord_3008866, baseEnd_3008866] using wordTrace_append hprefix tailTrace_3008866
  have hstable : (prefixWord ++ tailWord_3008866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008866).length < 2 ^ (prefixWord ++ tailWord_3008866).sum := by decide
  have hdescent : baseEnd_3008866 < baseStart_3008866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008967 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3008967 : Nat := 118140960795 + 3008967 * 2 ^ 59
def prefixEnd_3008967 : Nat := 4983230072969 + 3 ^ 40 * 3008967 * 2
def baseEnd_3008967 : Nat := 1030030896344822757649679

theorem tailTrace_3008967 : CollatzResearch.WordTrace tailWord_3008967 prefixEnd_3008967 1030030896344822757649679 := by
  unfold tailWord_3008967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109746042490033924495785155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73164028326689282997190103 109746042490033924495785155)
  ·
    refine ⟨164619063735050886743677733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109746042490033924495785155 164619063735050886743677733)
    ·
      refine ⟨30866074450322041264439575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164619063735050886743677733 30866074450322041264439575)
      ·
        refine ⟨46299111675483061896659363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30866074450322041264439575 46299111675483061896659363)
        ·
          refine ⟨69448667513224592844989045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46299111675483061896659363 69448667513224592844989045)
          ·
            refine ⟨6510812579364805579217723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69448667513224592844989045 6510812579364805579217723)
            ·
              refine ⟨9766218869047208368826585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510812579364805579217723 9766218869047208368826585)
              ·
                refine ⟨7324664151785406276619939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9766218869047208368826585 7324664151785406276619939)
                ·
                  refine ⟨10986996227678109414929909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324664151785406276619939 10986996227678109414929909)
                  ·
                    refine ⟨1030030896344822757649679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10986996227678109414929909 1030030896344822757649679)
                    ·
                      rfl

theorem cell22_3008967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3008967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3008967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3008967 prefixEnd_3008967 := by exact prefixLift 3008967
  have htrace : WordTrace (prefixWord ++ tailWord_3008967) baseStart_3008967 baseEnd_3008967 := by
    simpa [prefixWord, tailWord_3008967, baseEnd_3008967] using wordTrace_append hprefix tailTrace_3008967
  have hstable : (prefixWord ++ tailWord_3008967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008967).length < 2 ^ (prefixWord ++ tailWord_3008967).sum := by decide
  have hdescent : baseEnd_3008967 < baseStart_3008967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009014 : List Nat := [5, 1, 1, 1, 2, 1, 5, 6]
def baseStart_3009014 : Nat := 118140960795 + 3009014 * 2 ^ 59
def prefixEnd_3009014 : Nat := 4983230072969 + 3 ^ 40 * 3009014 * 2
def baseEnd_3009014 : Nat := 114449665045036700191615

theorem tailTrace_3009014 : CollatzResearch.WordTrace tailWord_3009014 prefixEnd_3009014 114449665045036700191615 := by
  unfold tailWord_3009014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859234795053978220171631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73165171147242434348497397 6859234795053978220171631)
  ·
    refine ⟨10288852192580967330257447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859234795053978220171631 10288852192580967330257447)
    ·
      refine ⟨15433278288871450995386171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288852192580967330257447 15433278288871450995386171)
      ·
        refine ⟨23149917433307176493079257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15433278288871450995386171 23149917433307176493079257)
        ·
          refine ⟨17362438074980382369809443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23149917433307176493079257 17362438074980382369809443)
          ·
            refine ⟨26043657112470573554714165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17362438074980382369809443 26043657112470573554714165)
            ·
              refine ⟨2441592854294116270754453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26043657112470573554714165 2441592854294116270754453)
              ·
                refine ⟨114449665045036700191615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2441592854294116270754453 114449665045036700191615)
                ·
                  rfl

theorem cell22_3009014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_3009014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009014 prefixEnd_3009014 := by exact prefixLift 3009014
  have htrace : WordTrace (prefixWord ++ tailWord_3009014) baseStart_3009014 baseEnd_3009014 := by
    simpa [prefixWord, tailWord_3009014, baseEnd_3009014] using wordTrace_append hprefix tailTrace_3009014
  have hstable : (prefixWord ++ tailWord_3009014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009014).length < 2 ^ (prefixWord ++ tailWord_3009014).sum := by decide
  have hdescent : baseEnd_3009014 < baseStart_3009014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009057 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3009057 : Nat := 118140960795 + 3009057 * 2 ^ 59
def prefixEnd_3009057 : Nat := 4983230072969 + 3 ^ 40 * 3009057 * 2
def baseEnd_3009057 : Nat := 1030061705184092522899403

theorem tailTrace_3009057 : CollatzResearch.WordTrace tailWord_3009057 prefixEnd_3009057 1030061705184092522899403 := by
  unfold tailWord_3009057
  simp only [CollatzResearch.WordTrace]
  refine ⟨109749325059707869866561425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73166216706471913244374283 109749325059707869866561425)
  ·
    refine ⟨82311993794780902399921069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109749325059707869866561425 82311993794780902399921069)
    ·
      refine ⟨30866997673042838399970401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82311993794780902399921069 30866997673042838399970401)
      ·
        refine ⟨23150248254782128799977801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30866997673042838399970401 23150248254782128799977801)
        ·
          refine ⟨17362686191086596599983351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23150248254782128799977801 17362686191086596599983351)
          ·
            refine ⟨26044029286629894899975027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17362686191086596599983351 26044029286629894899975027)
            ·
              refine ⟨39066043929944842349962541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26044029286629894899975027 39066043929944842349962541)
              ·
                refine ⟨14649766473729315881235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39066043929944842349962541 14649766473729315881235953)
                ·
                  refine ⟨10987324855296986910926965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14649766473729315881235953 10987324855296986910926965)
                  ·
                    refine ⟨1030061705184092522899403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10987324855296986910926965 1030061705184092522899403)
                    ·
                      rfl

theorem cell22_3009057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3009057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009057 prefixEnd_3009057 := by exact prefixLift 3009057
  have htrace : WordTrace (prefixWord ++ tailWord_3009057) baseStart_3009057 baseEnd_3009057 := by
    simpa [prefixWord, tailWord_3009057, baseEnd_3009057] using wordTrace_append hprefix tailTrace_3009057
  have hstable : (prefixWord ++ tailWord_3009057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009057).length < 2 ^ (prefixWord ++ tailWord_3009057).sum := by decide
  have hdescent : baseEnd_3009057 < baseStart_3009057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009072 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_3009072 : Nat := 118140960795 + 3009072 * 2 ^ 59
def prefixEnd_3009072 : Nat := 4983230072969 + 3 ^ 40 * 3009072 * 2
def baseEnd_3009072 : Nat := 1030066839990637483774357

theorem tailTrace_3009072 : CollatzResearch.WordTrace tailWord_3009072 prefixEnd_3009072 1030066839990637483774357 := by
  unfold tailWord_3009072
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874936077326763714178735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73166581436435684952238313 54874936077326763714178735)
  ·
    refine ⟨82312404115990145571268103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54874936077326763714178735 82312404115990145571268103)
    ·
      refine ⟨123468606173985218356902155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82312404115990145571268103 123468606173985218356902155)
      ·
        refine ⟨185202909260977827535353233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123468606173985218356902155 185202909260977827535353233)
        ·
          refine ⟨138902181945733370651514925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185202909260977827535353233 138902181945733370651514925)
          ·
            refine ⟨52088318229650013994318097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138902181945733370651514925 52088318229650013994318097)
            ·
              refine ⟨39066238672237510495738573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52088318229650013994318097 39066238672237510495738573)
              ·
                refine ⟨14649839502089066435901965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39066238672237510495738573 14649839502089066435901965)
                ·
                  refine ⟨5493689813283399913463237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14649839502089066435901965 5493689813283399913463237)
                  ·
                    refine ⟨1030066839990637483774357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493689813283399913463237 1030066839990637483774357)
                    ·
                      rfl

theorem cell22_3009072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_3009072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009072 prefixEnd_3009072 := by exact prefixLift 3009072
  have htrace : WordTrace (prefixWord ++ tailWord_3009072) baseStart_3009072 baseEnd_3009072 := by
    simpa [prefixWord, tailWord_3009072, baseEnd_3009072] using wordTrace_append hprefix tailTrace_3009072
  have hstable : (prefixWord ++ tailWord_3009072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009072).length < 2 ^ (prefixWord ++ tailWord_3009072).sum := by decide
  have hdescent : baseEnd_3009072 < baseStart_3009072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009132 : List Nat := [2, 2, 1, 1, 3, 1, 4, 8]
def baseStart_3009132 : Nat := 118140960795 + 3009132 * 2 ^ 59
def prefixEnd_3009132 : Nat := 4983230072969 + 3 ^ 40 * 3009132 * 2
def baseEnd_3009132 : Nat := 114454153246313036363797

theorem tailTrace_3009132 : CollatzResearch.WordTrace tailWord_3009132 prefixEnd_3009132 114454153246313036363797 := by
  unfold tailWord_3009132
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876030267218078837770825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73168040356290771783694433 54876030267218078837770825)
  ·
    refine ⟨41157022700413559128328119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54876030267218078837770825 41157022700413559128328119)
    ·
      refine ⟨61735534050620338692492179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41157022700413559128328119 61735534050620338692492179)
      ·
        refine ⟨92603301075930508038738269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61735534050620338692492179 92603301075930508038738269)
        ·
          refine ⟨34726237903473940514526851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92603301075930508038738269 34726237903473940514526851)
          ·
            refine ⟨52089356855210910771790277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34726237903473940514526851 52089356855210910771790277)
            ·
              refine ⟨9766754410352045769710677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52089356855210910771790277 9766754410352045769710677)
              ·
                refine ⟨114454153246313036363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9766754410352045769710677 114454153246313036363797)
                ·
                  rfl

theorem cell22_3009132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_3009132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009132 prefixEnd_3009132 := by exact prefixLift 3009132
  have htrace : WordTrace (prefixWord ++ tailWord_3009132) baseStart_3009132 baseEnd_3009132 := by
    simpa [prefixWord, tailWord_3009132, baseEnd_3009132] using wordTrace_append hprefix tailTrace_3009132
  have hstable : (prefixWord ++ tailWord_3009132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009132).length < 2 ^ (prefixWord ++ tailWord_3009132).sum := by decide
  have hdescent : baseEnd_3009132 < baseStart_3009132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009149 : List Nat := [1, 4, 1, 1, 6, 9]
def baseStart_3009149 : Nat := 118140960795 + 3009149 * 2 ^ 59
def prefixEnd_3009149 : Nat := 4983230072969 + 3 ^ 40 * 3009149 * 2
def baseEnd_3009149 : Nat := 12717199983509073451841

theorem tailTrace_3009149 : CollatzResearch.WordTrace tailWord_3009149 prefixEnd_3009149 12717199983509073451841 := by
  unfold tailWord_3009149
  simp only [CollatzResearch.WordTrace]
  refine ⟨109752680575374569578910501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73168453716916379719273667 109752680575374569578910501)
  ·
    refine ⟨20578627607882731796045719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109752680575374569578910501 20578627607882731796045719)
    ·
      refine ⟨30867941411824097694068579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20578627607882731796045719 30867941411824097694068579)
      ·
        refine ⟨46301912117736146541102869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30867941411824097694068579 46301912117736146541102869)
        ·
          refine ⟨2170402130518881869114197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46301912117736146541102869 2170402130518881869114197)
          ·
            refine ⟨12717199983509073451841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2170402130518881869114197 12717199983509073451841)
            ·
              rfl

theorem cell22_3009149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 9].length) (baseStart_3009149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009149 prefixEnd_3009149 := by exact prefixLift 3009149
  have htrace : WordTrace (prefixWord ++ tailWord_3009149) baseStart_3009149 baseEnd_3009149 := by
    simpa [prefixWord, tailWord_3009149, baseEnd_3009149] using wordTrace_append hprefix tailTrace_3009149
  have hstable : (prefixWord ++ tailWord_3009149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009149).length < 2 ^ (prefixWord ++ tailWord_3009149).sum := by decide
  have hdescent : baseEnd_3009149 < baseStart_3009149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009228 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_3009228 : Nat := 118140960795 + 3009228 * 2 ^ 59
def prefixEnd_3009228 : Nat := 4983230072969 + 3 ^ 40 * 3009228 * 2
def baseEnd_3009228 : Nat := 343373413992901692291293

theorem tailTrace_3009228 : CollatzResearch.WordTrace tailWord_3009228 prefixEnd_3009228 343373413992901692291293 := by
  unfold tailWord_3009228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877780971044183035518169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73170374628058910714024225 54877780971044183035518169)
  ·
    refine ⟨41158335728283137276638627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54877780971044183035518169 41158335728283137276638627)
    ·
      refine ⟨61737503592424705914957941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41158335728283137276638627 61737503592424705914957941)
      ·
        refine ⟨5787890961789816179527307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61737503592424705914957941 5787890961789816179527307)
        ·
          refine ⟨8681836442684724269290961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787890961789816179527307 8681836442684724269290961)
          ·
            refine ⟨6511377332013543201968221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681836442684724269290961 6511377332013543201968221)
            ·
              refine ⟨2441766499505078700738083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6511377332013543201968221 2441766499505078700738083)
              ·
                refine ⟨3662649749257618051107125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441766499505078700738083 3662649749257618051107125)
                ·
                  refine ⟨343373413992901692291293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662649749257618051107125 343373413992901692291293)
                  ·
                    rfl

theorem cell22_3009228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_3009228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009228 prefixEnd_3009228 := by exact prefixLift 3009228
  have htrace : WordTrace (prefixWord ++ tailWord_3009228) baseStart_3009228 baseEnd_3009228 := by
    simpa [prefixWord, tailWord_3009228, baseEnd_3009228] using wordTrace_append hprefix tailTrace_3009228
  have hstable : (prefixWord ++ tailWord_3009228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009228).length < 2 ^ (prefixWord ++ tailWord_3009228).sum := by decide
  have hdescent : baseEnd_3009228 < baseStart_3009228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009239 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 6]
def baseStart_3009239 : Nat := 118140960795 + 3009239 * 2 ^ 59
def prefixEnd_3009239 : Nat := 4983230072969 + 3 ^ 40 * 3009239 * 2
def baseEnd_3009239 : Nat := 343374669167834904949615

theorem tailTrace_3009239 : CollatzResearch.WordTrace tailWord_3009239 prefixEnd_3009239 343374669167834904949615 := by
  unfold tailWord_3009239
  simp only [CollatzResearch.WordTrace]
  refine ⟨109755963145048514949686771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73170642096699009966457847 109755963145048514949686771)
  ·
    refine ⟨164633944717572772424530157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109755963145048514949686771 164633944717572772424530157)
    ·
      refine ⟨61737729269089789659198809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164633944717572772424530157 61737729269089789659198809)
      ·
        refine ⟨46303296951817342244399107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61737729269089789659198809 46303296951817342244399107)
        ·
          refine ⟨69454945427726013366598661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46303296951817342244399107 69454945427726013366598661)
          ·
            refine ⟨13022802267698627506237249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69454945427726013366598661 13022802267698627506237249)
            ·
              refine ⟨9767101700773970629677937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13022802267698627506237249 9767101700773970629677937)
              ·
                refine ⟨7325326275580477972258453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767101700773970629677937 7325326275580477972258453)
                ·
                  refine ⟨343374669167834904949615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7325326275580477972258453 343374669167834904949615)
                  ·
                    rfl

theorem cell22_3009239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_3009239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009239 prefixEnd_3009239 := by exact prefixLift 3009239
  have htrace : WordTrace (prefixWord ++ tailWord_3009239) baseStart_3009239 baseEnd_3009239 := by
    simpa [prefixWord, tailWord_3009239, baseEnd_3009239] using wordTrace_append hprefix tailTrace_3009239
  have hstable : (prefixWord ++ tailWord_3009239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009239).length < 2 ^ (prefixWord ++ tailWord_3009239).sum := by decide
  have hdescent : baseEnd_3009239 < baseStart_3009239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009241 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_3009241 : Nat := 118140960795 + 3009241 * 2 ^ 59
def prefixEnd_3009241 : Nat := 4983230072969 + 3 ^ 40 * 3009241 * 2
def baseEnd_3009241 : Nat := 1030124692144377376298839

theorem tailTrace_3009241 : CollatzResearch.WordTrace tailWord_3009241 prefixEnd_3009241 1030124692144377376298839 := by
  unfold tailWord_3009241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109756036091041269291259577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73170690727360846194173051 109756036091041269291259577)
  ·
    refine ⟨82317027068280951968444683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109756036091041269291259577 82317027068280951968444683)
    ·
      refine ⟨123475540602421427952667025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82317027068280951968444683 123475540602421427952667025)
      ·
        refine ⟨92606655451816070964500269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123475540602421427952667025 92606655451816070964500269)
        ·
          refine ⟨34727495794431026611687601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92606655451816070964500269 34727495794431026611687601)
          ·
            refine ⟨26045621845823269958765701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34727495794431026611687601 26045621845823269958765701)
            ·
              refine ⟨4883554096091863117268569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26045621845823269958765701 4883554096091863117268569)
              ·
                refine ⟨3662665572068897337951427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883554096091863117268569 3662665572068897337951427)
                ·
                  refine ⟨5493998358103346006927141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662665572068897337951427 5493998358103346006927141)
                  ·
                    refine ⟨1030124692144377376298839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493998358103346006927141 1030124692144377376298839)
                    ·
                      rfl

theorem cell22_3009241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_3009241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009241 prefixEnd_3009241 := by exact prefixLift 3009241
  have htrace : WordTrace (prefixWord ++ tailWord_3009241) baseStart_3009241 baseEnd_3009241 := by
    simpa [prefixWord, tailWord_3009241, baseEnd_3009241] using wordTrace_append hprefix tailTrace_3009241
  have hstable : (prefixWord ++ tailWord_3009241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009241).length < 2 ^ (prefixWord ++ tailWord_3009241).sum := by decide
  have hdescent : baseEnd_3009241 < baseStart_3009241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009271 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 2, 3]
def baseStart_3009271 : Nat := 118140960795 + 3009271 * 2 ^ 59
def prefixEnd_3009271 : Nat := 4983230072969 + 3 ^ 40 * 3009271 * 2
def baseEnd_3009271 : Nat := 1030134961757467298048747

theorem tailTrace_3009271 : CollatzResearch.WordTrace tailWord_3009271 prefixEnd_3009271 1030134961757467298048747 := by
  unfold tailWord_3009271
  simp only [CollatzResearch.WordTrace]
  refine ⟨109757130280932584414851667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73171420187288389609901111 109757130280932584414851667)
  ·
    refine ⟨164635695421398876622277501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109757130280932584414851667 164635695421398876622277501)
    ·
      refine ⟨61738385783024578733354063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164635695421398876622277501 61738385783024578733354063)
      ·
        refine ⟨92607578674536868100031095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61738385783024578733354063 92607578674536868100031095)
        ·
          refine ⟨138911368011805302150046643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92607578674536868100031095 138911368011805302150046643)
          ·
            refine ⟨208367052017707953225069965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138911368011805302150046643 208367052017707953225069965)
            ·
              refine ⟨78137644506640482459401237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208367052017707953225069965 78137644506640482459401237)
              ·
                refine ⟨3662702086248772615284433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78137644506640482459401237 3662702086248772615284433)
                ·
                  refine ⟨2747026564686579461463325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662702086248772615284433 2747026564686579461463325)
                  ·
                    refine ⟨1030134961757467298048747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747026564686579461463325 1030134961757467298048747)
                    ·
                      rfl

theorem cell22_3009271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_3009271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009271 prefixEnd_3009271 := by exact prefixLift 3009271
  have htrace : WordTrace (prefixWord ++ tailWord_3009271) baseStart_3009271 baseEnd_3009271 := by
    simpa [prefixWord, tailWord_3009271, baseEnd_3009271] using wordTrace_append hprefix tailTrace_3009271
  have hstable : (prefixWord ++ tailWord_3009271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009271).length < 2 ^ (prefixWord ++ tailWord_3009271).sum := by decide
  have hdescent : baseEnd_3009271 < baseStart_3009271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009288 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3009288 : Nat := 118140960795 + 3009288 * 2 ^ 59
def prefixEnd_3009288 : Nat := 4983230072969 + 3 ^ 40 * 3009288 * 2
def baseEnd_3009288 : Nat := 1030140781204884920373695

theorem tailTrace_3009288 : CollatzResearch.WordTrace tailWord_3009288 prefixEnd_3009288 1030140781204884920373695 := by
  unfold tailWord_3009288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54878875160935498159110259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73171833547913997545480345 54878875160935498159110259)
  ·
    refine ⟨82318312741403247238665389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54878875160935498159110259 82318312741403247238665389)
    ·
      refine ⟨30869367278026217714499521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82318312741403247238665389 30869367278026217714499521)
      ·
        refine ⟨23152025458519663285874641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30869367278026217714499521 23152025458519663285874641)
        ·
          refine ⟨17364019093889747464405981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23152025458519663285874641 17364019093889747464405981)
          ·
            refine ⟨6511507160208655299152243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17364019093889747464405981 6511507160208655299152243)
            ·
              refine ⟨9767260740312982948728365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511507160208655299152243 9767260740312982948728365)
              ·
                refine ⟨3662722777617368605773137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9767260740312982948728365 3662722777617368605773137)
                ·
                  refine ⟨2747042083213026454329853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662722777617368605773137 2747042083213026454329853)
                  ·
                    refine ⟨1030140781204884920373695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747042083213026454329853 1030140781204884920373695)
                    ·
                      rfl

theorem cell22_3009288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3009288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009288 prefixEnd_3009288 := by exact prefixLift 3009288
  have htrace : WordTrace (prefixWord ++ tailWord_3009288) baseStart_3009288 baseEnd_3009288 := by
    simpa [prefixWord, tailWord_3009288, baseEnd_3009288] using wordTrace_append hprefix tailTrace_3009288
  have hstable : (prefixWord ++ tailWord_3009288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009288).length < 2 ^ (prefixWord ++ tailWord_3009288).sum := by decide
  have hdescent : baseEnd_3009288 < baseStart_3009288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009303 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3009303 : Nat := 118140960795 + 3009303 * 2 ^ 59
def prefixEnd_3009303 : Nat := 4983230072969 + 3 ^ 40 * 3009303 * 2
def baseEnd_3009303 : Nat := 1030145916011429881248649

theorem tailTrace_3009303 : CollatzResearch.WordTrace tailWord_3009303 prefixEnd_3009303 1030145916011429881248649 := by
  unfold tailWord_3009303
  simp only [CollatzResearch.WordTrace]
  refine ⟨109758297416816653880016563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73172198277877769253344375 109758297416816653880016563)
  ·
    refine ⟨164637446125224980820024845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109758297416816653880016563 164637446125224980820024845)
    ·
      refine ⟨61739042296959367807509317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164637446125224980820024845 61739042296959367807509317)
      ·
        refine ⟨11576070430679881463907997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61739042296959367807509317 11576070430679881463907997)
        ·
          refine ⟨4341026411504955548965499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11576070430679881463907997 4341026411504955548965499)
          ·
            refine ⟨6511539617257433323448249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341026411504955548965499 6511539617257433323448249)
            ·
              refine ⟨4883654712943074992586187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511539617257433323448249 4883654712943074992586187)
              ·
                refine ⟨7325482069414612488879281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883654712943074992586187 7325482069414612488879281)
                ·
                  refine ⟨5494111552060959366659461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7325482069414612488879281 5494111552060959366659461)
                  ·
                    refine ⟨1030145916011429881248649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494111552060959366659461 1030145916011429881248649)
                    ·
                      rfl

theorem cell22_3009303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3009303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009303 prefixEnd_3009303 := by exact prefixLift 3009303
  have htrace : WordTrace (prefixWord ++ tailWord_3009303) baseStart_3009303 baseEnd_3009303 := by
    simpa [prefixWord, tailWord_3009303, baseEnd_3009303] using wordTrace_append hprefix tailTrace_3009303
  have hstable : (prefixWord ++ tailWord_3009303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009303).length < 2 ^ (prefixWord ++ tailWord_3009303).sum := by decide
  have hdescent : baseEnd_3009303 < baseStart_3009303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009322 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3009322 : Nat := 118140960795 + 3009322 * 2 ^ 59
def prefixEnd_3009322 : Nat := 4983230072969 + 3 ^ 40 * 3009322 * 2
def baseEnd_3009322 : Nat := 1030152420099720165023591

theorem tailTrace_3009322 : CollatzResearch.WordTrace tailWord_3009322 prefixEnd_3009322 1030152420099720165023591 := by
  unfold tailWord_3009322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439747600936955031239555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73172660269165213416638813 27439747600936955031239555)
  ·
    refine ⟨41159621401405432546859333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27439747600936955031239555 41159621401405432546859333)
    ·
      refine ⟨7717429012763518602536125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41159621401405432546859333 7717429012763518602536125)
      ·
        refine ⟨2894035879786319475951047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7717429012763518602536125 2894035879786319475951047)
        ·
          refine ⟨4341053819679479213926571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894035879786319475951047 4341053819679479213926571)
          ·
            refine ⟨6511580729519218820889857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341053819679479213926571 6511580729519218820889857)
            ·
              refine ⟨4883685547139414115667393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511580729519218820889857 4883685547139414115667393)
              ·
                refine ⟨3662764160354560586750545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883685547139414115667393 3662764160354560586750545)
                ·
                  refine ⟨2747073120265920440062909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662764160354560586750545 2747073120265920440062909)
                  ·
                    refine ⟨1030152420099720165023591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747073120265920440062909 1030152420099720165023591)
                    ·
                      rfl

theorem cell22_3009322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3009322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009322 prefixEnd_3009322 := by exact prefixLift 3009322
  have htrace : WordTrace (prefixWord ++ tailWord_3009322) baseStart_3009322 baseEnd_3009322 := by
    simpa [prefixWord, tailWord_3009322, baseEnd_3009322] using wordTrace_append hprefix tailTrace_3009322
  have hstable : (prefixWord ++ tailWord_3009322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009322).length < 2 ^ (prefixWord ++ tailWord_3009322).sum := by decide
  have hdescent : baseEnd_3009322 < baseStart_3009322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009442 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3009442 : Nat := 118140960795 + 3009442 * 2 ^ 59
def prefixEnd_3009442 : Nat := 4983230072969 + 3 ^ 40 * 3009442 * 2
def baseEnd_3009442 : Nat := 343397832850693284007741

theorem tailTrace_3009442 : CollatzResearch.WordTrace tailWord_3009442 prefixEnd_3009442 343397832850693284007741 := by
  unfold tailWord_3009442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27440841790828270154831645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73175578108875387079551053 27440841790828270154831645)
  ·
    refine ⟨10290315671560601308061867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27440841790828270154831645 10290315671560601308061867)
    ·
      refine ⟨15435473507340901962092801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290315671560601308061867 15435473507340901962092801)
      ·
        refine ⟨11576605130505676471569601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15435473507340901962092801 11576605130505676471569601)
        ·
          refine ⟨8682453847879257353677201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11576605130505676471569601 8682453847879257353677201)
          ·
            refine ⟨6511840385909443015257901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682453847879257353677201 6511840385909443015257901)
            ·
              refine ⟨2441940144716041130721713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6511840385909443015257901 2441940144716041130721713)
              ·
                refine ⟨1831455108537030848041285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441940144716041130721713 1831455108537030848041285)
                ·
                  refine ⟨343397832850693284007741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831455108537030848041285 343397832850693284007741)
                  ·
                    rfl

theorem cell22_3009442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3009442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009442 prefixEnd_3009442 := by exact prefixLift 3009442
  have htrace : WordTrace (prefixWord ++ tailWord_3009442) baseStart_3009442 baseEnd_3009442 := by
    simpa [prefixWord, tailWord_3009442, baseEnd_3009442] using wordTrace_append hprefix tailTrace_3009442
  have hstable : (prefixWord ++ tailWord_3009442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009442).length < 2 ^ (prefixWord ++ tailWord_3009442).sum := by decide
  have hdescent : baseEnd_3009442 < baseStart_3009442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009478 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3009478 : Nat := 118140960795 + 3009478 * 2 ^ 59
def prefixEnd_3009478 : Nat := 4983230072969 + 3 ^ 40 * 3009478 * 2
def baseEnd_3009478 : Nat := 1030205822087787758123113

theorem tailTrace_3009478 : CollatzResearch.WordTrace tailWord_3009478 prefixEnd_3009478 1030205822087787758123113 := by
  unfold tailWord_3009478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430146255974458086488659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73176453460788439178424725 3430146255974458086488659)
  ·
    refine ⟨5145219383961687129732989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3430146255974458086488659 5145219383961687129732989)
    ·
      refine ⟨1929457268985632673649871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5145219383961687129732989 1929457268985632673649871)
      ·
        refine ⟨2894185903478449010474807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929457268985632673649871 2894185903478449010474807)
        ·
          refine ⟨4341278855217673515712211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894185903478449010474807 4341278855217673515712211)
          ·
            refine ⟨6511918282826510273568317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341278855217673515712211 6511918282826510273568317)
            ·
              refine ⟨2441969356059941352588119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6511918282826510273568317 2441969356059941352588119)
              ·
                refine ⟨3662954034089912028882179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441969356059941352588119 3662954034089912028882179)
                ·
                  refine ⟨5494431051134868043323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662954034089912028882179 5494431051134868043323269)
                  ·
                    refine ⟨1030205822087787758123113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494431051134868043323269 1030205822087787758123113)
                    ·
                      rfl

theorem cell22_3009478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3009478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009478 prefixEnd_3009478 := by exact prefixLift 3009478
  have htrace : WordTrace (prefixWord ++ tailWord_3009478) baseStart_3009478 baseEnd_3009478 := by
    simpa [prefixWord, tailWord_3009478, baseEnd_3009478] using wordTrace_append hprefix tailTrace_3009478
  have hstable : (prefixWord ++ tailWord_3009478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009478).length < 2 ^ (prefixWord ++ tailWord_3009478).sum := by decide
  have hdescent : baseEnd_3009478 < baseStart_3009478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009498 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_3009498 : Nat := 118140960795 + 3009498 * 2 ^ 59
def prefixEnd_3009498 : Nat := 4983230072969 + 3 ^ 40 * 3009498 * 2
def baseEnd_3009498 : Nat := 343404222832171457541017

theorem tailTrace_3009498 : CollatzResearch.WordTrace tailWord_3009498 prefixEnd_3009498 343404222832171457541017 := by
  unfold tailWord_3009498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27441352412777550545841287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73176939767406801455576765 27441352412777550545841287)
  ·
    refine ⟨41162028619166325818761931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27441352412777550545841287 41162028619166325818761931)
    ·
      refine ⟨61743042928749488728142897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41162028619166325818761931 61743042928749488728142897)
      ·
        refine ⟨46307282196562116546107173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61743042928749488728142897 46307282196562116546107173)
        ·
          refine ⟨8682615411855396852395095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46307282196562116546107173 8682615411855396852395095)
          ·
            refine ⟨13023923117783095278592643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682615411855396852395095 13023923117783095278592643)
            ·
              refine ⟨19535884676674642917888965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023923117783095278592643 19535884676674642917888965)
              ·
                refine ⟨3662978376876495547104181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19535884676674642917888965 3662978376876495547104181)
                ·
                  refine ⟨343404222832171457541017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662978376876495547104181 343404222832171457541017)
                  ·
                    rfl

theorem cell22_3009498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_3009498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009498 prefixEnd_3009498 := by exact prefixLift 3009498
  have htrace : WordTrace (prefixWord ++ tailWord_3009498) baseStart_3009498 baseEnd_3009498 := by
    simpa [prefixWord, tailWord_3009498, baseEnd_3009498] using wordTrace_append hprefix tailTrace_3009498
  have hstable : (prefixWord ++ tailWord_3009498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009498).length < 2 ^ (prefixWord ++ tailWord_3009498).sum := by decide
  have hdescent : baseEnd_3009498 < baseStart_3009498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009528 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_3009528 : Nat := 118140960795 + 3009528 * 2 ^ 59
def prefixEnd_3009528 : Nat := 4983230072969 + 3 ^ 40 * 3009528 * 2
def baseEnd_3009528 : Nat := 1030222938109604294372959

theorem tailTrace_3009528 : CollatzResearch.WordTrace tailWord_3009528 prefixEnd_3009528 1030222938109604294372959 := by
  unfold tailWord_3009528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54883251920500758653478619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73177669227334344871304825 54883251920500758653478619)
  ·
    refine ⟨82324877880751137980217929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54883251920500758653478619 82324877880751137980217929)
    ·
      refine ⟨61743658410563353485163447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82324877880751137980217929 61743658410563353485163447)
      ·
        refine ⟨92615487615845030227745171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61743658410563353485163447 92615487615845030227745171)
        ·
          refine ⟨138923231423767545341617757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92615487615845030227745171 138923231423767545341617757)
          ·
            refine ⟨52096211783912829503106659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138923231423767545341617757 52096211783912829503106659)
            ·
              refine ⟨78144317675869244254659989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52096211783912829503106659 78144317675869244254659989)
              ·
                refine ⟨3663014891056370824437187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78144317675869244254659989 3663014891056370824437187)
                ·
                  refine ⟨5494522336584556236655781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663014891056370824437187 5494522336584556236655781)
                  ·
                    refine ⟨1030222938109604294372959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494522336584556236655781 1030222938109604294372959)
                    ·
                      rfl

theorem cell22_3009528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_3009528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009528 prefixEnd_3009528 := by exact prefixLift 3009528
  have htrace : WordTrace (prefixWord ++ tailWord_3009528) baseStart_3009528 baseEnd_3009528 := by
    simpa [prefixWord, tailWord_3009528, baseEnd_3009528] using wordTrace_append hprefix tailTrace_3009528
  have hstable : (prefixWord ++ tailWord_3009528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009528).length < 2 ^ (prefixWord ++ tailWord_3009528).sum := by decide
  have hdescent : baseEnd_3009528 < baseStart_3009528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009560 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_3009560 : Nat := 118140960795 + 3009560 * 2 ^ 59
def prefixEnd_3009560 : Nat := 4983230072969 + 3 ^ 40 * 3009560 * 2
def baseEnd_3009560 : Nat := 343411297454522292524287

theorem tailTrace_3009560 : CollatzResearch.WordTrace tailWord_3009560 prefixEnd_3009560 343411297454522292524287 := by
  unfold tailWord_3009560
  simp only [CollatzResearch.WordTrace]
  refine ⟨54883835488442793386061067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73178447317923724514748089 54883835488442793386061067)
  ·
    refine ⟨82325753232664190079091601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54883835488442793386061067 82325753232664190079091601)
    ·
      refine ⟨61744314924498142559318701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82325753232664190079091601 61744314924498142559318701)
      ·
        refine ⟨23154118096686803459744513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61744314924498142559318701 23154118096686803459744513)
        ·
          refine ⟨17365588572515102594808385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23154118096686803459744513 17365588572515102594808385)
          ·
            refine ⟨13024191429386326946106289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17365588572515102594808385 13024191429386326946106289)
            ·
              refine ⟨9768143572039745209579717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13024191429386326946106289 9768143572039745209579717)
              ·
                refine ⟨1831526919757452226796197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9768143572039745209579717 1831526919757452226796197)
                ·
                  refine ⟨343411297454522292524287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831526919757452226796197 343411297454522292524287)
                  ·
                    rfl

theorem cell22_3009560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_3009560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009560 prefixEnd_3009560 := by exact prefixLift 3009560
  have htrace : WordTrace (prefixWord ++ tailWord_3009560) baseStart_3009560 baseEnd_3009560 := by
    simpa [prefixWord, tailWord_3009560, baseEnd_3009560] using wordTrace_append hprefix tailTrace_3009560
  have hstable : (prefixWord ++ tailWord_3009560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009560).length < 2 ^ (prefixWord ++ tailWord_3009560).sum := by decide
  have hdescent : baseEnd_3009560 < baseStart_3009560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009590 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3009590 : Nat := 118140960795 + 3009590 * 2 ^ 59
def prefixEnd_3009590 : Nat := 4983230072969 + 3 ^ 40 * 3009590 * 2
def baseEnd_3009590 : Nat := 1030244161976656799322769

theorem tailTrace_3009590 : CollatzResearch.WordTrace tailWord_3009590 prefixEnd_3009590 1030244161976656799322769 := by
  unfold tailWord_3009590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860547822923556368482139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73179176777851267930476149 6860547822923556368482139)
  ·
    refine ⟨10290821734385334552723209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860547822923556368482139 10290821734385334552723209)
    ·
      refine ⟨7718116300789000914542407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10290821734385334552723209 7718116300789000914542407)
      ·
        refine ⟨11577174451183501371813611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718116300789000914542407 11577174451183501371813611)
        ·
          refine ⟨17365761676775252057720417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11577174451183501371813611 17365761676775252057720417)
          ·
            refine ⟨13024321257581439043290313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17365761676775252057720417 13024321257581439043290313)
            ·
              refine ⟨9768240943186079282467735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13024321257581439043290313 9768240943186079282467735)
              ·
                refine ⟨14652361414779118923701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9768240943186079282467735 14652361414779118923701603)
                ·
                  refine ⟨21978542122168678385552405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14652361414779118923701603 21978542122168678385552405)
                  ·
                    refine ⟨1030244161976656799322769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21978542122168678385552405 1030244161976656799322769)
                    ·
                      rfl

theorem cell22_3009590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3009590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009590 prefixEnd_3009590 := by exact prefixLift 3009590
  have htrace : WordTrace (prefixWord ++ tailWord_3009590) baseStart_3009590 baseEnd_3009590 := by
    simpa [prefixWord, tailWord_3009590, baseEnd_3009590] using wordTrace_append hprefix tailTrace_3009590
  have hstable : (prefixWord ++ tailWord_3009590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009590).length < 2 ^ (prefixWord ++ tailWord_3009590).sum := by decide
  have hdescent : baseEnd_3009590 < baseStart_3009590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009654 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3009654 : Nat := 118140960795 + 3009654 * 2 ^ 59
def prefixEnd_3009654 : Nat := 4983230072969 + 3 ^ 40 * 3009654 * 2
def baseEnd_3009654 : Nat := 1030266070484581965722573

theorem tailTrace_3009654 : CollatzResearch.WordTrace tailWord_3009654 prefixEnd_3009654 1030266070484581965722573 := by
  unfold tailWord_3009654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860693714909065051627751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73180732959030027217362677 6860693714909065051627751)
  ·
    refine ⟨10291040572363597577441627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860693714909065051627751 10291040572363597577441627)
    ·
      refine ⟨15436560858545396366162441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291040572363597577441627 15436560858545396366162441)
      ·
        refine ⟨11577420643909047274621831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15436560858545396366162441 11577420643909047274621831)
        ·
          refine ⟨17366130965863570911932747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11577420643909047274621831 17366130965863570911932747)
          ·
            refine ⟨26049196448795356367899121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17366130965863570911932747 26049196448795356367899121)
            ·
              refine ⟨19536897336596517275924341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26049196448795356367899121 19536897336596517275924341)
              ·
                refine ⟨1831584125305923494617907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19536897336596517275924341 1831584125305923494617907)
                ·
                  refine ⟨2747376187958885241926861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831584125305923494617907 2747376187958885241926861)
                  ·
                    refine ⟨1030266070484581965722573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747376187958885241926861 1030266070484581965722573)
                    ·
                      rfl

theorem cell22_3009654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3009654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009654 prefixEnd_3009654 := by exact prefixLift 3009654
  have htrace : WordTrace (prefixWord ++ tailWord_3009654) baseStart_3009654 baseEnd_3009654 := by
    simpa [prefixWord, tailWord_3009654, baseEnd_3009654] using wordTrace_append hprefix tailTrace_3009654
  have hstable : (prefixWord ++ tailWord_3009654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009654).length < 2 ^ (prefixWord ++ tailWord_3009654).sum := by decide
  have hdescent : baseEnd_3009654 < baseStart_3009654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009714 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_3009714 : Nat := 118140960795 + 3009714 * 2 ^ 59
def prefixEnd_3009714 : Nat := 4983230072969 + 3 ^ 40 * 3009714 * 2
def baseEnd_3009714 : Nat := 1030286609710761809222389

theorem tailTrace_3009714 : CollatzResearch.WordTrace tailWord_3009714 prefixEnd_3009714 1030286609710761809222389 := by
  unfold tailWord_3009714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443321954581917768307049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73182191878885114048818797 27443321954581917768307049)
  ·
    refine ⟨20582491465936438326230287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27443321954581917768307049 20582491465936438326230287)
    ·
      refine ⟨30873737198904657489345431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582491465936438326230287 30873737198904657489345431)
      ·
        refine ⟨46310605798356986234018147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30873737198904657489345431 46310605798356986234018147)
        ·
          refine ⟨69465908697535479351027221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46310605798356986234018147 69465908697535479351027221)
          ·
            refine ⟨3256214470196975594579401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69465908697535479351027221 3256214470196975594579401)
            ·
              refine ⟨2442160852647731695934551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3256214470196975594579401 2442160852647731695934551)
              ·
                refine ⟨3663241278971597543901827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442160852647731695934551 3663241278971597543901827)
                ·
                  refine ⟨5494861918457396315852741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663241278971597543901827 5494861918457396315852741)
                  ·
                    refine ⟨1030286609710761809222389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494861918457396315852741 1030286609710761809222389)
                    ·
                      rfl

theorem cell22_3009714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_3009714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009714 prefixEnd_3009714 := by exact prefixLift 3009714
  have htrace : WordTrace (prefixWord ++ tailWord_3009714) baseStart_3009714 baseEnd_3009714 := by
    simpa [prefixWord, tailWord_3009714, baseEnd_3009714] using wordTrace_append hprefix tailTrace_3009714
  have hstable : (prefixWord ++ tailWord_3009714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009714).length < 2 ^ (prefixWord ++ tailWord_3009714).sum := by decide
  have hdescent : baseEnd_3009714 < baseStart_3009714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009718 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3009718 : Nat := 118140960795 + 3009718 * 2 ^ 59
def prefixEnd_3009718 : Nat := 4983230072969 + 3 ^ 40 * 3009718 * 2
def baseEnd_3009718 : Nat := 343429326330835710707459

theorem tailTrace_3009718 : CollatzResearch.WordTrace tailWord_3009718 prefixEnd_3009718 343429326330835710707459 := by
  unfold tailWord_3009718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860839606894573734773363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73182289140208786504249205 6860839606894573734773363)
  ·
    refine ⟨10291259410341860602160045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860839606894573734773363 10291259410341860602160045)
    ·
      refine ⟨3859222278878197725810017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10291259410341860602160045 3859222278878197725810017)
      ·
        refine ⟨2894416709158648294357513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3859222278878197725810017 2894416709158648294357513)
        ·
          refine ⟨2170812531868986220768135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894416709158648294357513 2170812531868986220768135)
          ·
            refine ⟨3256218797803479331152203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170812531868986220768135 3256218797803479331152203)
            ·
              refine ⟨4884328196705218996728305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256218797803479331152203 4884328196705218996728305)
              ·
                refine ⟨3663246147528914247546229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884328196705218996728305 3663246147528914247546229)
                ·
                  refine ⟨343429326330835710707459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663246147528914247546229 343429326330835710707459)
                  ·
                    rfl

theorem cell22_3009718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3009718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009718 prefixEnd_3009718 := by exact prefixLift 3009718
  have htrace : WordTrace (prefixWord ++ tailWord_3009718) baseStart_3009718 baseEnd_3009718 := by
    simpa [prefixWord, tailWord_3009718, baseEnd_3009718] using wordTrace_append hprefix tailTrace_3009718
  have hstable : (prefixWord ++ tailWord_3009718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009718).length < 2 ^ (prefixWord ++ tailWord_3009718).sum := by decide
  have hdescent : baseEnd_3009718 < baseStart_3009718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009725 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3009725 : Nat := 118140960795 + 3009725 * 2 ^ 59
def prefixEnd_3009725 : Nat := 4983230072969 + 3 ^ 40 * 3009725 * 2
def baseEnd_3009725 : Nat := 1030290375235561447197355

theorem tailTrace_3009725 : CollatzResearch.WordTrace tailWord_3009725 prefixEnd_3009725 1030290375235561447197355 := by
  unfold tailWord_3009725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109773689021287819951878629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73182459347525213301252419 109773689021287819951878629)
  ·
    refine ⟨20582566691491466240977243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109773689021287819951878629 20582566691491466240977243)
    ·
      refine ⟨30873850037237199361465865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582566691491466240977243 30873850037237199361465865)
      ·
        refine ⟨23155387527927899521099399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30873850037237199361465865 23155387527927899521099399)
        ·
          refine ⟨34733081291891849281649099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23155387527927899521099399 34733081291891849281649099)
          ·
            refine ⟨52099621937837773922473649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34733081291891849281649099 52099621937837773922473649)
            ·
              refine ⟨39074716453378330441855237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52099621937837773922473649 39074716453378330441855237)
              ·
                refine ⟨7326509335008436957847857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39074716453378330441855237 7326509335008436957847857)
                ·
                  refine ⟨5494882001256327718385893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7326509335008436957847857 5494882001256327718385893)
                  ·
                    refine ⟨1030290375235561447197355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494882001256327718385893 1030290375235561447197355)
                    ·
                      rfl

theorem cell22_3009725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3009725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009725 prefixEnd_3009725 := by exact prefixLift 3009725
  have htrace : WordTrace (prefixWord ++ tailWord_3009725) baseStart_3009725 baseEnd_3009725 := by
    simpa [prefixWord, tailWord_3009725, baseEnd_3009725] using wordTrace_append hprefix tailTrace_3009725
  have hstable : (prefixWord ++ tailWord_3009725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009725).length < 2 ^ (prefixWord ++ tailWord_3009725).sum := by decide
  have hdescent : baseEnd_3009725 < baseStart_3009725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009727 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 2, 3]
def baseStart_3009727 : Nat := 118140960795 + 3009727 * 2 ^ 59
def prefixEnd_3009727 : Nat := 4983230072969 + 3 ^ 40 * 3009727 * 2
def baseEnd_3009727 : Nat := 1030291059876434108647349

theorem tailTrace_3009727 : CollatzResearch.WordTrace tailWord_3009727 prefixEnd_3009727 1030291059876434108647349 := by
  unfold tailWord_3009727
  simp only [CollatzResearch.WordTrace]
  refine ⟨109773761967280574293451435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73182507978187049528967623 109773761967280574293451435)
  ·
    refine ⟨164660642950920861440177153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109773761967280574293451435 164660642950920861440177153)
    ·
      refine ⟨123495482213190646080132865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164660642950920861440177153 123495482213190646080132865)
      ·
        refine ⟨92621611659892984560099649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123495482213190646080132865 92621611659892984560099649)
        ·
          refine ⟨69466208744919738420074737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92621611659892984560099649 69466208744919738420074737)
          ·
            refine ⟨52099656558689803815056053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69466208744919738420074737 52099656558689803815056053)
            ·
              refine ⟨4884342802377169107661505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52099656558689803815056053 4884342802377169107661505)
              ·
                refine ⟨3663257101782876830746129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884342802377169107661505 3663257101782876830746129)
                ·
                  refine ⟨2747442826337157623059597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663257101782876830746129 2747442826337157623059597)
                  ·
                    refine ⟨1030291059876434108647349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747442826337157623059597 1030291059876434108647349)
                    ·
                      rfl

theorem cell22_3009727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_3009727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009727 prefixEnd_3009727 := by exact prefixLift 3009727
  have htrace : WordTrace (prefixWord ++ tailWord_3009727) baseStart_3009727 baseEnd_3009727 := by
    simpa [prefixWord, tailWord_3009727, baseEnd_3009727] using wordTrace_append hprefix tailTrace_3009727
  have hstable : (prefixWord ++ tailWord_3009727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009727).length < 2 ^ (prefixWord ++ tailWord_3009727).sum := by decide
  have hdescent : baseEnd_3009727 < baseStart_3009727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009729 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 4]
def baseStart_3009729 : Nat := 118140960795 + 3009729 * 2 ^ 59
def prefixEnd_3009729 : Nat := 4983230072969 + 3 ^ 40 * 3009729 * 2
def baseEnd_3009729 : Nat := 343430581505768923365781

theorem tailTrace_3009729 : CollatzResearch.WordTrace tailWord_3009729 prefixEnd_3009729 343430581505768923365781 := by
  unfold tailWord_3009729
  simp only [CollatzResearch.WordTrace]
  refine ⟨109773834913273328635024241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73182556608848885756682827 109773834913273328635024241)
  ·
    refine ⟨82330376184954996476268181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109773834913273328635024241 82330376184954996476268181)
    ·
      refine ⟨3859236383669765459825071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82330376184954996476268181 3859236383669765459825071)
      ·
        refine ⟨5788854575504648189737607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859236383669765459825071 5788854575504648189737607)
        ·
          refine ⟨8683281863256972284606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788854575504648189737607 8683281863256972284606411)
          ·
            refine ⟨13024922794885458426909617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8683281863256972284606411 13024922794885458426909617)
            ·
              refine ⟨9768692096164093820182213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13024922794885458426909617 9768692096164093820182213)
              ·
                refine ⟨1831629768030767591284165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9768692096164093820182213 1831629768030767591284165)
                ·
                  refine ⟨343430581505768923365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831629768030767591284165 343430581505768923365781)
                  ·
                    rfl

theorem cell22_3009729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_3009729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009729 prefixEnd_3009729 := by exact prefixLift 3009729
  have htrace : WordTrace (prefixWord ++ tailWord_3009729) baseStart_3009729 baseEnd_3009729 := by
    simpa [prefixWord, tailWord_3009729, baseEnd_3009729] using wordTrace_append hprefix tailTrace_3009729
  have hstable : (prefixWord ++ tailWord_3009729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009729).length < 2 ^ (prefixWord ++ tailWord_3009729).sum := by decide
  have hdescent : baseEnd_3009729 < baseStart_3009729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009757 : List Nat := [1, 4, 3, 2, 2, 1, 1, 8]
def baseStart_3009757 : Nat := 118140960795 + 3009757 * 2 ^ 59
def prefixEnd_3009757 : Nat := 4983230072969 + 3 ^ 40 * 3009757 * 2
def baseEnd_3009757 : Nat := 114477925498836003377473

theorem tailTrace_3009757 : CollatzResearch.WordTrace tailWord_3009757 prefixEnd_3009757 114477925498836003377473 := by
  unfold tailWord_3009757
  simp only [CollatzResearch.WordTrace]
  refine ⟨109774856157171889417043525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73183237438114592944695683 109774856157171889417043525)
  ·
    refine ⟨20582785529469729265695661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109774856157171889417043525 20582785529469729265695661)
    ·
      refine ⟨7718544573551148474635873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20582785529469729265695661 7718544573551148474635873)
      ·
        refine ⟨5788908430163361355976905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7718544573551148474635873 5788908430163361355976905)
        ·
          refine ⟨4341681322622521016982679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788908430163361355976905 4341681322622521016982679)
          ·
            refine ⟨6512521983933781525474019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341681322622521016982679 6512521983933781525474019)
            ·
              refine ⟨9768782975900672288211029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512521983933781525474019 9768782975900672288211029)
              ·
                refine ⟨114477925498836003377473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9768782975900672288211029 114477925498836003377473)
                ·
                  rfl

theorem cell22_3009757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 8].length) (baseStart_3009757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009757 prefixEnd_3009757 := by exact prefixLift 3009757
  have htrace : WordTrace (prefixWord ++ tailWord_3009757) baseStart_3009757 baseEnd_3009757 := by
    simpa [prefixWord, tailWord_3009757, baseEnd_3009757] using wordTrace_append hprefix tailTrace_3009757
  have hstable : (prefixWord ++ tailWord_3009757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009757).length < 2 ^ (prefixWord ++ tailWord_3009757).sum := by decide
  have hdescent : baseEnd_3009757 < baseStart_3009757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009780 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3009780 : Nat := 118140960795 + 3009780 * 2 ^ 59
def prefixEnd_3009780 : Nat := 4983230072969 + 3 ^ 40 * 3009780 * 2
def baseEnd_3009780 : Nat := 343436400953186545690729

theorem tailTrace_3009780 : CollatzResearch.WordTrace tailWord_3009780 prefixEnd_3009780 343436400953186545690729 := by
  unfold tailWord_3009780
  simp only [CollatzResearch.WordTrace]
  refine ⟨54887847518044282172565397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73183796690725709563420529 54887847518044282172565397)
  ·
    refine ⟨2572867852408325726839003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54887847518044282172565397 2572867852408325726839003)
    ·
      refine ⟨3859301778612488590258505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572867852408325726839003 3859301778612488590258505)
      ·
        refine ⟨2894476333959366442693879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3859301778612488590258505 2894476333959366442693879)
        ·
          refine ⟨4341714500939049664040819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894476333959366442693879 4341714500939049664040819)
          ·
            refine ⟨6512571751408574496061229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341714500939049664040819 6512571751408574496061229)
            ·
              refine ⟨2442214406778215436022961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6512571751408574496061229 2442214406778215436022961)
              ·
                refine ⟨1831660805083661577017221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442214406778215436022961 1831660805083661577017221)
                ·
                  refine ⟨343436400953186545690729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831660805083661577017221 343436400953186545690729)
                  ·
                    rfl

theorem cell22_3009780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3009780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009780 prefixEnd_3009780 := by exact prefixLift 3009780
  have htrace : WordTrace (prefixWord ++ tailWord_3009780) baseStart_3009780 baseEnd_3009780 := by
    simpa [prefixWord, tailWord_3009780, baseEnd_3009780] using wordTrace_append hprefix tailTrace_3009780
  have hstable : (prefixWord ++ tailWord_3009780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009780).length < 2 ^ (prefixWord ++ tailWord_3009780).sum := by decide
  have hdescent : baseEnd_3009780 < baseStart_3009780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009785 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 5]
def baseStart_3009785 : Nat := 118140960795 + 3009785 * 2 ^ 59
def prefixEnd_3009785 : Nat := 4983230072969 + 3 ^ 40 * 3009785 * 2
def baseEnd_3009785 : Nat := 343436971487247096899057

theorem tailTrace_3009785 : CollatzResearch.WordTrace tailWord_3009785 prefixEnd_3009785 343436971487247096899057 := by
  unfold tailWord_3009785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109775877401070450199062809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73183918267380300132708539 109775877401070450199062809)
  ·
    refine ⟨82331908050802837649297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109775877401070450199062809 82331908050802837649297107)
    ·
      refine ⟨123497862076204256473945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82331908050802837649297107 123497862076204256473945661)
      ·
        refine ⟨46311698278576596177729623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123497862076204256473945661 46311698278576596177729623)
        ·
          refine ⟨69467547417864894266594435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46311698278576596177729623 69467547417864894266594435)
          ·
            refine ⟨104201321126797341399891653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69467547417864894266594435 104201321126797341399891653)
            ·
              refine ⟨19537747711274501512479685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104201321126797341399891653 19537747711274501512479685)
              ·
                refine ⟨3663327695863969033589941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19537747711274501512479685 3663327695863969033589941)
                ·
                  refine ⟨343436971487247096899057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663327695863969033589941 343436971487247096899057)
                  ·
                    rfl

theorem cell22_3009785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_3009785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009785 prefixEnd_3009785 := by exact prefixLift 3009785
  have htrace : WordTrace (prefixWord ++ tailWord_3009785) baseStart_3009785 baseEnd_3009785 := by
    simpa [prefixWord, tailWord_3009785, baseEnd_3009785] using wordTrace_append hprefix tailTrace_3009785
  have hstable : (prefixWord ++ tailWord_3009785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009785).length < 2 ^ (prefixWord ++ tailWord_3009785).sum := by decide
  have hdescent : baseEnd_3009785 < baseStart_3009785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009877 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3009877 : Nat := 118140960795 + 3009877 * 2 ^ 59
def prefixEnd_3009877 : Nat := 4983230072969 + 3 ^ 40 * 3009877 * 2
def baseEnd_3009877 : Nat := 1030342407941883717396889

theorem tailTrace_3009877 : CollatzResearch.WordTrace tailWord_3009877 prefixEnd_3009877 1030342407941883717396889 := by
  unfold tailWord_3009877
  simp only [CollatzResearch.WordTrace]
  refine ⟨109779232916737149911411885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73186155277824766607607923 109779232916737149911411885)
  ·
    refine ⟨41167212343776431216779457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109779232916737149911411885 41167212343776431216779457)
    ·
      refine ⟨30875409257832323412584593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41167212343776431216779457 30875409257832323412584593)
      ·
        refine ⟨23156556943374242559438445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30875409257832323412584593 23156556943374242559438445)
        ·
          refine ⟨8683708853765340959789417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23156556943374242559438445 8683708853765340959789417)
          ·
            refine ⟨6512781640324005719842063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8683708853765340959789417 6512781640324005719842063)
            ·
              refine ⟨9769172460486008579763095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512781640324005719842063 9769172460486008579763095)
              ·
                refine ⟨14653758690729012869644643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9769172460486008579763095 14653758690729012869644643)
                ·
                  refine ⟨21980638036093519304466965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14653758690729012869644643 21980638036093519304466965)
                  ·
                    refine ⟨1030342407941883717396889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21980638036093519304466965 1030342407941883717396889)
                    ·
                      rfl

theorem cell22_3009877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3009877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009877 prefixEnd_3009877 := by exact prefixLift 3009877
  have htrace : WordTrace (prefixWord ++ tailWord_3009877) baseStart_3009877 baseEnd_3009877 := by
    simpa [prefixWord, tailWord_3009877, baseEnd_3009877] using wordTrace_append hprefix tailTrace_3009877
  have hstable : (prefixWord ++ tailWord_3009877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009877).length < 2 ^ (prefixWord ++ tailWord_3009877).sum := by decide
  have hdescent : baseEnd_3009877 < baseStart_3009877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009905 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3009905 : Nat := 118140960795 + 3009905 * 2 ^ 59
def prefixEnd_3009905 : Nat := 4983230072969 + 3 ^ 40 * 3009905 * 2
def baseEnd_3009905 : Nat := 1030351992914100977696803

theorem tailTrace_3009905 : CollatzResearch.WordTrace tailWord_3009905 prefixEnd_3009905 1030351992914100977696803 := by
  unfold tailWord_3009905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109780254160635710693431169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73186836107090473795620779 109780254160635710693431169)
  ·
    refine ⟨82335190620476783020073377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109780254160635710693431169 82335190620476783020073377)
    ·
      refine ⟨61751392965357587265055033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82335190620476783020073377 61751392965357587265055033)
      ·
        refine ⟨46313544724018190448791275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61751392965357587265055033 46313544724018190448791275)
        ·
          refine ⟨69470317086027285673186913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46313544724018190448791275 69470317086027285673186913)
          ·
            refine ⟨52102737814520464254890185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69470317086027285673186913 52102737814520464254890185)
            ·
              refine ⟨39077053360890348191167639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52102737814520464254890185 39077053360890348191167639)
              ·
                refine ⟨58615580041335522286751459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39077053360890348191167639 58615580041335522286751459)
                ·
                  refine ⟨87923370062003283430127189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58615580041335522286751459 87923370062003283430127189)
                  ·
                    refine ⟨1030351992914100977696803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87923370062003283430127189 1030351992914100977696803)
                    ·
                      rfl

theorem cell22_3009905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3009905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009905 prefixEnd_3009905 := by exact prefixLift 3009905
  have htrace : WordTrace (prefixWord ++ tailWord_3009905) baseStart_3009905 baseEnd_3009905 := by
    simpa [prefixWord, tailWord_3009905, baseEnd_3009905] using wordTrace_append hprefix tailTrace_3009905
  have hstable : (prefixWord ++ tailWord_3009905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009905).length < 2 ^ (prefixWord ++ tailWord_3009905).sum := by decide
  have hdescent : baseEnd_3009905 < baseStart_3009905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009924 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_3009924 : Nat := 118140960795 + 3009924 * 2 ^ 59
def prefixEnd_3009924 : Nat := 4983230072969 + 3 ^ 40 * 3009924 * 2
def baseEnd_3009924 : Nat := 1030358497002391261471745

theorem tailTrace_3009924 : CollatzResearch.WordTrace tailWord_3009924 prefixEnd_3009924 1030358497002391261471745 := by
  unfold tailWord_3009924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54890473573783438469186413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73187298098377917958915217 54890473573783438469186413)
  ·
    refine ⟨20583927590168789425944905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54890473573783438469186413 20583927590168789425944905)
    ·
      refine ⟨15437945692626592069458679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20583927590168789425944905 15437945692626592069458679)
      ·
        refine ⟨23156918538939888104188019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15437945692626592069458679 23156918538939888104188019)
        ·
          refine ⟨34735377808409832156282029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23156918538939888104188019 34735377808409832156282029)
          ·
            refine ⟨13025766678153687058605761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34735377808409832156282029 13025766678153687058605761)
            ·
              refine ⟨9769325008615265293954321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13025766678153687058605761 9769325008615265293954321)
              ·
                refine ⟨7326993756461448970465741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9769325008615265293954321 7326993756461448970465741)
                ·
                  refine ⟨2747622658673043363924653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7326993756461448970465741 2747622658673043363924653)
                  ·
                    refine ⟨1030358497002391261471745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747622658673043363924653 1030358497002391261471745)
                    ·
                      rfl

theorem cell22_3009924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_3009924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009924 prefixEnd_3009924 := by exact prefixLift 3009924
  have htrace : WordTrace (prefixWord ++ tailWord_3009924) baseStart_3009924 baseEnd_3009924 := by
    simpa [prefixWord, tailWord_3009924, baseEnd_3009924] using wordTrace_append hprefix tailTrace_3009924
  have hstable : (prefixWord ++ tailWord_3009924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009924).length < 2 ^ (prefixWord ++ tailWord_3009924).sum := by decide
  have hdescent : baseEnd_3009924 < baseStart_3009924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009941 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_3009941 : Nat := 118140960795 + 3009941 * 2 ^ 59
def prefixEnd_3009941 : Nat := 4983230072969 + 3 ^ 40 * 3009941 * 2
def baseEnd_3009941 : Nat := 1030364316449808883796693

theorem tailTrace_3009941 : CollatzResearch.WordTrace tailWord_3009941 prefixEnd_3009941 1030364316449808883796693 := by
  unfold tailWord_3009941
  simp only [CollatzResearch.WordTrace]
  refine ⟨109781567188505288841741677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73187711459003525894494451 109781567188505288841741677)
  ·
    refine ⟨41168087695689483315653129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109781567188505288841741677 41168087695689483315653129)
    ·
      refine ⟨30876065771767112486739847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41168087695689483315653129 30876065771767112486739847)
      ·
        refine ⟨46314098657650668730109771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30876065771767112486739847 46314098657650668730109771)
        ·
          refine ⟨69471147986476003095164657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46314098657650668730109771 69471147986476003095164657)
          ·
            refine ⟨52103360989857002321373493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69471147986476003095164657 52103360989857002321373493)
            ·
              refine ⟨4884690092799093967628765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52103360989857002321373493 4884690092799093967628765)
              ·
                refine ⟨1831758784799660237860787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4884690092799093967628765 1831758784799660237860787)
                ·
                  refine ⟨2747638177199490356791181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831758784799660237860787 2747638177199490356791181)
                  ·
                    refine ⟨1030364316449808883796693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747638177199490356791181 1030364316449808883796693)
                    ·
                      rfl

theorem cell22_3009941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_3009941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009941 prefixEnd_3009941 := by exact prefixLift 3009941
  have htrace : WordTrace (prefixWord ++ tailWord_3009941) baseStart_3009941 baseEnd_3009941 := by
    simpa [prefixWord, tailWord_3009941, baseEnd_3009941] using wordTrace_append hprefix tailTrace_3009941
  have hstable : (prefixWord ++ tailWord_3009941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009941).length < 2 ^ (prefixWord ++ tailWord_3009941).sum := by decide
  have hdescent : baseEnd_3009941 < baseStart_3009941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009982 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3009982 : Nat := 118140960795 + 3009982 * 2 ^ 59
def prefixEnd_3009982 : Nat := 4983230072969 + 3 ^ 40 * 3009982 * 2
def baseEnd_3009982 : Nat := 343459450529232814507189

theorem tailTrace_3009982 : CollatzResearch.WordTrace tailWord_3009982 prefixEnd_3009982 343459450529232814507189 := by
  unfold tailWord_3009982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722882822669594105498025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73188708387571168562656133 13722882822669594105498025)
  ·
    refine ⟨10292162117002195579123519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13722882822669594105498025 10292162117002195579123519)
    ·
      refine ⟨15438243175503293368685279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292162117002195579123519 15438243175503293368685279)
      ·
        refine ⟨23157364763254940053027919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438243175503293368685279 23157364763254940053027919)
        ·
          refine ⟨34736047144882410079541879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23157364763254940053027919 34736047144882410079541879)
          ·
            refine ⟨52104070717323615119312819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34736047144882410079541879 52104070717323615119312819)
            ·
              refine ⟨78156106075985422678969229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52104070717323615119312819 78156106075985422678969229)
              ·
                refine ⟨29308539778494533504613461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78156106075985422678969229 29308539778494533504613461)
                ·
                  refine ⟨343459450529232814507189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29308539778494533504613461 343459450529232814507189)
                  ·
                    rfl

theorem cell22_3009982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3009982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009982 prefixEnd_3009982 := by exact prefixLift 3009982
  have htrace : WordTrace (prefixWord ++ tailWord_3009982) baseStart_3009982 baseEnd_3009982 := by
    simpa [prefixWord, tailWord_3009982, baseEnd_3009982] using wordTrace_append hprefix tailTrace_3009982
  have hstable : (prefixWord ++ tailWord_3009982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009982).length < 2 ^ (prefixWord ++ tailWord_3009982).sum := by decide
  have hdescent : baseEnd_3009982 < baseStart_3009982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009984 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_3009984 : Nat := 118140960795 + 3009984 * 2 ^ 59
def prefixEnd_3009984 : Nat := 4983230072969 + 3 ^ 40 * 3009984 * 2
def baseEnd_3009984 : Nat := 1030379036228571104971561

theorem tailTrace_3009984 : CollatzResearch.WordTrace tailWord_3009984 prefixEnd_3009984 1030379036228571104971561 := by
  unfold tailWord_3009984
  simp only [CollatzResearch.WordTrace]
  refine ⟨54891567763674753592778503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73188757018233004790371337 54891567763674753592778503)
  ·
    refine ⟨82337351645512130389167755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54891567763674753592778503 82337351645512130389167755)
    ·
      refine ⟨123506027468268195583751633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82337351645512130389167755 123506027468268195583751633)
      ·
        refine ⟨92629520601201146687813725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123506027468268195583751633 92629520601201146687813725)
        ·
          refine ⟨34736070225450430007930147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92629520601201146687813725 34736070225450430007930147)
          ·
            refine ⟨52104105338175645011895221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34736070225450430007930147 52104105338175645011895221)
            ·
              refine ⟨4884759875453966719865177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52104105338175645011895221 4884759875453966719865177)
              ·
                refine ⟨3663569906590475039898883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884759875453966719865177 3663569906590475039898883)
                ·
                  refine ⟨5495354859885712559848325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663569906590475039898883 5495354859885712559848325)
                  ·
                    refine ⟨1030379036228571104971561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495354859885712559848325 1030379036228571104971561)
                    ·
                      rfl

theorem cell22_3009984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_3009984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3009984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3009984 prefixEnd_3009984 := by exact prefixLift 3009984
  have htrace : WordTrace (prefixWord ++ tailWord_3009984) baseStart_3009984 baseEnd_3009984 := by
    simpa [prefixWord, tailWord_3009984, baseEnd_3009984] using wordTrace_append hprefix tailTrace_3009984
  have hstable : (prefixWord ++ tailWord_3009984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009984).length < 2 ^ (prefixWord ++ tailWord_3009984).sum := by decide
  have hdescent : baseEnd_3009984 < baseStart_3009984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010076 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3010076 : Nat := 118140960795 + 3010076 * 2 ^ 59
def prefixEnd_3010076 : Nat := 4983230072969 + 3 ^ 40 * 3010076 * 2
def baseEnd_3010076 : Nat := 1030410529708713531671279

theorem tailTrace_3010076 : CollatzResearch.WordTrace tailWord_3010076 prefixEnd_3010076 1030410529708713531671279 := by
  unfold tailWord_3010076
  simp only [CollatzResearch.WordTrace]
  refine ⟨54893245521508103448953041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73190994028677471265270721 54893245521508103448953041)
  ·
    refine ⟨41169934141131077586714781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54893245521508103448953041 41169934141131077586714781)
    ·
      refine ⟨15438725302924154095018043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41169934141131077586714781 15438725302924154095018043)
      ·
        refine ⟨23158087954386231142527065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438725302924154095018043 23158087954386231142527065)
        ·
          refine ⟨17368565965789673356895299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23158087954386231142527065 17368565965789673356895299)
          ·
            refine ⟨26052848948684510035342949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17368565965789673356895299 26052848948684510035342949)
            ·
              refine ⟨4884909177878345631626803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26052848948684510035342949 4884909177878345631626803)
              ·
                refine ⟨7327363766817518447440205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884909177878345631626803 7327363766817518447440205)
                ·
                  refine ⟨2747761412556569417790077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7327363766817518447440205 2747761412556569417790077)
                  ·
                    refine ⟨1030410529708713531671279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747761412556569417790077 1030410529708713531671279)
                    ·
                      rfl

theorem cell22_3010076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3010076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010076 prefixEnd_3010076 := by exact prefixLift 3010076
  have htrace : WordTrace (prefixWord ++ tailWord_3010076) baseStart_3010076 baseEnd_3010076 := by
    simpa [prefixWord, tailWord_3010076, baseEnd_3010076] using wordTrace_append hprefix tailTrace_3010076
  have hstable : (prefixWord ++ tailWord_3010076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010076).length < 2 ^ (prefixWord ++ tailWord_3010076).sum := by decide
  have hdescent : baseEnd_3010076 < baseStart_3010076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010166 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3010166 : Nat := 118140960795 + 3010166 * 2 ^ 59
def prefixEnd_3010166 : Nat := 4983230072969 + 3 ^ 40 * 3010166 * 2
def baseEnd_3010166 : Nat := 1030441338547983296921003

theorem tailTrace_3010166 : CollatzResearch.WordTrace tailWord_3010166 prefixEnd_3010166 1030441338547983296921003 := by
  unfold tailWord_3010166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861860850793134516792647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73193182408460101512454901 6861860850793134516792647)
  ·
    refine ⟨10292791276189701775188971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6861860850793134516792647 10292791276189701775188971)
    ·
      refine ⟨15439186914284552662783457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292791276189701775188971 15439186914284552662783457)
      ·
        refine ⟨11579390185713414497087593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15439186914284552662783457 11579390185713414497087593)
        ·
          refine ⟨8684542639285060872815695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579390185713414497087593 8684542639285060872815695)
          ·
            refine ⟨13026813958927591309223543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684542639285060872815695 13026813958927591309223543)
            ·
              refine ⟨19540220938391386963835315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13026813958927591309223543 19540220938391386963835315)
              ·
                refine ⟨29310331407587080445752973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19540220938391386963835315 29310331407587080445752973)
                ·
                  refine ⟨10991374277845155167157365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29310331407587080445752973 10991374277845155167157365)
                  ·
                    refine ⟨1030441338547983296921003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10991374277845155167157365 1030441338547983296921003)
                    ·
                      rfl

theorem cell22_3010166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3010166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010166 prefixEnd_3010166 := by exact prefixLift 3010166
  have htrace : WordTrace (prefixWord ++ tailWord_3010166) baseStart_3010166 baseEnd_3010166 := by
    simpa [prefixWord, tailWord_3010166, baseEnd_3010166] using wordTrace_append hprefix tailTrace_3010166
  have hstable : (prefixWord ++ tailWord_3010166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010166).length < 2 ^ (prefixWord ++ tailWord_3010166).sum := by decide
  have hdescent : baseEnd_3010166 < baseStart_3010166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010183 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3010183 : Nat := 118140960795 + 3010183 * 2 ^ 59
def prefixEnd_3010183 : Nat := 4983230072969 + 3 ^ 40 * 3010183 * 2
def baseEnd_3010183 : Nat := 1030447157995400919245951

theorem tailTrace_3010183 : CollatzResearch.WordTrace tailWord_3010183 prefixEnd_3010183 1030447157995400919245951 := by
  unfold tailWord_3010183
  simp only [CollatzResearch.WordTrace]
  refine ⟨109790393653628564172051203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73193595769085709448034135 109790393653628564172051203)
  ·
    refine ⟨164685590480442846258076805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109790393653628564172051203 164685590480442846258076805)
    ·
      refine ⟨30878548215083033673389401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164685590480442846258076805 30878548215083033673389401)
      ·
        refine ⟨23158911161312275255042051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30878548215083033673389401 23158911161312275255042051)
        ·
          refine ⟨34738366741968412882563077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23158911161312275255042051 34738366741968412882563077)
          ·
            refine ⟨6513443764119077415480577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34738366741968412882563077 6513443764119077415480577)
            ·
              refine ⟨4885082823089308061610433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513443764119077415480577 4885082823089308061610433)
              ·
                refine ⟨3663812117316981046207825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885082823089308061610433 3663812117316981046207825)
                ·
                  refine ⟨2747859087987735784655869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663812117316981046207825 2747859087987735784655869)
                  ·
                    refine ⟨1030447157995400919245951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747859087987735784655869 1030447157995400919245951)
                    ·
                      rfl

theorem cell22_3010183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3010183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010183 prefixEnd_3010183 := by exact prefixLift 3010183
  have htrace : WordTrace (prefixWord ++ tailWord_3010183) baseStart_3010183 baseEnd_3010183 := by
    simpa [prefixWord, tailWord_3010183, baseEnd_3010183] using wordTrace_append hprefix tailTrace_3010183
  have hstable : (prefixWord ++ tailWord_3010183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010183).length < 2 ^ (prefixWord ++ tailWord_3010183).sum := by decide
  have hdescent : baseEnd_3010183 < baseStart_3010183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010211 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 3, 3]
def baseStart_3010211 : Nat := 118140960795 + 3010211 * 2 ^ 59
def prefixEnd_3010211 : Nat := 4983230072969 + 3 ^ 40 * 3010211 * 2
def baseEnd_3010211 : Nat := 1030456742967618179545865

theorem tailTrace_3010211 : CollatzResearch.WordTrace tailWord_3010211 prefixEnd_3010211 1030456742967618179545865 := by
  unfold tailWord_3010211
  simp only [CollatzResearch.WordTrace]
  refine ⟨109791414897527124954070487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73194276598351416636046991 109791414897527124954070487)
  ·
    refine ⟨164687122346290687431105731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109791414897527124954070487 164687122346290687431105731)
    ·
      refine ⟨247030683519436031146658597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164687122346290687431105731 247030683519436031146658597)
      ·
        refine ⟨46318253159894255839998487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247030683519436031146658597 46318253159894255839998487)
        ·
          refine ⟨69477379739841383759997731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46318253159894255839998487 69477379739841383759997731)
          ·
            refine ⟨104216069609762075639996597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69477379739841383759997731 104216069609762075639996597)
            ·
              refine ⟨9770256525915194591249681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104216069609762075639996597 9770256525915194591249681)
              ·
                refine ⟨7327692394436395943437261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770256525915194591249681 7327692394436395943437261)
                ·
                  refine ⟨2747884647913648478788973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7327692394436395943437261 2747884647913648478788973)
                  ·
                    refine ⟨1030456742967618179545865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747884647913648478788973 1030456742967618179545865)
                    ·
                      rfl

theorem cell22_3010211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].length) (baseStart_3010211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010211 prefixEnd_3010211 := by exact prefixLift 3010211
  have htrace : WordTrace (prefixWord ++ tailWord_3010211) baseStart_3010211 baseEnd_3010211 := by
    simpa [prefixWord, tailWord_3010211, baseEnd_3010211] using wordTrace_append hprefix tailTrace_3010211
  have hstable : (prefixWord ++ tailWord_3010211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010211).length < 2 ^ (prefixWord ++ tailWord_3010211).sum := by decide
  have hdescent : baseEnd_3010211 < baseStart_3010211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010239 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3010239 : Nat := 118140960795 + 3010239 * 2 ^ 59
def prefixEnd_3010239 : Nat := 4983230072969 + 3 ^ 40 * 3010239 * 2
def baseEnd_3010239 : Nat := 1030466327939835439845779

theorem tailTrace_3010239 : CollatzResearch.WordTrace tailWord_3010239 prefixEnd_3010239 1030466327939835439845779 := by
  unfold tailWord_3010239
  simp only [CollatzResearch.WordTrace]
  refine ⟨109792436141425685736089771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73194957427617123824059847 109792436141425685736089771)
  ·
    refine ⟨164688654212138528604134657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109792436141425685736089771 164688654212138528604134657)
    ·
      refine ⟨123516490659103896453100993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164688654212138528604134657 123516490659103896453100993)
      ·
        refine ⟨92637367994327922339825745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123516490659103896453100993 92637367994327922339825745)
        ·
          refine ⟨69478025995745941754869309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92637367994327922339825745 69478025995745941754869309)
          ·
            refine ⟨26054259748404728158075991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69478025995745941754869309 26054259748404728158075991)
            ·
              refine ⟨39081389622607092237113987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26054259748404728158075991 39081389622607092237113987)
              ·
                refine ⟨58622084433910638355670981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39081389622607092237113987 58622084433910638355670981)
                ·
                  refine ⟨10991640831358244691688309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58622084433910638355670981 10991640831358244691688309)
                  ·
                    refine ⟨1030466327939835439845779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10991640831358244691688309 1030466327939835439845779)
                    ·
                      rfl

theorem cell22_3010239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3010239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010239 prefixEnd_3010239 := by exact prefixLift 3010239
  have htrace : WordTrace (prefixWord ++ tailWord_3010239) baseStart_3010239 baseEnd_3010239 := by
    simpa [prefixWord, tailWord_3010239, baseEnd_3010239] using wordTrace_append hprefix tailTrace_3010239
  have hstable : (prefixWord ++ tailWord_3010239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010239).length < 2 ^ (prefixWord ++ tailWord_3010239).sum := by decide
  have hdescent : baseEnd_3010239 < baseStart_3010239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010279 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3010279 : Nat := 118140960795 + 3010279 * 2 ^ 59
def prefixEnd_3010279 : Nat := 4983230072969 + 3 ^ 40 * 3010279 * 2
def baseEnd_3010279 : Nat := 1030480020757288668845657

theorem tailTrace_3010279 : CollatzResearch.WordTrace tailWord_3010279 prefixEnd_3010279 1030480020757288668845657 := by
  unfold tailWord_3010279
  simp only [CollatzResearch.WordTrace]
  refine ⟨109793895061280772567545891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73195930040853848378363927 109793895061280772567545891)
  ·
    refine ⟨164690842591921158851318837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109793895061280772567545891 164690842591921158851318837)
    ·
      refine ⟨15439766492992608642311141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164690842591921158851318837 15439766492992608642311141)
      ·
        refine ⟨2894956217436114120433339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15439766492992608642311141 2894956217436114120433339)
        ·
          refine ⟨4342434326154171180650009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894956217436114120433339 4342434326154171180650009)
          ·
            refine ⟨3256825744615628385487507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342434326154171180650009 3256825744615628385487507)
            ·
              refine ⟨4885238616923442578231261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256825744615628385487507 4885238616923442578231261)
              ·
                refine ⟨1831964481346290966836723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4885238616923442578231261 1831964481346290966836723)
                ·
                  refine ⟨2747946722019436450255085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831964481346290966836723 2747946722019436450255085)
                  ·
                    refine ⟨1030480020757288668845657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747946722019436450255085 1030480020757288668845657)
                    ·
                      rfl

theorem cell22_3010279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3010279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010279 prefixEnd_3010279 := by exact prefixLift 3010279
  have htrace : WordTrace (prefixWord ++ tailWord_3010279) baseStart_3010279 baseEnd_3010279 := by
    simpa [prefixWord, tailWord_3010279, baseEnd_3010279] using wordTrace_append hprefix tailTrace_3010279
  have hstable : (prefixWord ++ tailWord_3010279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010279).length < 2 ^ (prefixWord ++ tailWord_3010279).sum := by decide
  have hdescent : baseEnd_3010279 < baseStart_3010279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010299 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_3010299 : Nat := 118140960795 + 3010299 * 2 ^ 59
def prefixEnd_3010299 : Nat := 4983230072969 + 3 ^ 40 * 3010299 * 2
def baseEnd_3010299 : Nat := 1030486867166015283345595

theorem tailTrace_3010299 : CollatzResearch.WordTrace tailWord_3010299 prefixEnd_3010299 1030486867166015283345595 := by
  unfold tailWord_3010299
  simp only [CollatzResearch.WordTrace]
  refine ⟨109794624521208315983273951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73196416347472210655515967 109794624521208315983273951)
  ·
    refine ⟨164691936781812473974910927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109794624521208315983273951 164691936781812473974910927)
    ·
      refine ⟨247037905172718710962366391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164691936781812473974910927 247037905172718710962366391)
      ·
        refine ⟨370556857759078066443549587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247037905172718710962366391 370556857759078066443549587)
        ·
          refine ⟨555835286638617099665324381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370556857759078066443549587 555835286638617099665324381)
          ·
            refine ⟨208438232489481412374496643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555835286638617099665324381 208438232489481412374496643)
            ·
              refine ⟨312657348734222118561744965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208438232489481412374496643 312657348734222118561744965)
              ·
                refine ⟨58623252887666647230327181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312657348734222118561744965 58623252887666647230327181)
                ·
                  refine ⟨21983719832874992711372693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58623252887666647230327181 21983719832874992711372693)
                  ·
                    refine ⟨1030486867166015283345595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21983719832874992711372693 1030486867166015283345595)
                    ·
                      rfl

theorem cell22_3010299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_3010299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010299 prefixEnd_3010299 := by exact prefixLift 3010299
  have htrace : WordTrace (prefixWord ++ tailWord_3010299) baseStart_3010299 baseEnd_3010299 := by
    simpa [prefixWord, tailWord_3010299, baseEnd_3010299] using wordTrace_append hprefix tailTrace_3010299
  have hstable : (prefixWord ++ tailWord_3010299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010299).length < 2 ^ (prefixWord ++ tailWord_3010299).sum := by decide
  have hdescent : baseEnd_3010299 < baseStart_3010299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010322 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3010322 : Nat := 118140960795 + 3010322 * 2 ^ 59
def prefixEnd_3010322 : Nat := 4983230072969 + 3 ^ 40 * 3010322 * 2
def baseEnd_3010322 : Nat := 1030494740536050890020525

theorem tailTrace_3010322 : CollatzResearch.WordTrace tailWord_3010322 prefixEnd_3010322 1030494740536050890020525 := by
  unfold tailWord_3010322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27448865850031247727840305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73196975600083327274240813 27448865850031247727840305)
  ·
    refine ⟨20586649387523435795880229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27448865850031247727840305 20586649387523435795880229)
    ·
      refine ⟨3859996760160644211727543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20586649387523435795880229 3859996760160644211727543)
      ·
        refine ⟨5789995140240966317591315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859996760160644211727543 5789995140240966317591315)
        ·
          refine ⟨8684992710361449476386973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789995140240966317591315 8684992710361449476386973)
          ·
            refine ⟨3256872266385543553645115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8684992710361449476386973 3256872266385543553645115)
            ·
              refine ⟨4885308399578315330467673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256872266385543553645115 4885308399578315330467673)
              ·
                refine ⟨3663981299683736497850755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885308399578315330467673 3663981299683736497850755)
                ·
                  refine ⟨5495971949525604746776133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663981299683736497850755 5495971949525604746776133)
                  ·
                    refine ⟨1030494740536050890020525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495971949525604746776133 1030494740536050890020525)
                    ·
                      rfl

theorem cell22_3010322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3010322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010322 prefixEnd_3010322 := by exact prefixLift 3010322
  have htrace : WordTrace (prefixWord ++ tailWord_3010322) baseStart_3010322 baseEnd_3010322 := by
    simpa [prefixWord, tailWord_3010322, baseEnd_3010322] using wordTrace_append hprefix tailTrace_3010322
  have hstable : (prefixWord ++ tailWord_3010322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010322).length < 2 ^ (prefixWord ++ tailWord_3010322).sum := by decide
  have hdescent : baseEnd_3010322 < baseStart_3010322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010380 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_3010380 : Nat := 118140960795 + 3010380 * 2 ^ 59
def prefixEnd_3010380 : Nat := 4983230072969 + 3 ^ 40 * 3010380 * 2
def baseEnd_3010380 : Nat := 1030514595121358072070347

theorem tailTrace_3010380 : CollatzResearch.WordTrace tailWord_3010380 prefixEnd_3010380 1030514595121358072070347 := by
  unfold tailWord_3010380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54898789416957433408486297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73198385889276577877981729 54898789416957433408486297)
  ·
    refine ⟨41174092062718075056364723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54898789416957433408486297 41174092062718075056364723)
    ·
      refine ⟨61761138094077112584547085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174092062718075056364723 61761138094077112584547085)
      ·
        refine ⟨23160426785278917219205157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61761138094077112584547085 23160426785278917219205157)
        ·
          refine ⟨4342580022239796978600967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23160426785278917219205157 4342580022239796978600967)
          ·
            refine ⟨6513870033359695467901451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342580022239796978600967 6513870033359695467901451)
            ·
              refine ⟨9770805050039543201852177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513870033359695467901451 9770805050039543201852177)
              ·
                refine ⟨7328103787529657401389133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770805050039543201852177 7328103787529657401389133)
                ·
                  refine ⟨2748038920323621525520925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7328103787529657401389133 2748038920323621525520925)
                  ·
                    refine ⟨1030514595121358072070347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748038920323621525520925 1030514595121358072070347)
                    ·
                      rfl

theorem cell22_3010380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_3010380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010380 prefixEnd_3010380 := by exact prefixLift 3010380
  have htrace : WordTrace (prefixWord ++ tailWord_3010380) baseStart_3010380 baseEnd_3010380 := by
    simpa [prefixWord, tailWord_3010380, baseEnd_3010380] using wordTrace_append hprefix tailTrace_3010380
  have hstable : (prefixWord ++ tailWord_3010380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010380).length < 2 ^ (prefixWord ++ tailWord_3010380).sum := by decide
  have hdescent : baseEnd_3010380 < baseStart_3010380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010410 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_3010410 : Nat := 118140960795 + 3010410 * 2 ^ 59
def prefixEnd_3010410 : Nat := 4983230072969 + 3 ^ 40 * 3010410 * 2
def baseEnd_3010410 : Nat := 343508288244815997940085

theorem tailTrace_3010410 : CollatzResearch.WordTrace tailWord_3010410 prefixEnd_3010410 343508288244815997940085 := by
  unfold tailWord_3010410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449668255951545485141171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73199115349204121293709789 27449668255951545485141171)
  ·
    refine ⟨41174502383927318227711757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27449668255951545485141171 41174502383927318227711757)
    ·
      refine ⟨15440438393972744335391909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41174502383927318227711757 15440438393972744335391909)
      ·
        refine ⟨2895082198869889562885983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15440438393972744335391909 2895082198869889562885983)
        ·
          refine ⟨4342623298304834344328975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895082198869889562885983 4342623298304834344328975)
          ·
            refine ⟨6513934947457251516493463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342623298304834344328975 6513934947457251516493463)
            ·
              refine ⟨9770902421185877274740195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513934947457251516493463 9770902421185877274740195)
              ·
                refine ⟨14656353631778815912110293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9770902421185877274740195 14656353631778815912110293)
                ·
                  refine ⟨343508288244815997940085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14656353631778815912110293 343508288244815997940085)
                  ·
                    rfl

theorem cell22_3010410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_3010410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010410 prefixEnd_3010410 := by exact prefixLift 3010410
  have htrace : WordTrace (prefixWord ++ tailWord_3010410) baseStart_3010410 baseEnd_3010410 := by
    simpa [prefixWord, tailWord_3010410, baseEnd_3010410] using wordTrace_append hprefix tailTrace_3010410
  have hstable : (prefixWord ++ tailWord_3010410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010410).length < 2 ^ (prefixWord ++ tailWord_3010410).sum := by decide
  have hdescent : baseEnd_3010410 < baseStart_3010410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010453 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_3010453 : Nat := 118140960795 + 3010453 * 2 ^ 59
def prefixEnd_3010453 : Nat := 4983230072969 + 3 ^ 40 * 3010453 * 2
def baseEnd_3010453 : Nat := 1030539584513210214995123

theorem tailTrace_3010453 : CollatzResearch.WordTrace tailWord_3010453 prefixEnd_3010453 1030539584513210214995123 := by
  unfold tailWord_3010453
  simp only [CollatzResearch.WordTrace]
  refine ⟨109800241362650400284380013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73200160908433600189586675 109800241362650400284380013)
  ·
    refine ⟨41175090510993900106642505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109800241362650400284380013 41175090510993900106642505)
    ·
      refine ⟨30881317883245425079981879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41175090510993900106642505 30881317883245425079981879)
      ·
        refine ⟨46321976824868137619972819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30881317883245425079981879 46321976824868137619972819)
        ·
          refine ⟨69482965237302206429959229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46321976824868137619972819 69482965237302206429959229)
          ·
            refine ⟨26056111963988327411234711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69482965237302206429959229 26056111963988327411234711)
            ·
              refine ⟨39084167945982491116852067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26056111963988327411234711 39084167945982491116852067)
              ·
                refine ⟨58626251918973736675278101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39084167945982491116852067 58626251918973736675278101)
                ·
                  refine ⟨2748105558701893906653661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58626251918973736675278101 2748105558701893906653661)
                  ·
                    refine ⟨1030539584513210214995123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748105558701893906653661 1030539584513210214995123)
                    ·
                      rfl

theorem cell22_3010453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_3010453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010453 prefixEnd_3010453 := by exact prefixLift 3010453
  have htrace : WordTrace (prefixWord ++ tailWord_3010453) baseStart_3010453 baseEnd_3010453 := by
    simpa [prefixWord, tailWord_3010453, baseEnd_3010453] using wordTrace_append hprefix tailTrace_3010453
  have hstable : (prefixWord ++ tailWord_3010453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010453).length < 2 ^ (prefixWord ++ tailWord_3010453).sum := by decide
  have hdescent : baseEnd_3010453 < baseStart_3010453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010455 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 4]
def baseStart_3010455 : Nat := 118140960795 + 3010455 * 2 ^ 59
def prefixEnd_3010455 : Nat := 4983230072969 + 3 ^ 40 * 3010455 * 2
def baseEnd_3010455 : Nat := 343513423051360958815039

theorem tailTrace_3010455 : CollatzResearch.WordTrace tailWord_3010455 prefixEnd_3010455 343513423051360958815039 := by
  unfold tailWord_3010455
  simp only [CollatzResearch.WordTrace]
  refine ⟨109800314308643154625952819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73200209539095436417301879 109800314308643154625952819)
  ·
    refine ⟨164700471462964731938929229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109800314308643154625952819 164700471462964731938929229)
    ·
      refine ⟨61762676798611774477098461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164700471462964731938929229 61762676798611774477098461)
      ·
        refine ⟨23161003799479415428911923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61762676798611774477098461 23161003799479415428911923)
        ·
          refine ⟨34741505699219123143367885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23161003799479415428911923 34741505699219123143367885)
          ·
            refine ⟨13028064637207171178762957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34741505699219123143367885 13028064637207171178762957)
            ·
              refine ⟨4885524238952689192036109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13028064637207171178762957 4885524238952689192036109)
              ·
                refine ⟨1832071589607258447013541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4885524238952689192036109 1832071589607258447013541)
                ·
                  refine ⟨343513423051360958815039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832071589607258447013541 343513423051360958815039)
                  ·
                    rfl

theorem cell22_3010455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 4].length) (baseStart_3010455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010455 prefixEnd_3010455 := by exact prefixLift 3010455
  have htrace : WordTrace (prefixWord ++ tailWord_3010455) baseStart_3010455 baseEnd_3010455 := by
    simpa [prefixWord, tailWord_3010455, baseEnd_3010455] using wordTrace_append hprefix tailTrace_3010455
  have hstable : (prefixWord ++ tailWord_3010455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010455).length < 2 ^ (prefixWord ++ tailWord_3010455).sum := by decide
  have hdescent : baseEnd_3010455 < baseStart_3010455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010468 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3010468 : Nat := 118140960795 + 3010468 * 2 ^ 59
def prefixEnd_3010468 : Nat := 4983230072969 + 3 ^ 40 * 3010468 * 2
def baseEnd_3010468 : Nat := 1030544719319755175870077

theorem tailTrace_3010468 : CollatzResearch.WordTrace tailWord_3010468 prefixEnd_3010468 1030544719319755175870077 := by
  unfold tailWord_3010468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54900394228798028923088029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73200525638397371897450705 54900394228798028923088029)
  ·
    refine ⟨20587647835799260846158011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54900394228798028923088029 20587647835799260846158011)
    ·
      refine ⟨30881471753698891269237017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20587647835799260846158011 30881471753698891269237017)
      ·
        refine ⟨23161103815274168451927763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30881471753698891269237017 23161103815274168451927763)
        ·
          refine ⟨34741655722911252677891645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23161103815274168451927763 34741655722911252677891645)
          ·
            refine ⟨13028120896091719754209367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34741655722911252677891645 13028120896091719754209367)
            ·
              refine ⟨19542181344137579631314051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13028120896091719754209367 19542181344137579631314051)
              ·
                refine ⟨29313272016206369446971077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19542181344137579631314051 29313272016206369446971077)
                ·
                  refine ⟨5496238503038694271307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29313272016206369446971077 5496238503038694271307077)
                  ·
                    refine ⟨1030544719319755175870077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496238503038694271307077 1030544719319755175870077)
                    ·
                      rfl

theorem cell22_3010468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3010468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010468 prefixEnd_3010468 := by exact prefixLift 3010468
  have htrace : WordTrace (prefixWord ++ tailWord_3010468) baseStart_3010468 baseEnd_3010468 := by
    simpa [prefixWord, tailWord_3010468, baseEnd_3010468] using wordTrace_append hprefix tailTrace_3010468
  have hstable : (prefixWord ++ tailWord_3010468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010468).length < 2 ^ (prefixWord ++ tailWord_3010468).sum := by decide
  have hdescent : baseEnd_3010468 < baseStart_3010468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010478 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3010478 : Nat := 118140960795 + 3010478 * 2 ^ 59
def prefixEnd_3010478 : Nat := 4983230072969 + 3 ^ 40 * 3010478 * 2
def baseEnd_3010478 : Nat := 343516047508039494373349

theorem tailTrace_3010478 : CollatzResearch.WordTrace tailWord_3010478 prefixEnd_3010478 343516047508039494373349 := by
  unfold tailWord_3010478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13725144148444978694255011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73200768791706553036026725 13725144148444978694255011)
  ·
    refine ⟨20587716222667468041382517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13725144148444978694255011 20587716222667468041382517)
    ·
      refine ⟨1930098395875075128879611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20587716222667468041382517 1930098395875075128879611)
      ·
        refine ⟨2895147593812612693319417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930098395875075128879611 2895147593812612693319417)
        ·
          refine ⟨2171360695359459519989563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895147593812612693319417 2171360695359459519989563)
          ·
            refine ⟨3257041043039189279984345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171360695359459519989563 3257041043039189279984345)
            ·
              refine ⟨2442780782279391959988259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257041043039189279984345 2442780782279391959988259)
              ·
                refine ⟨3664171173419087939982389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442780782279391959988259 3664171173419087939982389)
                ·
                  refine ⟨343516047508039494373349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664171173419087939982389 343516047508039494373349)
                  ·
                    rfl

theorem cell22_3010478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3010478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010478 prefixEnd_3010478 := by exact prefixLift 3010478
  have htrace : WordTrace (prefixWord ++ tailWord_3010478) baseStart_3010478 baseEnd_3010478 := by
    simpa [prefixWord, tailWord_3010478, baseEnd_3010478] using wordTrace_append hprefix tailTrace_3010478
  have hstable : (prefixWord ++ tailWord_3010478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010478).length < 2 ^ (prefixWord ++ tailWord_3010478).sum := by decide
  have hdescent : baseEnd_3010478 < baseStart_3010478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010532 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_3010532 : Nat := 118140960795 + 3010532 * 2 ^ 59
def prefixEnd_3010532 : Nat := 4983230072969 + 3 ^ 40 * 3010532 * 2
def baseEnd_3010532 : Nat := 1030566627827680342269881

theorem tailTrace_3010532 : CollatzResearch.WordTrace tailWord_3010532 prefixEnd_3010532 1030566627827680342269881 := by
  unfold tailWord_3010532
  simp only [CollatzResearch.WordTrace]
  refine ⟨54901561364682098388252925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73202081819576131184337233 54901561364682098388252925)
  ·
    refine ⟨20588085511755786895594847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54901561364682098388252925 20588085511755786895594847)
    ·
      refine ⟨30882128267633680343392271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20588085511755786895594847 30882128267633680343392271)
      ·
        refine ⟨46323192401450520515088407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30882128267633680343392271 46323192401450520515088407)
        ·
          refine ⟨69484788602175780772632611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46323192401450520515088407 69484788602175780772632611)
          ·
            refine ⟨104227182903263671158948917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69484788602175780772632611 104227182903263671158948917)
            ·
              refine ⟨9771298397180969171151461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104227182903263671158948917 9771298397180969171151461)
              ·
                refine ⟨1832118449471431719590899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9771298397180969171151461 1832118449471431719590899)
                ·
                  refine ⟨2748177674207147579386349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832118449471431719590899 2748177674207147579386349)
                  ·
                    refine ⟨1030566627827680342269881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748177674207147579386349 1030566627827680342269881)
                    ·
                      rfl

theorem cell22_3010532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_3010532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010532 prefixEnd_3010532 := by exact prefixLift 3010532
  have htrace : WordTrace (prefixWord ++ tailWord_3010532) baseStart_3010532 baseEnd_3010532 := by
    simpa [prefixWord, tailWord_3010532, baseEnd_3010532] using wordTrace_append hprefix tailTrace_3010532
  have hstable : (prefixWord ++ tailWord_3010532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010532).length < 2 ^ (prefixWord ++ tailWord_3010532).sum := by decide
  have hdescent : baseEnd_3010532 < baseStart_3010532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010543 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3010543 : Nat := 118140960795 + 3010543 * 2 ^ 59
def prefixEnd_3010543 : Nat := 4983230072969 + 3 ^ 40 * 3010543 * 2
def baseEnd_3010543 : Nat := 1030570393352479980244847

theorem tailTrace_3010543 : CollatzResearch.WordTrace tailWord_3010543 prefixEnd_3010543 1030570393352479980244847 := by
  unfold tailWord_3010543
  simp only [CollatzResearch.WordTrace]
  refine ⟨109803523932324345655156283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73202349288216230436770855 109803523932324345655156283)
  ·
    refine ⟨164705285898486518482734425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109803523932324345655156283 164705285898486518482734425)
    ·
      refine ⟨123528964423864888862050819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164705285898486518482734425 123528964423864888862050819)
      ·
        refine ⟨185293446635797333293076229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123528964423864888862050819 185293446635797333293076229)
        ·
          refine ⟨34742521244211999992451793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185293446635797333293076229 34742521244211999992451793)
          ·
            refine ⟨26056890933158999994338845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34742521244211999992451793 26056890933158999994338845)
            ·
              refine ⟨9771334099934624997877067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26056890933158999994338845 9771334099934624997877067)
              ·
                refine ⟨14657001149901937496815601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771334099934624997877067 14657001149901937496815601)
                ·
                  refine ⟨10992750862426453122611701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14657001149901937496815601 10992750862426453122611701)
                  ·
                    refine ⟨1030570393352479980244847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10992750862426453122611701 1030570393352479980244847)
                    ·
                      rfl

theorem cell22_3010543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3010543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010543 prefixEnd_3010543 := by exact prefixLift 3010543
  have htrace : WordTrace (prefixWord ++ tailWord_3010543) baseStart_3010543 baseEnd_3010543 := by
    simpa [prefixWord, tailWord_3010543, baseEnd_3010543] using wordTrace_append hprefix tailTrace_3010543
  have hstable : (prefixWord ++ tailWord_3010543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010543).length < 2 ^ (prefixWord ++ tailWord_3010543).sum := by decide
  have hdescent : baseEnd_3010543 < baseStart_3010543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_3010603 : Nat := 118140960795 + 3010603 * 2 ^ 59
def prefixEnd_3010603 : Nat := 4983230072969 + 3 ^ 40 * 3010603 * 2
def baseEnd_3010603 : Nat := 1030590932578659823744663

theorem tailTrace_3010603 : CollatzResearch.WordTrace tailWord_3010603 prefixEnd_3010603 1030590932578659823744663 := by
  unfold tailWord_3010603
  simp only [CollatzResearch.WordTrace]
  refine ⟨109805712312106975902340463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73203808208071317268226975 109805712312106975902340463)
  ·
    refine ⟨164708568468160463853510695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109805712312106975902340463 164708568468160463853510695)
    ·
      refine ⟨247062852702240695780266043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164708568468160463853510695 247062852702240695780266043)
      ·
        refine ⟨370594279053361043670399065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247062852702240695780266043 370594279053361043670399065)
        ·
          refine ⟨277945709290020782752799299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370594279053361043670399065 277945709290020782752799299)
          ·
            refine ⟨416918563935031174129198949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277945709290020782752799299 416918563935031174129198949)
            ·
              refine ⟨78172230737818345149224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416918563935031174129198949 78172230737818345149224803)
              ·
                refine ⟨117258346106727517723837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78172230737818345149224803 117258346106727517723837205)
                ·
                  refine ⟨5496484973752852393304869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117258346106727517723837205 5496484973752852393304869)
                  ·
                    refine ⟨1030590932578659823744663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496484973752852393304869 1030590932578659823744663)
                    ·
                      rfl

theorem cell22_3010603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_3010603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010603 prefixEnd_3010603 := by exact prefixLift 3010603
  have htrace : WordTrace (prefixWord ++ tailWord_3010603) baseStart_3010603 baseEnd_3010603 := by
    simpa [prefixWord, tailWord_3010603, baseEnd_3010603] using wordTrace_append hprefix tailTrace_3010603
  have hstable : (prefixWord ++ tailWord_3010603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010603).length < 2 ^ (prefixWord ++ tailWord_3010603).sum := by decide
  have hdescent : baseEnd_3010603 < baseStart_3010603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010620 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3010620 : Nat := 118140960795 + 3010620 * 2 ^ 59
def prefixEnd_3010620 : Nat := 4983230072969 + 3 ^ 40 * 3010620 * 2
def baseEnd_3010620 : Nat := 1030596752026077446069611

theorem tailTrace_3010620 : CollatzResearch.WordTrace tailWord_3010620 prefixEnd_3010620 1030596752026077446069611 := by
  unfold tailWord_3010620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54903166176522693902854657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73204221568696925203806209 54903166176522693902854657)
  ·
    refine ⟨41177374632392020427140993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54903166176522693902854657 41177374632392020427140993)
    ·
      refine ⟨30883030974294015320355745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41177374632392020427140993 30883030974294015320355745)
      ·
        refine ⟨23162273230720511490266809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30883030974294015320355745 23162273230720511490266809)
        ·
          refine ⟨17371704923040383617700107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23162273230720511490266809 17371704923040383617700107)
          ·
            refine ⟨26057557384560575426550161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17371704923040383617700107 26057557384560575426550161)
            ·
              refine ⟨19543168038420431569912621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26057557384560575426550161 19543168038420431569912621)
              ·
                refine ⟨7328688014407661838717233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19543168038420431569912621 7328688014407661838717233)
                ·
                  refine ⟨5496516010805746379037925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7328688014407661838717233 5496516010805746379037925)
                  ·
                    refine ⟨1030596752026077446069611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496516010805746379037925 1030596752026077446069611)
                    ·
                      rfl

theorem cell22_3010620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3010620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010620 prefixEnd_3010620 := by exact prefixLift 3010620
  have htrace : WordTrace (prefixWord ++ tailWord_3010620) baseStart_3010620 baseEnd_3010620 := by
    simpa [prefixWord, tailWord_3010620, baseEnd_3010620] using wordTrace_append hprefix tailTrace_3010620
  have hstable : (prefixWord ++ tailWord_3010620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010620).length < 2 ^ (prefixWord ++ tailWord_3010620).sum := by decide
  have hdescent : baseEnd_3010620 < baseStart_3010620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010637 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3010637 : Nat := 118140960795 + 3010637 * 2 ^ 59
def prefixEnd_3010637 : Nat := 4983230072969 + 3 ^ 40 * 3010637 * 2
def baseEnd_3010637 : Nat := 1030602571473495068394559

theorem tailTrace_3010637 : CollatzResearch.WordTrace tailWord_3010637 prefixEnd_3010637 1030602571473495068394559 := by
  unfold tailWord_3010637
  simp only [CollatzResearch.WordTrace]
  refine ⟨109806952393983799709078165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73204634929322533139385443 109806952393983799709078165)
  ·
    refine ⟨5147200893467990611363039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109806952393983799709078165 5147200893467990611363039)
    ·
      refine ⟨7720801340201985917044559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5147200893467990611363039 7720801340201985917044559)
      ·
        refine ⟨11581202010302978875566839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7720801340201985917044559 11581202010302978875566839)
        ·
          refine ⟨17371803015454468313350259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11581202010302978875566839 17371803015454468313350259)
          ·
            refine ⟨26057704523181702470025389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17371803015454468313350259 26057704523181702470025389)
            ·
              refine ⟨9771639196193138426259521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26057704523181702470025389 9771639196193138426259521)
              ·
                refine ⟨7328729397144853819694641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9771639196193138426259521 7328729397144853819694641)
                ·
                  refine ⟨5496547047858640364770981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7328729397144853819694641 5496547047858640364770981)
                  ·
                    refine ⟨1030602571473495068394559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496547047858640364770981 1030602571473495068394559)
                    ·
                      rfl

theorem cell22_3010637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3010637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010637 prefixEnd_3010637 := by exact prefixLift 3010637
  have htrace : WordTrace (prefixWord ++ tailWord_3010637) baseStart_3010637 baseEnd_3010637 := by
    simpa [prefixWord, tailWord_3010637, baseEnd_3010637] using wordTrace_append hprefix tailTrace_3010637
  have hstable : (prefixWord ++ tailWord_3010637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010637).length < 2 ^ (prefixWord ++ tailWord_3010637).sum := by decide
  have hdescent : baseEnd_3010637 < baseStart_3010637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010712 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_3010712 : Nat := 118140960795 + 3010712 * 2 ^ 59
def prefixEnd_3010712 : Nat := 4983230072969 + 3 ^ 40 * 3010712 * 2
def baseEnd_3010712 : Nat := 1030628245506219872769329

theorem tailTrace_3010712 : CollatzResearch.WordTrace tailWord_3010712 prefixEnd_3010712 1030628245506219872769329 := by
  unfold tailWord_3010712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54904843934356043759029195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73206458579141391678705593 54904843934356043759029195)
  ·
    refine ⟨82357265901534065638543793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54904843934356043759029195 82357265901534065638543793)
    ·
      refine ⟨61767949426150549228907845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82357265901534065638543793 61767949426150549228907845)
      ·
        refine ⟨11581490517403227980420221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61767949426150549228907845 11581490517403227980420221)
        ·
          refine ⟨4343058944026210492657583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11581490517403227980420221 4343058944026210492657583)
          ·
            refine ⟨6514588416039315738986375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343058944026210492657583 6514588416039315738986375)
            ·
              refine ⟨9771882624058973608479563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514588416039315738986375 9771882624058973608479563)
              ·
                refine ⟨14657823936088460412719345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771882624058973608479563 14657823936088460412719345)
                ·
                  refine ⟨10993367952066345309539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14657823936088460412719345 10993367952066345309539509)
                  ·
                    refine ⟨1030628245506219872769329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10993367952066345309539509 1030628245506219872769329)
                    ·
                      rfl

theorem cell22_3010712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_3010712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010712 prefixEnd_3010712 := by exact prefixLift 3010712
  have htrace : WordTrace (prefixWord ++ tailWord_3010712) baseStart_3010712 baseEnd_3010712 := by
    simpa [prefixWord, tailWord_3010712, baseEnd_3010712] using wordTrace_append hprefix tailTrace_3010712
  have hstable : (prefixWord ++ tailWord_3010712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010712).length < 2 ^ (prefixWord ++ tailWord_3010712).sum := by decide
  have hdescent : baseEnd_3010712 < baseStart_3010712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010725 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 6]
def baseStart_3010725 : Nat := 118140960795 + 3010725 * 2 ^ 59
def prefixEnd_3010725 : Nat := 4983230072969 + 3 ^ 40 * 3010725 * 2
def baseEnd_3010725 : Nat := 343544231890630724064763

theorem tailTrace_3010725 : CollatzResearch.WordTrace tailWord_3010725 prefixEnd_3010725 343544231890630724064763 := by
  unfold tailWord_3010725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109810162017664990738281629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73206774678443327158854419 109810162017664990738281629)
  ·
    refine ⟨41178810756624371526855611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109810162017664990738281629 41178810756624371526855611)
    ·
      refine ⟨61768216134936557290283417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41178810756624371526855611 61768216134936557290283417)
      ·
        refine ⟨46326162101202417967712563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61768216134936557290283417 46326162101202417967712563)
        ·
          refine ⟨69489243151803626951568845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46326162101202417967712563 69489243151803626951568845)
          ·
            refine ⟨26058466181926360106838317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69489243151803626951568845 26058466181926360106838317)
            ·
              refine ⟨9771924818222385040064369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26058466181926360106838317 9771924818222385040064369)
              ·
                refine ⟨7328943613666788780048277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9771924818222385040064369 7328943613666788780048277)
                ·
                  refine ⟨343544231890630724064763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7328943613666788780048277 343544231890630724064763)
                  ·
                    rfl

theorem cell22_3010725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_3010725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010725 prefixEnd_3010725 := by exact prefixLift 3010725
  have htrace : WordTrace (prefixWord ++ tailWord_3010725) baseStart_3010725 baseEnd_3010725 := by
    simpa [prefixWord, tailWord_3010725, baseEnd_3010725] using wordTrace_append hprefix tailTrace_3010725
  have hstable : (prefixWord ++ tailWord_3010725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010725).length < 2 ^ (prefixWord ++ tailWord_3010725).sum := by decide
  have hdescent : baseEnd_3010725 < baseStart_3010725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010785 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3010785 : Nat := 118140960795 + 3010785 * 2 ^ 59
def prefixEnd_3010785 : Nat := 4983230072969 + 3 ^ 40 * 3010785 * 2
def baseEnd_3010785 : Nat := 1030653234898072015694105

theorem tailTrace_3010785 : CollatzResearch.WordTrace tailWord_3010785 prefixEnd_3010785 1030653234898072015694105 := by
  unfold tailWord_3010785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109812350397447620985465809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73208233598298413990310539 109812350397447620985465809)
  ·
    refine ⟨82359262798085715739099357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109812350397447620985465809 82359262798085715739099357)
    ·
      refine ⟨30884723549282143402162259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82359262798085715739099357 30884723549282143402162259)
      ·
        refine ⟨46327085323923215103243389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30884723549282143402162259 46327085323923215103243389)
        ·
          refine ⟨17372656996471205663716271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46327085323923215103243389 17372656996471205663716271)
          ·
            refine ⟨26058985494706808495574407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17372656996471205663716271 26058985494706808495574407)
            ·
              refine ⟨39088478242060212743361611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26058985494706808495574407 39088478242060212743361611)
              ·
                refine ⟨58632717363090319115042417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39088478242060212743361611 58632717363090319115042417)
                ·
                  refine ⟨43974538022317739336281813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58632717363090319115042417 43974538022317739336281813)
                  ·
                    refine ⟨1030653234898072015694105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43974538022317739336281813 1030653234898072015694105)
                    ·
                      rfl

theorem cell22_3010785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3010785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010785 prefixEnd_3010785 := by exact prefixLift 3010785
  have htrace : WordTrace (prefixWord ++ tailWord_3010785) baseStart_3010785 baseEnd_3010785 := by
    simpa [prefixWord, tailWord_3010785, baseEnd_3010785] using wordTrace_append hprefix tailTrace_3010785
  have hstable : (prefixWord ++ tailWord_3010785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010785).length < 2 ^ (prefixWord ++ tailWord_3010785).sum := by decide
  have hdescent : baseEnd_3010785 < baseStart_3010785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010815 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 7]
def baseStart_3010815 : Nat := 118140960795 + 3010815 * 2 ^ 59
def prefixEnd_3010815 : Nat := 4983230072969 + 3 ^ 40 * 3010815 * 2
def baseEnd_3010815 : Nat := 343554501503720645814671

theorem tailTrace_3010815 : CollatzResearch.WordTrace tailWord_3010815 prefixEnd_3010815 343554501503720645814671 := by
  unfold tailWord_3010815
  simp only [CollatzResearch.WordTrace]
  refine ⟨109813444587338936109057899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73208963058225957406038599 109813444587338936109057899)
  ·
    refine ⟨164720166881008404163586849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109813444587338936109057899 164720166881008404163586849)
    ·
      refine ⟨123540125160756303122690137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164720166881008404163586849 123540125160756303122690137)
      ·
        refine ⟨92655093870567227342017603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123540125160756303122690137 92655093870567227342017603)
        ·
          refine ⟨138982640805850841013026405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92655093870567227342017603 138982640805850841013026405)
          ·
            refine ⟨26059245151097032689942451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138982640805850841013026405 26059245151097032689942451)
            ·
              refine ⟨39088867726645549034913677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26059245151097032689942451 39088867726645549034913677)
              ·
                refine ⟨14658325397492080888092629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39088867726645549034913677 14658325397492080888092629)
                ·
                  refine ⟨343554501503720645814671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14658325397492080888092629 343554501503720645814671)
                  ·
                    rfl

theorem cell22_3010815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_3010815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010815 prefixEnd_3010815 := by exact prefixLift 3010815
  have htrace : WordTrace (prefixWord ++ tailWord_3010815) baseStart_3010815 baseEnd_3010815 := by
    simpa [prefixWord, tailWord_3010815, baseEnd_3010815] using wordTrace_append hprefix tailTrace_3010815
  have hstable : (prefixWord ++ tailWord_3010815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010815).length < 2 ^ (prefixWord ++ tailWord_3010815).sum := by decide
  have hdescent : baseEnd_3010815 < baseStart_3010815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010967 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 7]
def baseStart_3010967 : Nat := 118140960795 + 3010967 * 2 ^ 59
def prefixEnd_3010967 : Nat := 4983230072969 + 3 ^ 40 * 3010967 * 2
def baseEnd_3010967 : Nat := 343571845739161402547849

theorem tailTrace_3010967 : CollatzResearch.WordTrace tailWord_3010967 prefixEnd_3010967 343571845739161402547849 := by
  unfold tailWord_3010967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109818988482788266068591155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73212658988525510712394103 109818988482788266068591155)
  ·
    refine ⟨164728482724182399102886733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109818988482788266068591155 164728482724182399102886733)
    ·
      refine ⟨61773181021568399663582525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164728482724182399102886733 61773181021568399663582525)
      ·
        refine ⟨23164942883088149873843447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61773181021568399663582525 23164942883088149873843447)
        ·
          refine ⟨34747414324632224810765171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23164942883088149873843447 34747414324632224810765171)
          ·
            refine ⟨52121121486948337216147757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34747414324632224810765171 52121121486948337216147757)
            ·
              refine ⟨19545420557605626456055409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52121121486948337216147757 19545420557605626456055409)
              ·
                refine ⟨14659065418204219842041557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19545420557605626456055409 14659065418204219842041557)
                ·
                  refine ⟨343571845739161402547849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14659065418204219842041557 343571845739161402547849)
                  ·
                    rfl

theorem cell22_3010967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_3010967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3010967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3010967 prefixEnd_3010967 := by exact prefixLift 3010967
  have htrace : WordTrace (prefixWord ++ tailWord_3010967) baseStart_3010967 baseEnd_3010967 := by
    simpa [prefixWord, tailWord_3010967, baseEnd_3010967] using wordTrace_append hprefix tailTrace_3010967
  have hstable : (prefixWord ++ tailWord_3010967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010967).length < 2 ^ (prefixWord ++ tailWord_3010967).sum := by decide
  have hdescent : baseEnd_3010967 < baseStart_3010967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011001 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 5]
def baseStart_3011001 : Nat := 118140960795 + 3011001 * 2 ^ 59
def prefixEnd_3011001 : Nat := 4983230072969 + 3 ^ 40 * 3011001 * 2
def baseEnd_3011001 : Nat := 343575725370773150764481

theorem tailTrace_3011001 : CollatzResearch.WordTrace tailWord_3011001 prefixEnd_3011001 343575725370773150764481 := by
  unfold tailWord_3011001
  simp only [CollatzResearch.WordTrace]
  refine ⟨109820228564665089875328857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73213485709776726583552571 109820228564665089875328857)
  ·
    refine ⟨82365171423498817406496643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109820228564665089875328857 82365171423498817406496643)
    ·
      refine ⟨123547757135248226109744965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82365171423498817406496643 123547757135248226109744965)
      ·
        refine ⟨23165204462859042395577181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123547757135248226109744965 23165204462859042395577181)
        ·
          refine ⟨8686951673572140898341443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23165204462859042395577181 8686951673572140898341443)
          ·
            refine ⟨13030427510358211347512165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8686951673572140898341443 13030427510358211347512165)
            ·
              refine ⟨2443205158192164627658531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13030427510358211347512165 2443205158192164627658531)
              ·
                refine ⟨3664807737288246941487797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443205158192164627658531 3664807737288246941487797)
                ·
                  refine ⟨343575725370773150764481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3664807737288246941487797 343575725370773150764481)
                  ·
                    rfl

theorem cell22_3011001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_3011001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011001 prefixEnd_3011001 := by exact prefixLift 3011001
  have htrace : WordTrace (prefixWord ++ tailWord_3011001) baseStart_3011001 baseEnd_3011001 := by
    simpa [prefixWord, tailWord_3011001, baseEnd_3011001] using wordTrace_append hprefix tailTrace_3011001
  have hstable : (prefixWord ++ tailWord_3011001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011001).length < 2 ^ (prefixWord ++ tailWord_3011001).sum := by decide
  have hdescent : baseEnd_3011001 < baseStart_3011001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011076 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3011076 : Nat := 118140960795 + 3011076 * 2 ^ 59
def prefixEnd_3011076 : Nat := 4983230072969 + 3 ^ 40 * 3011076 * 2
def baseEnd_3011076 : Nat := 1030752850145044256668213

theorem tailTrace_3011076 : CollatzResearch.WordTrace tailWord_3011076 prefixEnd_3011076 1030752850145044256668213 := by
  unfold tailWord_3011076
  simp only [CollatzResearch.WordTrace]
  refine ⟨54911482019696688842154541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73215309359595585122872721 54911482019696688842154541)
  ·
    refine ⟨20591805757386258315807953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54911482019696688842154541 20591805757386258315807953)
    ·
      refine ⟨15443854318039693736855965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20591805757386258315807953 15443854318039693736855965)
      ·
        refine ⟨5791445369264885151320987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15443854318039693736855965 5791445369264885151320987)
        ·
          refine ⟨8687168053897327726981481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791445369264885151320987 8687168053897327726981481)
          ·
            refine ⟨6515376040422995795236111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8687168053897327726981481 6515376040422995795236111)
            ·
              refine ⟨9773064060634493692854167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515376040422995795236111 9773064060634493692854167)
              ·
                refine ⟨14659596090951740539281251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9773064060634493692854167 14659596090951740539281251)
                ·
                  refine ⟨21989394136427610808921877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14659596090951740539281251 21989394136427610808921877)
                  ·
                    refine ⟨1030752850145044256668213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21989394136427610808921877 1030752850145044256668213)
                    ·
                      rfl

theorem cell22_3011076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3011076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011076 prefixEnd_3011076 := by exact prefixLift 3011076
  have htrace : WordTrace (prefixWord ++ tailWord_3011076) baseStart_3011076 baseEnd_3011076 := by
    simpa [prefixWord, tailWord_3011076, baseEnd_3011076] using wordTrace_append hprefix tailTrace_3011076
  have hstable : (prefixWord ++ tailWord_3011076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011076).length < 2 ^ (prefixWord ++ tailWord_3011076).sum := by decide
  have hdescent : baseEnd_3011076 < baseStart_3011076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011170 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3011170 : Nat := 118140960795 + 3011170 * 2 ^ 59
def prefixEnd_3011170 : Nat := 4983230072969 + 3 ^ 40 * 3011170 * 2
def baseEnd_3011170 : Nat := 343595009422019781605975

theorem tailTrace_3011170 : CollatzResearch.WordTrace tailWord_3011170 prefixEnd_3011170 343595009422019781605975 := by
  unfold tailWord_3011170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456598125263207934557741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73217595000701887825487309 27456598125263207934557741)
  ·
    refine ⟨10296224296973702975459153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27456598125263207934557741 10296224296973702975459153)
    ·
      refine ⟨7722168222730277231594365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10296224296973702975459153 7722168222730277231594365)
      ·
        refine ⟨2895813083523853961847887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722168222730277231594365 2895813083523853961847887)
        ·
          refine ⟨4343719625285780942771831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895813083523853961847887 4343719625285780942771831)
          ·
            refine ⟨6515579437928671414157747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343719625285780942771831 6515579437928671414157747)
            ·
              refine ⟨9773369156893007121236621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515579437928671414157747 9773369156893007121236621)
              ·
                refine ⟨3665013433834877670463733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9773369156893007121236621 3665013433834877670463733)
                ·
                  refine ⟨343595009422019781605975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3665013433834877670463733 343595009422019781605975)
                  ·
                    rfl

theorem cell22_3011170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3011170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011170 prefixEnd_3011170 := by exact prefixLift 3011170
  have htrace : WordTrace (prefixWord ++ tailWord_3011170) baseStart_3011170 baseEnd_3011170 := by
    simpa [prefixWord, tailWord_3011170, baseEnd_3011170] using wordTrace_append hprefix tailTrace_3011170
  have hstable : (prefixWord ++ tailWord_3011170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011170).length < 2 ^ (prefixWord ++ tailWord_3011170).sum := by decide
  have hdescent : baseEnd_3011170 < baseStart_3011170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011194 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_3011194 : Nat := 118140960795 + 3011194 * 2 ^ 59
def prefixEnd_3011194 : Nat := 4983230072969 + 3 ^ 40 * 3011194 * 2
def baseEnd_3011194 : Nat := 1030793243956531282217851

theorem tailTrace_3011194 : CollatzResearch.WordTrace tailWord_3011194 prefixEnd_3011194 1030793243956531282217851 := by
  unfold tailWord_3011194
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456816963241470959276159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73218178568643922558069757 27456816963241470959276159)
  ·
    refine ⟨41185225444862206438914239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27456816963241470959276159 41185225444862206438914239)
    ·
      refine ⟨61777838167293309658371359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41185225444862206438914239 61777838167293309658371359)
      ·
        refine ⟨92666757250939964487557039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61777838167293309658371359 92666757250939964487557039)
        ·
          refine ⟨139000135876409946731335559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92666757250939964487557039 139000135876409946731335559)
          ·
            refine ⟨208500203814614920097003339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139000135876409946731335559 208500203814614920097003339)
            ·
              refine ⟨312750305721922380145505009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208500203814614920097003339 312750305721922380145505009)
              ·
                refine ⟨234562729291441785109128757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312750305721922380145505009 234562729291441785109128757)
                ·
                  refine ⟨21990255871072667353980821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234562729291441785109128757 21990255871072667353980821)
                  ·
                    refine ⟨1030793243956531282217851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21990255871072667353980821 1030793243956531282217851)
                    ·
                      rfl

theorem cell22_3011194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_3011194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011194 prefixEnd_3011194 := by exact prefixLift 3011194
  have htrace : WordTrace (prefixWord ++ tailWord_3011194) baseStart_3011194 baseEnd_3011194 := by
    simpa [prefixWord, tailWord_3011194, baseEnd_3011194] using wordTrace_append hprefix tailTrace_3011194
  have hstable : (prefixWord ++ tailWord_3011194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011194).length < 2 ^ (prefixWord ++ tailWord_3011194).sum := by decide
  have hdescent : baseEnd_3011194 < baseStart_3011194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011196 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_3011196 : Nat := 118140960795 + 3011196 * 2 ^ 59
def prefixEnd_3011196 : Nat := 4983230072969 + 3 ^ 40 * 3011196 * 2
def baseEnd_3011196 : Nat := 1030793928597403943667845

theorem tailTrace_3011196 : CollatzResearch.WordTrace tailWord_3011196 prefixEnd_3011196 1030793928597403943667845 := by
  unfold tailWord_3011196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54913670399479319089338721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73218227199305758785784961 54913670399479319089338721)
  ·
    refine ⟨41185252799609489317004041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54913670399479319089338721 41185252799609489317004041)
    ·
      refine ⟨30888939599707116987753031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41185252799609489317004041 30888939599707116987753031)
      ·
        refine ⟨46333409399560675481629547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30888939599707116987753031 46333409399560675481629547)
        ·
          refine ⟨69500114099341013222444321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46333409399560675481629547 69500114099341013222444321)
          ·
            refine ⟨52125085574505759916833241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69500114099341013222444321 52125085574505759916833241)
            ·
              refine ⟨39093814180879319937624931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52125085574505759916833241 39093814180879319937624931)
              ·
                refine ⟨58640721271318979906437397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39093814180879319937624931 58640721271318979906437397)
                ·
                  refine ⟨2748783809593077183114253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58640721271318979906437397 2748783809593077183114253)
                  ·
                    refine ⟨1030793928597403943667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748783809593077183114253 1030793928597403943667845)
                    ·
                      rfl

theorem cell22_3011196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_3011196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011196 prefixEnd_3011196 := by exact prefixLift 3011196
  have htrace : WordTrace (prefixWord ++ tailWord_3011196) baseStart_3011196 baseEnd_3011196 := by
    simpa [prefixWord, tailWord_3011196, baseEnd_3011196] using wordTrace_append hprefix tailTrace_3011196
  have hstable : (prefixWord ++ tailWord_3011196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011196).length < 2 ^ (prefixWord ++ tailWord_3011196).sum := by decide
  have hdescent : baseEnd_3011196 < baseStart_3011196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011230 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3011230 : Nat := 118140960795 + 3011230 * 2 ^ 59
def prefixEnd_3011230 : Nat := 4983230072969 + 3 ^ 40 * 3011230 * 2
def baseEnd_3011230 : Nat := 1030805567492239188317741

theorem tailTrace_3011230 : CollatzResearch.WordTrace tailWord_3011230 prefixEnd_3011230 1030805567492239188317741 := by
  unfold tailWord_3011230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728572610104432748176893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73219053920556974656943429 13728572610104432748176893)
  ·
    refine ⟨5148214728789162280566335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13728572610104432748176893 5148214728789162280566335)
    ·
      refine ⟨7722322093183743420849503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148214728789162280566335 7722322093183743420849503)
      ·
        refine ⟨11583483139775615131274255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722322093183743420849503 11583483139775615131274255)
        ·
          refine ⟨17375224709663422696911383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583483139775615131274255 17375224709663422696911383)
          ·
            refine ⟨26062837064495134045367075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17375224709663422696911383 26062837064495134045367075)
            ·
              refine ⟨39094255596742701068050613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26062837064495134045367075 39094255596742701068050613)
              ·
                refine ⟨3665086462194628225129745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39094255596742701068050613 3665086462194628225129745)
                ·
                  refine ⟨2748814846645971168847309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665086462194628225129745 2748814846645971168847309)
                  ·
                    refine ⟨1030805567492239188317741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748814846645971168847309 1030805567492239188317741)
                    ·
                      rfl

theorem cell22_3011230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3011230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011230 prefixEnd_3011230 := by exact prefixLift 3011230
  have htrace : WordTrace (prefixWord ++ tailWord_3011230) baseStart_3011230 baseEnd_3011230 := by
    simpa [prefixWord, tailWord_3011230, baseEnd_3011230] using wordTrace_append hprefix tailTrace_3011230
  have hstable : (prefixWord ++ tailWord_3011230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011230).length < 2 ^ (prefixWord ++ tailWord_3011230).sum := by decide
  have hdescent : baseEnd_3011230 < baseStart_3011230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011241 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_3011241 : Nat := 118140960795 + 3011241 * 2 ^ 59
def prefixEnd_3011241 : Nat := 4983230072969 + 3 ^ 40 * 3011241 * 2
def baseEnd_3011241 : Nat := 1030809333017038826292707

theorem tailTrace_3011241 : CollatzResearch.WordTrace tailWord_3011241 prefixEnd_3011241 1030809333017038826292707 := by
  unfold tailWord_3011241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109828982083795610864065577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73219321389197073909377051 109828982083795610864065577)
  ·
    refine ⟨82371736562846708148049183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109828982083795610864065577 82371736562846708148049183)
    ·
      refine ⟨123557604844270062222073775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82371736562846708148049183 123557604844270062222073775)
      ·
        refine ⟨185336407266405093333110663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123557604844270062222073775 185336407266405093333110663)
        ·
          refine ⟨278004610899607639999665995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185336407266405093333110663 278004610899607639999665995)
          ·
            refine ⟨417006916349411459999498993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278004610899607639999665995 417006916349411459999498993)
            ·
              refine ⟨312755187262058594999624245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417006916349411459999498993 312755187262058594999624245)
              ·
                refine ⟨29320798805817993281214773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312755187262058594999624245 29320798805817993281214773)
                ·
                  refine ⟨2748824888045436870113885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29320798805817993281214773 2748824888045436870113885)
                  ·
                    refine ⟨1030809333017038826292707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748824888045436870113885 1030809333017038826292707)
                    ·
                      rfl

theorem cell22_3011241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_3011241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011241 prefixEnd_3011241 := by exact prefixLift 3011241
  have htrace : WordTrace (prefixWord ++ tailWord_3011241) baseStart_3011241 baseEnd_3011241 := by
    simpa [prefixWord, tailWord_3011241, baseEnd_3011241] using wordTrace_append hprefix tailTrace_3011241
  have hstable : (prefixWord ++ tailWord_3011241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011241).length < 2 ^ (prefixWord ++ tailWord_3011241).sum := by decide
  have hdescent : baseEnd_3011241 < baseStart_3011241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011245 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3011245 : Nat := 118140960795 + 3011245 * 2 ^ 59
def prefixEnd_3011245 : Nat := 4983230072969 + 3 ^ 40 * 3011245 * 2
def baseEnd_3011245 : Nat := 1030810702298784149192695

theorem tailTrace_3011245 : CollatzResearch.WordTrace tailWord_3011245 prefixEnd_3011245 1030810702298784149192695 := by
  unfold tailWord_3011245
  simp only [CollatzResearch.WordTrace]
  refine ⟨109829127975781119547211189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73219418650520746364807459 109829127975781119547211189)
  ·
    refine ⟨10296480747729479957551049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109829127975781119547211189 10296480747729479957551049)
    ·
      refine ⟨7722360560797109968163287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10296480747729479957551049 7722360560797109968163287)
      ·
        refine ⟨11583540841195664952244931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722360560797109968163287 11583540841195664952244931)
        ·
          refine ⟨17375311261793497428367397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583540841195664952244931 17375311261793497428367397)
          ·
            refine ⟨3257870861586280767818887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17375311261793497428367397 3257870861586280767818887)
            ·
              refine ⟨4886806292379421151728331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257870861586280767818887 4886806292379421151728331)
              ·
                refine ⟨7330209438569131727592497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886806292379421151728331 7330209438569131727592497)
                ·
                  refine ⟨5497657078926848795694373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330209438569131727592497 5497657078926848795694373)
                  ·
                    refine ⟨1030810702298784149192695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497657078926848795694373 1030810702298784149192695)
                    ·
                      rfl

theorem cell22_3011245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3011245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011245 prefixEnd_3011245 := by exact prefixLift 3011245
  have htrace : WordTrace (prefixWord ++ tailWord_3011245) baseStart_3011245 baseEnd_3011245 := by
    simpa [prefixWord, tailWord_3011245, baseEnd_3011245] using wordTrace_append hprefix tailTrace_3011245
  have hstable : (prefixWord ++ tailWord_3011245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011245).length < 2 ^ (prefixWord ++ tailWord_3011245).sum := by decide
  have hdescent : baseEnd_3011245 < baseStart_3011245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011271 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 5]
def baseStart_3011271 : Nat := 118140960795 + 3011271 * 2 ^ 59
def prefixEnd_3011271 : Nat := 4983230072969 + 3 ^ 40 * 3011271 * 2
def baseEnd_3011271 : Nat := 343606534210042916014205

theorem tailTrace_3011271 : CollatzResearch.WordTrace tailWord_3011271 prefixEnd_3011271 343606534210042916014205 := by
  unfold tailWord_3011271
  simp only [CollatzResearch.WordTrace]
  refine ⟨109830076273686925987657667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73220050849124617325105111 109830076273686925987657667)
  ·
    refine ⟨164745114410530388981486501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109830076273686925987657667 164745114410530388981486501)
    ·
      refine ⟨30889708951974447934028719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164745114410530388981486501 30889708951974447934028719)
      ·
        refine ⟨46334563427961671901043079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30889708951974447934028719 46334563427961671901043079)
        ·
          refine ⟨69501845141942507851564619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46334563427961671901043079 69501845141942507851564619)
          ·
            refine ⟨104252767712913761777346929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69501845141942507851564619 104252767712913761777346929)
            ·
              refine ⟨78189575784685321333010197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104252767712913761777346929 78189575784685321333010197)
              ·
                refine ⟨3665136364907124437484853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78189575784685321333010197 3665136364907124437484853)
                ·
                  refine ⟨343606534210042916014205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3665136364907124437484853 343606534210042916014205)
                  ·
                    rfl

theorem cell22_3011271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].length) (baseStart_3011271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011271 prefixEnd_3011271 := by exact prefixLift 3011271
  have htrace : WordTrace (prefixWord ++ tailWord_3011271) baseStart_3011271 baseEnd_3011271 := by
    simpa [prefixWord, tailWord_3011271, baseEnd_3011271] using wordTrace_append hprefix tailTrace_3011271
  have hstable : (prefixWord ++ tailWord_3011271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011271).length < 2 ^ (prefixWord ++ tailWord_3011271).sum := by decide
  have hdescent : baseEnd_3011271 < baseStart_3011271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011333 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 4]
def baseStart_3011333 : Nat := 118140960795 + 3011333 * 2 ^ 59
def prefixEnd_3011333 : Nat := 4983230072969 + 3 ^ 40 * 3011333 * 2
def baseEnd_3011333 : Nat := 343613608832393750997475

theorem tailTrace_3011333 : CollatzResearch.WordTrace tailWord_3011333 prefixEnd_3011333 343613608832393750997475 := by
  unfold tailWord_3011333
  simp only [CollatzResearch.WordTrace]
  refine ⟨109832337599462310576414653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73221558399641540384276435 109832337599462310576414653)
  ·
    refine ⟨41187126599798366466155495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109832337599462310576414653 41187126599798366466155495)
    ·
      refine ⟨61780689899697549699233243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41187126599798366466155495 61780689899697549699233243)
      ·
        refine ⟨92671034849546324548849865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61780689899697549699233243 92671034849546324548849865)
        ·
          refine ⟨69503276137159743411637399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92671034849546324548849865 69503276137159743411637399)
          ·
            refine ⟨104254914205739615117456099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69503276137159743411637399 104254914205739615117456099)
            ·
              refine ⟨156382371308609422676184149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104254914205739615117456099 156382371308609422676184149)
              ·
                refine ⟨1832605913772766671986533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 156382371308609422676184149 1832605913772766671986533)
                ·
                  refine ⟨343613608832393750997475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832605913772766671986533 343613608832393750997475)
                  ·
                    rfl

theorem cell22_3011333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_3011333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011333 prefixEnd_3011333 := by exact prefixLift 3011333
  have htrace : WordTrace (prefixWord ++ tailWord_3011333) baseStart_3011333 baseEnd_3011333 := by
    simpa [prefixWord, tailWord_3011333, baseEnd_3011333] using wordTrace_append hprefix tailTrace_3011333
  have hstable : (prefixWord ++ tailWord_3011333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011333).length < 2 ^ (prefixWord ++ tailWord_3011333).sum := by decide
  have hdescent : baseEnd_3011333 < baseStart_3011333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011361 : List Nat := [1, 2, 3, 2, 1, 2, 1, 10]
def baseStart_3011361 : Nat := 118140960795 + 3011361 * 2 ^ 59
def prefixEnd_3011361 : Nat := 4983230072969 + 3 ^ 40 * 3011361 * 2
def baseEnd_3011361 : Nat := 114538934607710945921371

theorem tailTrace_3011361 : CollatzResearch.WordTrace tailWord_3011361 prefixEnd_3011361 114538934607710945921371 := by
  unfold tailWord_3011361
  simp only [CollatzResearch.WordTrace]
  refine ⟨109833358843360871358433937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73222239228907247572289291 109833358843360871358433937)
  ·
    refine ⟨82375019132520653518825453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109833358843360871358433937 82375019132520653518825453)
    ·
      refine ⟨30890632174695245069559545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82375019132520653518825453 30890632174695245069559545)
      ·
        refine ⟨23167974131021433802169659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30890632174695245069559545 23167974131021433802169659)
        ·
          refine ⟨34751961196532150703254489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23167974131021433802169659 34751961196532150703254489)
          ·
            refine ⟨26063970897399113027440867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34751961196532150703254489 26063970897399113027440867)
            ·
              refine ⟨39095956346098669541161301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26063970897399113027440867 39095956346098669541161301)
              ·
                refine ⟨114538934607710945921371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39095956346098669541161301 114538934607710945921371)
                ·
                  rfl

theorem cell22_3011361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 10].length) (baseStart_3011361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011361 prefixEnd_3011361 := by exact prefixLift 3011361
  have htrace : WordTrace (prefixWord ++ tailWord_3011361) baseStart_3011361 baseEnd_3011361 := by
    simpa [prefixWord, tailWord_3011361, baseEnd_3011361] using wordTrace_append hprefix tailTrace_3011361
  have hstable : (prefixWord ++ tailWord_3011361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011361).length < 2 ^ (prefixWord ++ tailWord_3011361).sum := by decide
  have hdescent : baseEnd_3011361 < baseStart_3011361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011410 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3011410 : Nat := 118140960795 + 3011410 * 2 ^ 59
def prefixEnd_3011410 : Nat := 4983230072969 + 3 ^ 40 * 3011410 * 2
def baseEnd_3011410 : Nat := 1030867185170778718817189

theorem tailTrace_3011410 : CollatzResearch.WordTrace tailWord_3011410 prefixEnd_3011410 1030867185170778718817189 := by
  unfold tailWord_3011410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458786505045838181741921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73223430680122235151311789 27458786505045838181741921)
  ·
    refine ⟨20594089878784378636306441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27458786505045838181741921 20594089878784378636306441)
    ·
      refine ⟨15445567409088283977229831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20594089878784378636306441 15445567409088283977229831)
      ·
        refine ⟨23168351113632425965844747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15445567409088283977229831 23168351113632425965844747)
        ·
          refine ⟨34752526670448638948767121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23168351113632425965844747 34752526670448638948767121)
          ·
            refine ⟨26064395002836479211575341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34752526670448638948767121 26064395002836479211575341)
            ·
              refine ⟨9774148126063679704340753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26064395002836479211575341 9774148126063679704340753)
              ·
                refine ⟨7330611094547759778255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774148126063679704340753 7330611094547759778255565)
                ·
                  refine ⟨2748979160455409916845837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7330611094547759778255565 2748979160455409916845837)
                  ·
                    refine ⟨1030867185170778718817189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748979160455409916845837 1030867185170778718817189)
                    ·
                      rfl

theorem cell22_3011410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3011410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011410 prefixEnd_3011410 := by exact prefixLift 3011410
  have htrace : WordTrace (prefixWord ++ tailWord_3011410) baseStart_3011410 baseEnd_3011410 := by
    simpa [prefixWord, tailWord_3011410, baseEnd_3011410] using wordTrace_append hprefix tailTrace_3011410
  have hstable : (prefixWord ++ tailWord_3011410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011410).length < 2 ^ (prefixWord ++ tailWord_3011410).sum := by decide
  have hdescent : baseEnd_3011410 < baseStart_3011410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011427 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 1, 3]
def baseStart_3011427 : Nat := 118140960795 + 3011427 * 2 ^ 59
def prefixEnd_3011427 : Nat := 4983230072969 + 3 ^ 40 * 3011427 * 2
def baseEnd_3011427 : Nat := 1030873004618196341142137

theorem tailTrace_3011427 : CollatzResearch.WordTrace tailWord_3011427 prefixEnd_3011427 1030873004618196341142137 := by
  unfold tailWord_3011427
  simp only [CollatzResearch.WordTrace]
  refine ⟨109835766061121764630336535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73223844040747843086891023 109835766061121764630336535)
  ·
    refine ⟨164753649091682646945504803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109835766061121764630336535 164753649091682646945504803)
    ·
      refine ⟨247130473637523970418257205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164753649091682646945504803 247130473637523970418257205)
      ·
        refine ⟨23168481903517872226711613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247130473637523970418257205 23168481903517872226711613)
        ·
          refine ⟨8688180713819202085016855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23168481903517872226711613 8688180713819202085016855)
          ·
            refine ⟨13032271070728803127525283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688180713819202085016855 13032271070728803127525283)
            ·
              refine ⟨19548406606093204691287925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032271070728803127525283 19548406606093204691287925)
              ·
                refine ⟨1832663119321237939808243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19548406606093204691287925 1832663119321237939808243)
                ·
                  refine ⟨2748994678981856909712365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832663119321237939808243 2748994678981856909712365)
                  ·
                    refine ⟨1030873004618196341142137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748994678981856909712365 1030873004618196341142137)
                    ·
                      rfl

theorem cell22_3011427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 3].length) (baseStart_3011427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011427 prefixEnd_3011427 := by exact prefixLift 3011427
  have htrace : WordTrace (prefixWord ++ tailWord_3011427) baseStart_3011427 baseEnd_3011427 := by
    simpa [prefixWord, tailWord_3011427, baseEnd_3011427] using wordTrace_append hprefix tailTrace_3011427
  have hstable : (prefixWord ++ tailWord_3011427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011427).length < 2 ^ (prefixWord ++ tailWord_3011427).sum := by decide
  have hdescent : baseEnd_3011427 < baseStart_3011427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011453 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3011453 : Nat := 118140960795 + 3011453 * 2 ^ 59
def prefixEnd_3011453 : Nat := 4983230072969 + 3 ^ 40 * 3011453 * 2
def baseEnd_3011453 : Nat := 1030881904949540939992057

theorem tailTrace_3011453 : CollatzResearch.WordTrace tailWord_3011453 prefixEnd_3011453 1030881904949540939992057 := by
  unfold tailWord_3011453
  simp only [CollatzResearch.WordTrace]
  refine ⟨109836714359027571070783013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73224476239351714047188675 109836714359027571070783013)
  ·
    refine ⟨20594383942317669575771815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109836714359027571070783013 20594383942317669575771815)
    ·
      refine ⟨30891575913476504363657723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20594383942317669575771815 30891575913476504363657723)
      ·
        refine ⟨46337363870214756545486585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30891575913476504363657723 46337363870214756545486585)
        ·
          refine ⟨34753022902661067409114939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46337363870214756545486585 34753022902661067409114939)
          ·
            refine ⟨52129534353991601113672409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34753022902661067409114939 52129534353991601113672409)
            ·
              refine ⟨39097150765493700835254307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52129534353991601113672409 39097150765493700835254307)
              ·
                refine ⟨58645726148240551252881461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39097150765493700835254307 58645726148240551252881461)
                ·
                  refine ⟨5498036826397551679957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58645726148240551252881461 5498036826397551679957637)
                  ·
                    refine ⟨1030881904949540939992057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498036826397551679957637 1030881904949540939992057)
                    ·
                      rfl

theorem cell22_3011453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3011453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011453 prefixEnd_3011453 := by exact prefixLift 3011453
  have htrace : WordTrace (prefixWord ++ tailWord_3011453) baseStart_3011453 baseEnd_3011453 := by
    simpa [prefixWord, tailWord_3011453, baseEnd_3011453] using wordTrace_append hprefix tailTrace_3011453
  have hstable : (prefixWord ++ tailWord_3011453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011453).length < 2 ^ (prefixWord ++ tailWord_3011453).sum := by decide
  have hdescent : baseEnd_3011453 < baseStart_3011453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011468 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_3011468 : Nat := 118140960795 + 3011468 * 2 ^ 59
def prefixEnd_3011468 : Nat := 4983230072969 + 3 ^ 40 * 3011468 * 2
def baseEnd_3011468 : Nat := 343629013252028633622337

theorem tailTrace_3011468 : CollatzResearch.WordTrace tailWord_3011468 prefixEnd_3011468 343629013252028633622337 := by
  unfold tailWord_3011468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54918630726986614316289529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73224840969315485755052705 54918630726986614316289529)
  ·
    refine ⟨41188973045239960737217147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54918630726986614316289529 41188973045239960737217147)
    ·
      refine ⟨61783459567859941105825721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41188973045239960737217147 61783459567859941105825721)
      ·
        refine ⟨46337594675894955829369291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61783459567859941105825721 46337594675894955829369291)
        ·
          refine ⟨69506392013842433744053937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46337594675894955829369291 69506392013842433744053937)
          ·
            refine ⟨52129794010381825308040453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69506392013842433744053937 52129794010381825308040453)
            ·
              refine ⟨9774336376946592245257585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52129794010381825308040453 9774336376946592245257585)
              ·
                refine ⟨7330752282709944183943189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774336376946592245257585 7330752282709944183943189)
                ·
                  refine ⟨343629013252028633622337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7330752282709944183943189 343629013252028633622337)
                  ·
                    rfl

theorem cell22_3011468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_3011468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011468 prefixEnd_3011468 := by exact prefixLift 3011468
  have htrace : WordTrace (prefixWord ++ tailWord_3011468) baseStart_3011468 baseEnd_3011468 := by
    simpa [prefixWord, tailWord_3011468, baseEnd_3011468] using wordTrace_append hprefix tailTrace_3011468
  have hstable : (prefixWord ++ tailWord_3011468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011468).length < 2 ^ (prefixWord ++ tailWord_3011468).sum := by decide
  have hdescent : baseEnd_3011468 < baseStart_3011468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011478 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3011478 : Nat := 118140960795 + 3011478 * 2 ^ 59
def prefixEnd_3011478 : Nat := 4983230072969 + 3 ^ 40 * 3011478 * 2
def baseEnd_3011478 : Nat := 1030890462960449208116981

theorem tailTrace_3011478 : CollatzResearch.WordTrace tailWord_3011478 prefixEnd_3011478 1030890462960449208116981 := by
  unfold tailWord_3011478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864851636496062521277693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73225084122624666893628725 6864851636496062521277693)
  ·
    refine ⟨2574319363686023445479135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6864851636496062521277693 2574319363686023445479135)
    ·
      refine ⟨3861479045529035168218703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574319363686023445479135 3861479045529035168218703)
      ·
        refine ⟨5792218568293552752328055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861479045529035168218703 5792218568293552752328055)
        ·
          refine ⟨8688327852440329128492083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792218568293552752328055 8688327852440329128492083)
          ·
            refine ⟨13032491778660493692738125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688327852440329128492083 13032491778660493692738125)
            ·
              refine ⟨4887184416997685134776797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13032491778660493692738125 4887184416997685134776797)
              ·
                refine ⟨1832694156374131925541299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887184416997685134776797 1832694156374131925541299)
                ·
                  refine ⟨2749041234561197888311949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832694156374131925541299 2749041234561197888311949)
                  ·
                    refine ⟨1030890462960449208116981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749041234561197888311949 1030890462960449208116981)
                    ·
                      rfl

theorem cell22_3011478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3011478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011478 prefixEnd_3011478 := by exact prefixLift 3011478
  have htrace : WordTrace (prefixWord ++ tailWord_3011478) baseStart_3011478 baseEnd_3011478 := by
    simpa [prefixWord, tailWord_3011478, baseEnd_3011478] using wordTrace_append hprefix tailTrace_3011478
  have hstable : (prefixWord ++ tailWord_3011478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011478).length < 2 ^ (prefixWord ++ tailWord_3011478).sum := by decide
  have hdescent : baseEnd_3011478 < baseStart_3011478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011513 : List Nat := [1, 2, 1, 4, 2, 2, 1, 9]
def baseStart_3011513 : Nat := 118140960795 + 3011513 * 2 ^ 59
def prefixEnd_3011513 : Nat := 4983230072969 + 3 ^ 40 * 3011513 * 2
def baseEnd_3011513 : Nat := 114544716019524531499097

theorem tailTrace_3011513 : CollatzResearch.WordTrace tailWord_3011513 prefixEnd_3011513 114544716019524531499097 := by
  unfold tailWord_3011513
  simp only [CollatzResearch.WordTrace]
  refine ⟨109838902738810201317967193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73225935159206800878644795 109838902738810201317967193)
  ·
    refine ⟨82379177054107650988475395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109838902738810201317967193 82379177054107650988475395)
    ·
      refine ⟨123568765581161476482713093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82379177054107650988475395 123568765581161476482713093)
      ·
        refine ⟨23169143546467776840508705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123568765581161476482713093 23169143546467776840508705)
        ·
          refine ⟨17376857659850832630381529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23169143546467776840508705 17376857659850832630381529)
          ·
            refine ⟨13032643244888124472786147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17376857659850832630381529 13032643244888124472786147)
            ·
              refine ⟨19548964867332186709179221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032643244888124472786147 19548964867332186709179221)
              ·
                refine ⟨114544716019524531499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19548964867332186709179221 114544716019524531499097)
                ·
                  rfl

theorem cell22_3011513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 9].length) (baseStart_3011513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011513 prefixEnd_3011513 := by exact prefixLift 3011513
  have htrace : WordTrace (prefixWord ++ tailWord_3011513) baseStart_3011513 baseEnd_3011513 := by
    simpa [prefixWord, tailWord_3011513, baseEnd_3011513] using wordTrace_append hprefix tailTrace_3011513
  have hstable : (prefixWord ++ tailWord_3011513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011513).length < 2 ^ (prefixWord ++ tailWord_3011513).sum := by decide
  have hdescent : baseEnd_3011513 < baseStart_3011513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011603 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 10]
def baseStart_3011603 : Nat := 118140960795 + 3011603 * 2 ^ 59
def prefixEnd_3011603 : Nat := 4983230072969 + 3 ^ 40 * 3011603 * 2
def baseEnd_3011603 : Nat := 343644417671663516247199

theorem tailTrace_3011603 : CollatzResearch.WordTrace tailWord_3011603 prefixEnd_3011603 343644417671663516247199 := by
  unfold tailWord_3011603
  simp only [CollatzResearch.WordTrace]
  refine ⟨109842185308484146688743463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73228123538989431125828975 109842185308484146688743463)
  ·
    refine ⟨164763277962726220033115195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109842185308484146688743463 164763277962726220033115195)
    ·
      refine ⟨247144916944089330049672793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164763277962726220033115195 247144916944089330049672793)
      ·
        refine ⟨185358687708066997537254595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247144916944089330049672793 185358687708066997537254595)
        ·
          refine ⟨278038031562100496305881893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185358687708066997537254595 278038031562100496305881893)
          ·
            refine ⟨52132130917893843057352855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278038031562100496305881893 52132130917893843057352855)
            ·
              refine ⟨78198196376840764586029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52132130917893843057352855 78198196376840764586029283)
              ·
                refine ⟨117297294565261146879043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78198196376840764586029283 117297294565261146879043925)
                ·
                  refine ⟨343644417671663516247199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117297294565261146879043925 343644417671663516247199)
                  ·
                    rfl

theorem cell22_3011603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_3011603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011603 prefixEnd_3011603 := by exact prefixLift 3011603
  have htrace : WordTrace (prefixWord ++ tailWord_3011603) baseStart_3011603 baseEnd_3011603 := by
    simpa [prefixWord, tailWord_3011603, baseEnd_3011603] using wordTrace_append hprefix tailTrace_3011603
  have hstable : (prefixWord ++ tailWord_3011603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011603).length < 2 ^ (prefixWord ++ tailWord_3011603).sum := by decide
  have hdescent : baseEnd_3011603 < baseStart_3011603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011682 : List Nat := [3, 3, 2, 2, 1, 1, 1, 9]
def baseStart_3011682 : Nat := 118140960795 + 3011682 * 2 ^ 59
def prefixEnd_3011682 : Nat := 4983230072969 + 3 ^ 40 * 3011682 * 2
def baseEnd_3011682 : Nat := 114551144036606741779595

theorem tailTrace_3011682 : CollatzResearch.WordTrace tailWord_3011682 prefixEnd_3011682 114551144036606741779595 := by
  unfold tailWord_3011682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27461266668799485795217325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73230044450131962120579533 27461266668799485795217325)
  ·
    refine ⟨10297975000799807173206497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27461266668799485795217325 10297975000799807173206497)
    ·
      refine ⟨7723481250599855379904873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10297975000799807173206497 7723481250599855379904873)
      ·
        refine ⟨5792610937949891534928655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7723481250599855379904873 5792610937949891534928655)
        ·
          refine ⟨8688916406924837302392983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792610937949891534928655 8688916406924837302392983)
          ·
            refine ⟨13033374610387255953589475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688916406924837302392983 13033374610387255953589475)
            ·
              refine ⟨19550061915580883930384213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033374610387255953589475 19550061915580883930384213)
              ·
                refine ⟨114551144036606741779595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19550061915580883930384213 114551144036606741779595)
                ·
                  rfl

theorem cell22_3011682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_3011682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011682 prefixEnd_3011682 := by exact prefixLift 3011682
  have htrace : WordTrace (prefixWord ++ tailWord_3011682) baseStart_3011682 baseEnd_3011682 := by
    simpa [prefixWord, tailWord_3011682, baseEnd_3011682] using wordTrace_append hprefix tailTrace_3011682
  have hstable : (prefixWord ++ tailWord_3011682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011682).length < 2 ^ (prefixWord ++ tailWord_3011682).sum := by decide
  have hdescent : baseEnd_3011682 < baseStart_3011682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011701 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3011701 : Nat := 118140960795 + 3011701 * 2 ^ 59
def prefixEnd_3011701 : Nat := 4983230072969 + 3 ^ 40 * 3011701 * 2
def baseEnd_3011701 : Nat := 1030966800417750959791297

theorem tailTrace_3011701 : CollatzResearch.WordTrace tailWord_3011701 prefixEnd_3011701 1030966800417750959791297 := by
  unfold tailWord_3011701
  simp only [CollatzResearch.WordTrace]
  refine ⟨109845759662129109425810957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73230506441419406283873971 109845759662129109425810957)
  ·
    refine ⟨41192159873298416034679109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109845759662129109425810957 41192159873298416034679109)
    ·
      refine ⟨7723529976243453006502333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41192159873298416034679109 7723529976243453006502333)
      ·
        refine ⟨2896323741091294877438375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7723529976243453006502333 2896323741091294877438375)
        ·
          refine ⟨4344485611636942316157563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896323741091294877438375 4344485611636942316157563)
          ·
            refine ⟨6516728417455413474236345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344485611636942316157563 6516728417455413474236345)
            ·
              refine ⟨4887546313091560105677259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516728417455413474236345 4887546313091560105677259)
              ·
                refine ⟨7331319469637340158515889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4887546313091560105677259 7331319469637340158515889)
                ·
                  refine ⟨5498489602228005118886917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7331319469637340158515889 5498489602228005118886917)
                  ·
                    refine ⟨1030966800417750959791297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498489602228005118886917 1030966800417750959791297)
                    ·
                      rfl

theorem cell22_3011701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3011701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011701 prefixEnd_3011701 := by exact prefixLift 3011701
  have htrace : WordTrace (prefixWord ++ tailWord_3011701) baseStart_3011701 baseEnd_3011701 := by
    simpa [prefixWord, tailWord_3011701, baseEnd_3011701] using wordTrace_append hprefix tailTrace_3011701
  have hstable : (prefixWord ++ tailWord_3011701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011701).length < 2 ^ (prefixWord ++ tailWord_3011701).sum := by decide
  have hdescent : baseEnd_3011701 < baseStart_3011701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011731 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 1, 3]
def baseStart_3011731 : Nat := 118140960795 + 3011731 * 2 ^ 59
def prefixEnd_3011731 : Nat := 4983230072969 + 3 ^ 40 * 3011731 * 2
def baseEnd_3011731 : Nat := 1030977070030840881541205

theorem tailTrace_3011731 : CollatzResearch.WordTrace tailWord_3011731 prefixEnd_3011731 1030977070030840881541205 := by
  unfold tailWord_3011731
  simp only [CollatzResearch.WordTrace]
  refine ⟨109846853852020424549403047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73231235901346949699602031 109846853852020424549403047)
  ·
    refine ⟨164770280778030636824104571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109846853852020424549403047 164770280778030636824104571)
    ·
      refine ⟨247155421167045955236156857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164770280778030636824104571 247155421167045955236156857)
      ·
        refine ⟨185366565875284466427117643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247155421167045955236156857 185366565875284466427117643)
        ·
          refine ⟨278049848812926699640676465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185366565875284466427117643 278049848812926699640676465)
          ·
            refine ⟨208537386609695024730507349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278049848812926699640676465 208537386609695024730507349)
            ·
              refine ⟨2443797499332363571060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 208537386609695024730507349 2443797499332363571060633)
              ·
                refine ⟨1832848124499272678295475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443797499332363571060633 1832848124499272678295475)
                ·
                  refine ⟨2749272186748909017443213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832848124499272678295475 2749272186748909017443213)
                  ·
                    refine ⟨1030977070030840881541205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749272186748909017443213 1030977070030840881541205)
                    ·
                      rfl

theorem cell22_3011731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 3].length) (baseStart_3011731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011731 prefixEnd_3011731 := by exact prefixLift 3011731
  have htrace : WordTrace (prefixWord ++ tailWord_3011731) baseStart_3011731 baseEnd_3011731 := by
    simpa [prefixWord, tailWord_3011731, baseEnd_3011731] using wordTrace_append hprefix tailTrace_3011731
  have hstable : (prefixWord ++ tailWord_3011731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011731).length < 2 ^ (prefixWord ++ tailWord_3011731).sum := by decide
  have hdescent : baseEnd_3011731 < baseStart_3011731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011823 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 4]
def baseStart_3011823 : Nat := 118140960795 + 3011823 * 2 ^ 59
def prefixEnd_3011823 : Nat := 4983230072969 + 3 ^ 40 * 3011823 * 2
def baseEnd_3011823 : Nat := 343669521170327769413641

theorem tailTrace_3011823 : CollatzResearch.WordTrace tailWord_3011823 prefixEnd_3011823 343669521170327769413641 := by
  unfold tailWord_3011823
  simp only [CollatzResearch.WordTrace]
  refine ⟨109850209367687124261752123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73233472911791416174501415 109850209367687124261752123)
  ·
    refine ⟨164775314051530686392628185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109850209367687124261752123 164775314051530686392628185)
    ·
      refine ⟨123581485538648014794471139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164775314051530686392628185 123581485538648014794471139)
      ·
        refine ⟨185372228307972022191706709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123581485538648014794471139 185372228307972022191706709)
        ·
          refine ⟨2172330800484047135059063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 185372228307972022191706709 2172330800484047135059063)
          ·
            refine ⟨3258496200726070702588595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172330800484047135059063 3258496200726070702588595)
            ·
              refine ⟨4887744301089106053882893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258496200726070702588595 4887744301089106053882893)
              ·
                refine ⟨1832904112908414770206085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887744301089106053882893 1832904112908414770206085)
                ·
                  refine ⟨343669521170327769413641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832904112908414770206085 343669521170327769413641)
                  ·
                    rfl

theorem cell22_3011823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 4].length) (baseStart_3011823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011823 prefixEnd_3011823 := by exact prefixLift 3011823
  have htrace : WordTrace (prefixWord ++ tailWord_3011823) baseStart_3011823 baseEnd_3011823 := by
    simpa [prefixWord, tailWord_3011823, baseEnd_3011823] using wordTrace_append hprefix tailTrace_3011823
  have hstable : (prefixWord ++ tailWord_3011823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011823).length < 2 ^ (prefixWord ++ tailWord_3011823).sum := by decide
  have hdescent : baseEnd_3011823 < baseStart_3011823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011900 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3011900 : Nat := 118140960795 + 3011900 * 2 ^ 59
def prefixEnd_3011900 : Nat := 4983230072969 + 3 ^ 40 * 3011900 * 2
def baseEnd_3011900 : Nat := 1031034922184580774065687

theorem tailTrace_3011900 : CollatzResearch.WordTrace tailWord_3011900 prefixEnd_3011900 1031034922184580774065687 := by
  unfold tailWord_3011900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54926508894204083206152577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73235345192272110941536769 54926508894204083206152577)
  ·
    refine ⟨41194881670653062404614433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54926508894204083206152577 41194881670653062404614433)
    ·
      refine ⟨30896161252989796803460825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41194881670653062404614433 30896161252989796803460825)
      ·
        refine ⟨23172120939742347602595619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30896161252989796803460825 23172120939742347602595619)
        ·
          refine ⟨34758181409613521403893429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23172120939742347602595619 34758181409613521403893429)
          ·
            refine ⟨3258579507151267631615009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34758181409613521403893429 3258579507151267631615009)
            ·
              refine ⟨2443934630363450723711257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258579507151267631615009 2443934630363450723711257)
              ·
                refine ⟨1832950972772588042783443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443934630363450723711257 1832950972772588042783443)
                ·
                  refine ⟨2749426459158882064175165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832950972772588042783443 2749426459158882064175165)
                  ·
                    refine ⟨1031034922184580774065687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749426459158882064175165 1031034922184580774065687)
                    ·
                      rfl

theorem cell22_3011900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3011900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011900 prefixEnd_3011900 := by exact prefixLift 3011900
  have htrace : WordTrace (prefixWord ++ tailWord_3011900) baseStart_3011900 baseEnd_3011900 := by
    simpa [prefixWord, tailWord_3011900, baseEnd_3011900] using wordTrace_append hprefix tailTrace_3011900
  have hstable : (prefixWord ++ tailWord_3011900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011900).length < 2 ^ (prefixWord ++ tailWord_3011900).sum := by decide
  have hdescent : baseEnd_3011900 < baseStart_3011900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011907 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 6]
def baseStart_3011907 : Nat := 118140960795 + 3011907 * 2 ^ 59
def prefixEnd_3011907 : Nat := 4983230072969 + 3 ^ 40 * 3011907 * 2
def baseEnd_3011907 : Nat := 343679106142545029713555

theorem tailTrace_3011907 : CollatzResearch.WordTrace tailWord_3011907 prefixEnd_3011907 343679106142545029713555 := by
  unfold tailWord_3011907
  simp only [CollatzResearch.WordTrace]
  refine ⟨109853273099382806607809975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73235515399588537738539983 109853273099382806607809975)
  ·
    refine ⟨164779909649074209911714963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109853273099382806607809975 164779909649074209911714963)
    ·
      refine ⟨247169864473611314867572445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164779909649074209911714963 247169864473611314867572445)
      ·
        refine ⟨92688699177604243075339667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247169864473611314867572445 92688699177604243075339667)
        ·
          refine ⟨139033048766406364613009501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92688699177604243075339667 139033048766406364613009501)
          ·
            refine ⟨52137393287402386729878563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139033048766406364613009501 52137393287402386729878563)
            ·
              refine ⟨78206089931103580094817845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52137393287402386729878563 78206089931103580094817845)
              ·
                refine ⟨7331820931040960633889173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78206089931103580094817845 7331820931040960633889173)
                ·
                  refine ⟨343679106142545029713555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7331820931040960633889173 343679106142545029713555)
                  ·
                    rfl

theorem cell22_3011907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_3011907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011907 prefixEnd_3011907 := by exact prefixLift 3011907
  have htrace : WordTrace (prefixWord ++ tailWord_3011907) baseStart_3011907 baseEnd_3011907 := by
    simpa [prefixWord, tailWord_3011907, baseEnd_3011907] using wordTrace_append hprefix tailTrace_3011907
  have hstable : (prefixWord ++ tailWord_3011907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011907).length < 2 ^ (prefixWord ++ tailWord_3011907).sum := by decide
  have hdescent : baseEnd_3011907 < baseStart_3011907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011924 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3011924 : Nat := 118140960795 + 3011924 * 2 ^ 59
def prefixEnd_3011924 : Nat := 4983230072969 + 3 ^ 40 * 3011924 * 2
def baseEnd_3011924 : Nat := 343681045958350903821871

theorem tailTrace_3011924 : CollatzResearch.WordTrace tailWord_3011924 prefixEnd_3011924 343681045958350903821871 := by
  unfold tailWord_3011924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54926946570160609255589413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73235928760214145674119217 54926946570160609255589413)
  ·
    refine ⟨10298802481905114235423015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54926946570160609255589413 10298802481905114235423015)
    ·
      refine ⟨15448203722857671353134523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10298802481905114235423015 15448203722857671353134523)
      ·
        refine ⟨23172305584286507029701785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15448203722857671353134523 23172305584286507029701785)
        ·
          refine ⟨17379229188214880272276339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23172305584286507029701785 17379229188214880272276339)
          ·
            refine ⟨26068843782322320408414509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17379229188214880272276339 26068843782322320408414509)
            ·
              refine ⟨9775816418370870153155441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26068843782322320408414509 9775816418370870153155441)
              ·
                refine ⟨7331862313778152614866581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9775816418370870153155441 7331862313778152614866581)
                ·
                  refine ⟨343681045958350903821871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7331862313778152614866581 343681045958350903821871)
                  ·
                    rfl

theorem cell22_3011924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3011924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011924 prefixEnd_3011924 := by exact prefixLift 3011924
  have htrace : WordTrace (prefixWord ++ tailWord_3011924) baseStart_3011924 baseEnd_3011924 := by
    simpa [prefixWord, tailWord_3011924, baseEnd_3011924] using wordTrace_append hprefix tailTrace_3011924
  have hstable : (prefixWord ++ tailWord_3011924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011924).length < 2 ^ (prefixWord ++ tailWord_3011924).sum := by decide
  have hdescent : baseEnd_3011924 < baseStart_3011924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011939 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_3011939 : Nat := 118140960795 + 3011939 * 2 ^ 59
def prefixEnd_3011939 : Nat := 4983230072969 + 3 ^ 40 * 3011939 * 2
def baseEnd_3011939 : Nat := 1031048272681597672340567

theorem tailTrace_3011939 : CollatzResearch.WordTrace tailWord_3011939 prefixEnd_3011939 1031048272681597672340567 := by
  unfold tailWord_3011939
  simp only [CollatzResearch.WordTrace]
  refine ⟨109854440235266876072974871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73236293490177917381983247 109854440235266876072974871)
  ·
    refine ⟨164781660352900314109462307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109854440235266876072974871 164781660352900314109462307)
    ·
      refine ⟨247172490529350471164193461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164781660352900314109462307 247172490529350471164193461)
      ·
        refine ⟨23172420987126606671643137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247172490529350471164193461 23172420987126606671643137)
        ·
          refine ⟨17379315740344955003732353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23172420987126606671643137 17379315740344955003732353)
          ·
            refine ⟨13034486805258716252799265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17379315740344955003732353 13034486805258716252799265)
            ·
              refine ⟨9775865103944037189599449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13034486805258716252799265 9775865103944037189599449)
              ·
                refine ⟨7331898827958027892199587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9775865103944037189599449 7331898827958027892199587)
                ·
                  refine ⟨10997848241937041838299381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7331898827958027892199587 10997848241937041838299381)
                  ·
                    refine ⟨1031048272681597672340567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10997848241937041838299381 1031048272681597672340567)
                    ·
                      rfl

theorem cell22_3011939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_3011939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011939 prefixEnd_3011939 := by exact prefixLift 3011939
  have htrace : WordTrace (prefixWord ++ tailWord_3011939) baseStart_3011939 baseEnd_3011939 := by
    simpa [prefixWord, tailWord_3011939, baseEnd_3011939] using wordTrace_append hprefix tailTrace_3011939
  have hstable : (prefixWord ++ tailWord_3011939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011939).length < 2 ^ (prefixWord ++ tailWord_3011939).sum := by decide
  have hdescent : baseEnd_3011939 < baseStart_3011939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011941 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 4]
def baseStart_3011941 : Nat := 118140960795 + 3011941 * 2 ^ 59
def prefixEnd_3011941 : Nat := 4983230072969 + 3 ^ 40 * 3011941 * 2
def baseEnd_3011941 : Nat := 343682985774156777930187

theorem tailTrace_3011941 : CollatzResearch.WordTrace tailWord_3011941 prefixEnd_3011941 343682985774156777930187 := by
  unfold tailWord_3011941
  simp only [CollatzResearch.WordTrace]
  refine ⟨109854513181259630414547677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73236342120839753609698451 109854513181259630414547677)
  ·
    refine ⟨41195442442972361405455379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109854513181259630414547677 41195442442972361405455379)
    ·
      refine ⟨61793163664458542108183069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41195442442972361405455379 61793163664458542108183069)
      ·
        refine ⟨23172436374171953290568651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61793163664458542108183069 23172436374171953290568651)
        ·
          refine ⟨34758654561257929935852977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23172436374171953290568651 34758654561257929935852977)
          ·
            refine ⟨26068990920943447451889733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34758654561257929935852977 26068990920943447451889733)
            ·
              refine ⟨4887935797676896397229325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26068990920943447451889733 4887935797676896397229325)
              ·
                refine ⟨1832975924128836148960997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887935797676896397229325 1832975924128836148960997)
                ·
                  refine ⟨343682985774156777930187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832975924128836148960997 343682985774156777930187)
                  ·
                    rfl

theorem cell22_3011941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_3011941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011941 prefixEnd_3011941 := by exact prefixLift 3011941
  have htrace : WordTrace (prefixWord ++ tailWord_3011941) baseStart_3011941 baseEnd_3011941 := by
    simpa [prefixWord, tailWord_3011941, baseEnd_3011941] using wordTrace_append hprefix tailTrace_3011941
  have hstable : (prefixWord ++ tailWord_3011941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011941).length < 2 ^ (prefixWord ++ tailWord_3011941).sum := by decide
  have hdescent : baseEnd_3011941 < baseStart_3011941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011952 : List Nat := [2, 1, 1, 1, 4, 2, 11]
def baseStart_3011952 : Nat := 118140960795 + 3011952 * 2 ^ 59
def prefixEnd_3011952 : Nat := 4983230072969 + 3 ^ 40 * 3011952 * 2
def baseEnd_3011952 : Nat := 38187137883232221176501

theorem tailTrace_3011952 : CollatzResearch.WordTrace tailWord_3011952 prefixEnd_3011952 38187137883232221176501 := by
  unfold tailWord_3011952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54927457192109889646599055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73236609589479852862132073 54927457192109889646599055)
  ·
    refine ⟨82391185788164834469898583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54927457192109889646599055 82391185788164834469898583)
    ·
      refine ⟨123586778682247251704847875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82391185788164834469898583 123586778682247251704847875)
      ·
        refine ⟨185380168023370877557271813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123586778682247251704847875 185380168023370877557271813)
        ·
          refine ⟨34758781504382039541988465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185380168023370877557271813 34758781504382039541988465)
          ·
            refine ⟨26069086128286529656491349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34758781504382039541988465 26069086128286529656491349)
            ·
              refine ⟨38187137883232221176501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26069086128286529656491349 38187137883232221176501)
              ·
                rfl

theorem cell22_3011952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 11].length) (baseStart_3011952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011952 prefixEnd_3011952 := by exact prefixLift 3011952
  have htrace : WordTrace (prefixWord ++ tailWord_3011952) baseStart_3011952 baseEnd_3011952 := by
    simpa [prefixWord, tailWord_3011952, baseEnd_3011952] using wordTrace_append hprefix tailTrace_3011952
  have hstable : (prefixWord ++ tailWord_3011952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011952).length < 2 ^ (prefixWord ++ tailWord_3011952).sum := by decide
  have hdescent : baseEnd_3011952 < baseStart_3011952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011954 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3011954 : Nat := 118140960795 + 3011954 * 2 ^ 59
def prefixEnd_3011954 : Nat := 4983230072969 + 3 ^ 40 * 3011954 * 2
def baseEnd_3011954 : Nat := 1031053407488142633215521

theorem tailTrace_3011954 : CollatzResearch.WordTrace tailWord_3011954 prefixEnd_3011954 1031053407488142633215521 := by
  unfold tailWord_3011954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27463746832553133408692729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73236658220141689089847277 27463746832553133408692729)
  ·
    refine ⟨20597810124414850056519547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27463746832553133408692729 20597810124414850056519547)
    ·
      refine ⟨30896715186622275084779321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20597810124414850056519547 30896715186622275084779321)
      ·
        refine ⟨23172536389966706313584491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30896715186622275084779321 23172536389966706313584491)
        ·
          refine ⟨34758804584950059470376737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23172536389966706313584491 34758804584950059470376737)
          ·
            refine ⟨26069103438712544602782553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34758804584950059470376737 26069103438712544602782553)
            ·
              refine ⟨19551827579034408452086915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26069103438712544602782553 19551827579034408452086915)
              ·
                refine ⟨29327741368551612678130373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19551827579034408452086915 29327741368551612678130373)
                ·
                  refine ⟨5498951506603427377149445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29327741368551612678130373 5498951506603427377149445)
                  ·
                    refine ⟨1031053407488142633215521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5498951506603427377149445 1031053407488142633215521)
                    ·
                      rfl

theorem cell22_3011954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3011954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011954 prefixEnd_3011954 := by exact prefixLift 3011954
  have htrace : WordTrace (prefixWord ++ tailWord_3011954) baseStart_3011954 baseEnd_3011954 := by
    simpa [prefixWord, tailWord_3011954, baseEnd_3011954] using wordTrace_append hprefix tailTrace_3011954
  have hstable : (prefixWord ++ tailWord_3011954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011954).length < 2 ^ (prefixWord ++ tailWord_3011954).sum := by decide
  have hdescent : baseEnd_3011954 < baseStart_3011954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3011967 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3011967 : Nat := 118140960795 + 3011967 * 2 ^ 59
def prefixEnd_3011967 : Nat := 4983230072969 + 3 ^ 40 * 3011967 * 2
def baseEnd_3011967 : Nat := 1031057857653814932640481

theorem tailTrace_3011967 : CollatzResearch.WordTrace tailWord_3011967 prefixEnd_3011967 1031057857653814932640481 := by
  unfold tailWord_3011967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109855461479165436854994155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73236974319443624569996103 109855461479165436854994155)
  ·
    refine ⟨164783192218748155282491233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109855461479165436854994155 164783192218748155282491233)
    ·
      refine ⟨123587394164061116461868425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164783192218748155282491233 123587394164061116461868425)
      ·
        refine ⟨92690545623045837346401319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123587394164061116461868425 92690545623045837346401319)
        ·
          refine ⟨139035818434568756019601979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92690545623045837346401319 139035818434568756019601979)
          ·
            refine ⟨208553727651853134029402969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139035818434568756019601979 208553727651853134029402969)
            ·
              refine ⟨156415295738889850522052227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208553727651853134029402969 156415295738889850522052227)
              ·
                refine ⟨234622943608334775783078341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156415295738889850522052227 234622943608334775783078341)
                ·
                  refine ⟨43991801926562770459327189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234622943608334775783078341 43991801926562770459327189)
                  ·
                    refine ⟨1031057857653814932640481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43991801926562770459327189 1031057857653814932640481)
                    ·
                      rfl

theorem cell22_3011967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3011967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3011967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3011967 prefixEnd_3011967 := by exact prefixLift 3011967
  have htrace : WordTrace (prefixWord ++ tailWord_3011967) baseStart_3011967 baseEnd_3011967 := by
    simpa [prefixWord, tailWord_3011967, baseEnd_3011967] using wordTrace_append hprefix tailTrace_3011967
  have hstable : (prefixWord ++ tailWord_3011967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3011967).length < 2 ^ (prefixWord ++ tailWord_3011967).sum := by decide
  have hdescent : baseEnd_3011967 < baseStart_3011967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3011967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012029 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3012029 : Nat := 118140960795 + 3012029 * 2 ^ 59
def prefixEnd_3012029 : Nat := 4983230072969 + 3 ^ 40 * 3012029 * 2
def baseEnd_3012029 : Nat := 1031079081520867437590291

theorem tailTrace_3012029 : CollatzResearch.WordTrace tailWord_3012029 prefixEnd_3012029 1031079081520867437590291 := by
  unfold tailWord_3012029
  simp only [CollatzResearch.WordTrace]
  refine ⟨109857722804940821443751141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73238481869960547629167427 109857722804940821443751141)
  ·
    refine ⟨20598323025926404020703339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109857722804940821443751141 20598323025926404020703339)
    ·
      refine ⟨30897484538889606031055009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20598323025926404020703339 30897484538889606031055009)
      ·
        refine ⟨23173113404167204523291257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30897484538889606031055009 23173113404167204523291257)
        ·
          refine ⟨17379835053125403392468443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23173113404167204523291257 17379835053125403392468443)
          ·
            refine ⟨26069752579688105088702665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17379835053125403392468443 26069752579688105088702665)
            ·
              refine ⟨19552314434766078816526999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26069752579688105088702665 19552314434766078816526999)
              ·
                refine ⟨29328471652149118224790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19552314434766078816526999 29328471652149118224790499)
                ·
                  refine ⟨43992707478223677337185749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29328471652149118224790499 43992707478223677337185749)
                  ·
                    refine ⟨1031079081520867437590291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43992707478223677337185749 1031079081520867437590291)
                    ·
                      rfl

theorem cell22_3012029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3012029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012029 prefixEnd_3012029 := by exact prefixLift 3012029
  have htrace : WordTrace (prefixWord ++ tailWord_3012029) baseStart_3012029 baseEnd_3012029 := by
    simpa [prefixWord, tailWord_3012029, baseEnd_3012029] using wordTrace_append hprefix tailTrace_3012029
  have hstable : (prefixWord ++ tailWord_3012029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012029).length < 2 ^ (prefixWord ++ tailWord_3012029).sum := by decide
  have hdescent : baseEnd_3012029 < baseStart_3012029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012089 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_3012089 : Nat := 118140960795 + 3012089 * 2 ^ 59
def prefixEnd_3012089 : Nat := 4983230072969 + 3 ^ 40 * 3012089 * 2
def baseEnd_3012089 : Nat := 1031099620747047281090107

theorem tailTrace_3012089 : CollatzResearch.WordTrace tailWord_3012089 prefixEnd_3012089 1031099620747047281090107 := by
  unfold tailWord_3012089
  simp only [CollatzResearch.WordTrace]
  refine ⟨109859911184723451690935321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73239940789815634460623547 109859911184723451690935321)
  ·
    refine ⟨82394933388542588768201491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109859911184723451690935321 82394933388542588768201491)
    ·
      refine ⟨123592400082813883152302237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82394933388542588768201491 123592400082813883152302237)
      ·
        refine ⟨46347150031055206182113339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123592400082813883152302237 46347150031055206182113339)
        ·
          refine ⟨69520725046582809273170009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46347150031055206182113339 69520725046582809273170009)
          ·
            refine ⟨52140543784937106954877507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69520725046582809273170009 52140543784937106954877507)
            ·
              refine ⟨78210815677405660432316261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52140543784937106954877507 78210815677405660432316261)
              ·
                refine ⟨14664527939513561331059299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78210815677405660432316261 14664527939513561331059299)
                ·
                  refine ⟨21996791909270341996588949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664527939513561331059299 21996791909270341996588949)
                  ·
                    refine ⟨1031099620747047281090107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21996791909270341996588949 1031099620747047281090107)
                    ·
                      rfl

theorem cell22_3012089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_3012089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012089 prefixEnd_3012089 := by exact prefixLift 3012089
  have htrace : WordTrace (prefixWord ++ tailWord_3012089) baseStart_3012089 baseEnd_3012089 := by
    simpa [prefixWord, tailWord_3012089, baseEnd_3012089] using wordTrace_append hprefix tailTrace_3012089
  have hstable : (prefixWord ++ tailWord_3012089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012089).length < 2 ^ (prefixWord ++ tailWord_3012089).sum := by decide
  have hdescent : baseEnd_3012089 < baseStart_3012089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012104 : List Nat := [2, 1, 3, 2, 1, 1, 2, 10]
def baseStart_3012104 : Nat := 118140960795 + 3012104 * 2 ^ 59
def prefixEnd_3012104 : Nat := 4983230072969 + 3 ^ 40 * 3012104 * 2
def baseEnd_3012104 : Nat := 114567195061510249107229

theorem tailTrace_3012104 : CollatzResearch.WordTrace tailWord_3012104 prefixEnd_3012104 114567195061510249107229 := by
  unfold tailWord_3012104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54930229139834554626365683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73240305519779406168487577 54930229139834554626365683)
  ·
    refine ⟨82395343709751831939548525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54930229139834554626365683 82395343709751831939548525)
    ·
      refine ⟨30898253891156936977330697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82395343709751831939548525 30898253891156936977330697)
      ·
        refine ⟨23173690418367702732998023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30898253891156936977330697 23173690418367702732998023)
        ·
          refine ⟨34760535627551554099497035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23173690418367702732998023 34760535627551554099497035)
          ·
            refine ⟨52140803441327331149245553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34760535627551554099497035 52140803441327331149245553)
            ·
              refine ⟨39105602580995498361934165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52140803441327331149245553 39105602580995498361934165)
              ·
                refine ⟨114567195061510249107229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39105602580995498361934165 114567195061510249107229)
                ·
                  rfl

theorem cell22_3012104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_3012104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012104 prefixEnd_3012104 := by exact prefixLift 3012104
  have htrace : WordTrace (prefixWord ++ tailWord_3012104) baseStart_3012104 baseEnd_3012104 := by
    simpa [prefixWord, tailWord_3012104, baseEnd_3012104] using wordTrace_append hprefix tailTrace_3012104
  have hstable : (prefixWord ++ tailWord_3012104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012104).length < 2 ^ (prefixWord ++ tailWord_3012104).sum := by decide
  have hdescent : baseEnd_3012104 < baseStart_3012104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012106 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_3012106 : Nat := 118140960795 + 3012106 * 2 ^ 59
def prefixEnd_3012106 : Nat := 4983230072969 + 3 ^ 40 * 3012106 * 2
def baseEnd_3012106 : Nat := 1031105440194464903415055

theorem tailTrace_3012106 : CollatzResearch.WordTrace tailWord_3012106 prefixEnd_3012106 1031105440194464903415055 := by
  unfold tailWord_3012106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27465132806415465898576043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73240354150441242396202781 27465132806415465898576043)
  ·
    refine ⟨41197699209623198847864065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27465132806415465898576043 41197699209623198847864065)
    ·
      refine ⟨30898274407217399135898049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41197699209623198847864065 30898274407217399135898049)
      ·
        refine ⟨23173705805413049351923537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30898274407217399135898049 23173705805413049351923537)
        ·
          refine ⟨17380279354059787013942653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23173705805413049351923537 17380279354059787013942653)
          ·
            refine ⟨6517604757772420130228495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17380279354059787013942653 6517604757772420130228495)
            ·
              refine ⟨9776407136658630195342743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517604757772420130228495 9776407136658630195342743)
              ·
                refine ⟨14664610704987945293014115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776407136658630195342743 14664610704987945293014115)
                ·
                  refine ⟨21996916057481917939521173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664610704987945293014115 21996916057481917939521173)
                  ·
                    refine ⟨1031105440194464903415055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21996916057481917939521173 1031105440194464903415055)
                    ·
                      rfl

theorem cell22_3012106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_3012106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012106 prefixEnd_3012106 := by exact prefixLift 3012106
  have htrace : WordTrace (prefixWord ++ tailWord_3012106) baseStart_3012106 baseEnd_3012106 := by
    simpa [prefixWord, tailWord_3012106, baseEnd_3012106] using wordTrace_append hprefix tailTrace_3012106
  have hstable : (prefixWord ++ tailWord_3012106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012106).length < 2 ^ (prefixWord ++ tailWord_3012106).sum := by decide
  have hdescent : baseEnd_3012106 < baseStart_3012106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012110 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_3012110 : Nat := 118140960795 + 3012110 * 2 ^ 59
def prefixEnd_3012110 : Nat := 4983230072969 + 3 ^ 40 * 3012110 * 2
def baseEnd_3012110 : Nat := 343702269825403408771681

theorem tailTrace_3012110 : CollatzResearch.WordTrace tailWord_3012110 prefixEnd_3012110 343702269825403408771681 := by
  unfold tailWord_3012110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732584639705921534681223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73240451411764914851633189 13732584639705921534681223)
  ·
    refine ⟨20598876959558882302021835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732584639705921534681223 20598876959558882302021835)
    ·
      refine ⟨30898315439338323453032753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20598876959558882302021835 30898315439338323453032753)
      ·
        refine ⟨23173736579503742589774565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30898315439338323453032753 23173736579503742589774565)
        ·
          refine ⟨4345075608656951735582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23173736579503742589774565 4345075608656951735582731)
          ·
            refine ⟨6517613412985427603374097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345075608656951735582731 6517613412985427603374097)
            ·
              refine ⟨4888210059739070702530573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6517613412985427603374097 4888210059739070702530573)
              ·
                refine ⟨1833078772402151513448965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4888210059739070702530573 1833078772402151513448965)
                ·
                  refine ⟨343702269825403408771681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833078772402151513448965 343702269825403408771681)
                  ·
                    rfl

theorem cell22_3012110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_3012110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012110 prefixEnd_3012110 := by exact prefixLift 3012110
  have htrace : WordTrace (prefixWord ++ tailWord_3012110) baseStart_3012110 baseEnd_3012110 := by
    simpa [prefixWord, tailWord_3012110, baseEnd_3012110] using wordTrace_append hprefix tailTrace_3012110
  have hstable : (prefixWord ++ tailWord_3012110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012110).length < 2 ^ (prefixWord ++ tailWord_3012110).sum := by decide
  have hdescent : baseEnd_3012110 < baseStart_3012110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012142 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3012142 : Nat := 118140960795 + 3012142 * 2 ^ 59
def prefixEnd_3012142 : Nat := 4983230072969 + 3 ^ 40 * 3012142 * 2
def baseEnd_3012142 : Nat := 1031117763730172809514945

theorem tailTrace_3012142 : CollatzResearch.WordTrace tailWord_3012142 prefixEnd_3012142 1031117763730172809514945 := by
  unfold tailWord_3012142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732730531691430217826835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73241229502354294495076453 13732730531691430217826835)
  ·
    refine ⟨20599095797537145326740253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732730531691430217826835 20599095797537145326740253)
    ·
      refine ⟨7724660924076429497527595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20599095797537145326740253 7724660924076429497527595)
      ·
        refine ⟨11586991386114644246291393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724660924076429497527595 11586991386114644246291393)
        ·
          refine ⟨8690243539585983184718545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11586991386114644246291393 8690243539585983184718545)
          ·
            refine ⟨6517682654689487388538909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8690243539585983184718545 6517682654689487388538909)
            ·
              refine ⟨2444130995508557770702091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6517682654689487388538909 2444130995508557770702091)
              ·
                refine ⟨3666196493262836656053137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444130995508557770702091 3666196493262836656053137)
                ·
                  refine ⟨2749647369947127492039853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666196493262836656053137 2749647369947127492039853)
                  ·
                    refine ⟨1031117763730172809514945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749647369947127492039853 1031117763730172809514945)
                    ·
                      rfl

theorem cell22_3012142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3012142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012142 prefixEnd_3012142 := by exact prefixLift 3012142
  have htrace : WordTrace (prefixWord ++ tailWord_3012142) baseStart_3012142 baseEnd_3012142 := by
    simpa [prefixWord, tailWord_3012142, baseEnd_3012142] using wordTrace_append hprefix tailTrace_3012142
  have hstable : (prefixWord ++ tailWord_3012142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012142).length < 2 ^ (prefixWord ++ tailWord_3012142).sum := by decide
  have hdescent : baseEnd_3012142 < baseStart_3012142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012153 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_3012153 : Nat := 118140960795 + 3012153 * 2 ^ 59
def prefixEnd_3012153 : Nat := 4983230072969 + 3 ^ 40 * 3012153 * 2
def baseEnd_3012153 : Nat := 1031121529254972447489911

theorem tailTrace_3012153 : CollatzResearch.WordTrace tailWord_3012153 prefixEnd_3012153 1031121529254972447489911 := by
  unfold tailWord_3012153
  simp only [CollatzResearch.WordTrace]
  refine ⟨109862245456491590621265113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73241496970994393747510075 109862245456491590621265113)
  ·
    refine ⟨82396684092368692965948835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109862245456491590621265113 82396684092368692965948835)
    ·
      refine ⟨123595026138553039448923253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82396684092368692965948835 123595026138553039448923253)
      ·
        refine ⟨11587033700489347448336555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123595026138553039448923253 11587033700489347448336555)
        ·
          refine ⟨17380550550734021172504833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11587033700489347448336555 17380550550734021172504833)
          ·
            refine ⟨13035412913050515879378625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17380550550734021172504833 13035412913050515879378625)
            ·
              refine ⟨9776559684787886909533969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13035412913050515879378625 9776559684787886909533969)
              ·
                refine ⟨7332419763590915182150477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776559684787886909533969 7332419763590915182150477)
                ·
                  refine ⟨2749657411346593193306429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7332419763590915182150477 2749657411346593193306429)
                  ·
                    refine ⟨1031121529254972447489911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749657411346593193306429 1031121529254972447489911)
                    ·
                      rfl

theorem cell22_3012153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_3012153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012153 prefixEnd_3012153 := by exact prefixLift 3012153
  have htrace : WordTrace (prefixWord ++ tailWord_3012153) baseStart_3012153 baseEnd_3012153 := by
    simpa [prefixWord, tailWord_3012153, baseEnd_3012153] using wordTrace_append hprefix tailTrace_3012153
  have hstable : (prefixWord ++ tailWord_3012153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012153).length < 2 ^ (prefixWord ++ tailWord_3012153).sum := by decide
  have hdescent : baseEnd_3012153 < baseStart_3012153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012200 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_3012200 : Nat := 118140960795 + 3012200 * 2 ^ 59
def prefixEnd_3012200 : Nat := 4983230072969 + 3 ^ 40 * 3012200 * 2
def baseEnd_3012200 : Nat := 343712539438493330521589

theorem tailTrace_3012200 : CollatzResearch.WordTrace tailWord_3012200 prefixEnd_3012200 343712539438493330521589 := by
  unfold tailWord_3012200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54931979843660658824113027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73242639791547545098817369 54931979843660658824113027)
  ·
    refine ⟨82397969765490988236169541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54931979843660658824113027 82397969765490988236169541)
    ·
      refine ⟨15449619331029560294281789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82397969765490988236169541 15449619331029560294281789)
      ·
        refine ⟨5793607249136085110355671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15449619331029560294281789 5793607249136085110355671)
        ·
          refine ⟨8690410873704127665533507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793607249136085110355671 8690410873704127665533507)
          ·
            refine ⟨13035616310556191498300261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690410873704127665533507 13035616310556191498300261)
            ·
              refine ⟨2444178058229285905931299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13035616310556191498300261 2444178058229285905931299)
              ·
                refine ⟨3666267087343928858896949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444178058229285905931299 3666267087343928858896949)
                ·
                  refine ⟨343712539438493330521589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3666267087343928858896949 343712539438493330521589)
                  ·
                    rfl

theorem cell22_3012200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_3012200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012200 prefixEnd_3012200 := by exact prefixLift 3012200
  have htrace : WordTrace (prefixWord ++ tailWord_3012200) baseStart_3012200 baseEnd_3012200 := by
    simpa [prefixWord, tailWord_3012200, baseEnd_3012200] using wordTrace_append hprefix tailTrace_3012200
  have hstable : (prefixWord ++ tailWord_3012200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012200).length < 2 ^ (prefixWord ++ tailWord_3012200).sum := by decide
  have hdescent : baseEnd_3012200 < baseStart_3012200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012241 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3012241 : Nat := 118140960795 + 3012241 * 2 ^ 59
def prefixEnd_3012241 : Nat := 4983230072969 + 3 ^ 40 * 3012241 * 2
def baseEnd_3012241 : Nat := 1031151653453369551289641

theorem tailTrace_3012241 : CollatzResearch.WordTrace tailWord_3012241 prefixEnd_3012241 1031151653453369551289641 := by
  unfold tailWord_3012241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109865455080172781650468577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73243636720115187766979051 109865455080172781650468577)
  ·
    refine ⟨82399091310129586237851433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109865455080172781650468577 82399091310129586237851433)
    ·
      refine ⟨61799318482597189678388575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82399091310129586237851433 61799318482597189678388575)
      ·
        refine ⟨92698977723895784517582863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61799318482597189678388575 92698977723895784517582863)
        ·
          refine ⟨139048466585843676776374295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92698977723895784517582863 139048466585843676776374295)
          ·
            refine ⟨208572699878765515164561443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139048466585843676776374295 208572699878765515164561443)
            ·
              refine ⟨312859049818148272746842165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208572699878765515164561443 312859049818148272746842165)
              ·
                refine ⟨29330535920451400570016453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312859049818148272746842165 29330535920451400570016453)
                ·
                  refine ⟨5499475485084637606878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29330535920451400570016453 5499475485084637606878085)
                  ·
                    refine ⟨1031151653453369551289641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499475485084637606878085 1031151653453369551289641)
                    ·
                      rfl

theorem cell22_3012241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3012241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012241 prefixEnd_3012241 := by exact prefixLift 3012241
  have htrace : WordTrace (prefixWord ++ tailWord_3012241) baseStart_3012241 baseEnd_3012241 := by
    simpa [prefixWord, tailWord_3012241, baseEnd_3012241] using wordTrace_append hprefix tailTrace_3012241
  have hstable : (prefixWord ++ tailWord_3012241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012241).length < 2 ^ (prefixWord ++ tailWord_3012241).sum := by decide
  have hdescent : baseEnd_3012241 < baseStart_3012241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012260 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_3012260 : Nat := 118140960795 + 3012260 * 2 ^ 59
def prefixEnd_3012260 : Nat := 4983230072969 + 3 ^ 40 * 3012260 * 2
def baseEnd_3012260 : Nat := 1031158157541659835064583

theorem tailTrace_3012260 : CollatzResearch.WordTrace tailWord_3012260 prefixEnd_3012260 1031158157541659835064583 := by
  unfold tailWord_3012260
  simp only [CollatzResearch.WordTrace]
  refine ⟨54933074033551973947705117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73244098711402631930273489 54933074033551973947705117)
  ·
    refine ⟨20599902762581990230389419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54933074033551973947705117 20599902762581990230389419)
    ·
      refine ⟨30899854143872985345584129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20599902762581990230389419 30899854143872985345584129)
      ·
        refine ⟨23174890607904739009188097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30899854143872985345584129 23174890607904739009188097)
        ·
          refine ⟨17381167955928554256891073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23174890607904739009188097 17381167955928554256891073)
          ·
            refine ⟨13035875966946415692668305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17381167955928554256891073 13035875966946415692668305)
            ·
              refine ⟨9776906975209811769501229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13035875966946415692668305 9776906975209811769501229)
              ·
                refine ⟨3666340115703679413562961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9776906975209811769501229 3666340115703679413562961)
                ·
                  refine ⟨2749755086777759560172221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666340115703679413562961 2749755086777759560172221)
                  ·
                    refine ⟨1031158157541659835064583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749755086777759560172221 1031158157541659835064583)
                    ·
                      rfl

theorem cell22_3012260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_3012260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012260 prefixEnd_3012260 := by exact prefixLift 3012260
  have htrace : WordTrace (prefixWord ++ tailWord_3012260) baseStart_3012260 baseEnd_3012260 := by
    simpa [prefixWord, tailWord_3012260, baseEnd_3012260] using wordTrace_append hprefix tailTrace_3012260
  have hstable : (prefixWord ++ tailWord_3012260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012260).length < 2 ^ (prefixWord ++ tailWord_3012260).sum := by decide
  have hdescent : baseEnd_3012260 < baseStart_3012260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012288 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_3012288 : Nat := 118140960795 + 3012288 * 2 ^ 59
def prefixEnd_3012288 : Nat := 4983230072969 + 3 ^ 40 * 3012288 * 2
def baseEnd_3012288 : Nat := 1031167742513877095364497

theorem tailTrace_3012288 : CollatzResearch.WordTrace tailWord_3012288 prefixEnd_3012288 1031167742513877095364497 := by
  unfold tailWord_3012288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54933584655501254338714759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73244779540668339118286345 54933584655501254338714759)
  ·
    refine ⟨82400376983251881508072139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54933584655501254338714759 82400376983251881508072139)
    ·
      refine ⟨123600565474877822262108209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82400376983251881508072139 123600565474877822262108209)
      ·
        refine ⟨92700424106158366696581157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123600565474877822262108209 92700424106158366696581157)
        ·
          refine ⟨17381329519904693755608967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92700424106158366696581157 17381329519904693755608967)
          ·
            refine ⟨26071994279857040633413451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17381329519904693755608967 26071994279857040633413451)
            ·
              refine ⟨39107991419785560950120177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26071994279857040633413451 39107991419785560950120177)
              ·
                refine ⟨29330993564839170712590133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39107991419785560950120177 29330993564839170712590133)
                ·
                  refine ⟨2749780646703672254305325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29330993564839170712590133 2749780646703672254305325)
                  ·
                    refine ⟨1031167742513877095364497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749780646703672254305325 1031167742513877095364497)
                    ·
                      rfl

theorem cell22_3012288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_3012288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012288 prefixEnd_3012288 := by exact prefixLift 3012288
  have htrace : WordTrace (prefixWord ++ tailWord_3012288) baseStart_3012288 baseEnd_3012288 := by
    simpa [prefixWord, tailWord_3012288, baseEnd_3012288] using wordTrace_append hprefix tailTrace_3012288
  have hstable : (prefixWord ++ tailWord_3012288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012288).length < 2 ^ (prefixWord ++ tailWord_3012288).sum := by decide
  have hdescent : baseEnd_3012288 < baseStart_3012288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012294 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3012294 : Nat := 118140960795 + 3012294 * 2 ^ 59
def prefixEnd_3012294 : Nat := 4983230072969 + 3 ^ 40 * 3012294 * 2
def baseEnd_3012294 : Nat := 1031169796436495079714479

theorem tailTrace_3012294 : CollatzResearch.WordTrace tailWord_3012294 prefixEnd_3012294 1031169796436495079714479 := by
  unfold tailWord_3012294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433355879655649115692123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73244925432653847801431957 3433355879655649115692123)
  ·
    refine ⟨5150033819483473673538185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433355879655649115692123 5150033819483473673538185)
    ·
      refine ⟨3862525364612605255153639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5150033819483473673538185 3862525364612605255153639)
      ·
        refine ⟨5793788046918907882730459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862525364612605255153639 5793788046918907882730459)
        ·
          refine ⟨8690682070378361824095689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793788046918907882730459 8690682070378361824095689)
          ·
            refine ⟨6518011552783771368071767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8690682070378361824095689 6518011552783771368071767)
            ·
              refine ⟨9777017329175657052107651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518011552783771368071767 9777017329175657052107651)
              ·
                refine ⟨14665525993763485578161477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9777017329175657052107651 14665525993763485578161477)
                ·
                  refine ⟨2749786123830653545905277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14665525993763485578161477 2749786123830653545905277)
                  ·
                    refine ⟨1031169796436495079714479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749786123830653545905277 1031169796436495079714479)
                    ·
                      rfl

theorem cell22_3012294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3012294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012294 prefixEnd_3012294 := by exact prefixLift 3012294
  have htrace : WordTrace (prefixWord ++ tailWord_3012294) baseStart_3012294 baseEnd_3012294 := by
    simpa [prefixWord, tailWord_3012294, baseEnd_3012294] using wordTrace_append hprefix tailTrace_3012294
  have hstable : (prefixWord ++ tailWord_3012294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012294).length < 2 ^ (prefixWord ++ tailWord_3012294).sum := by decide
  have hdescent : baseEnd_3012294 < baseStart_3012294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012305 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_3012305 : Nat := 118140960795 + 3012305 * 2 ^ 59
def prefixEnd_3012305 : Nat := 4983230072969 + 3 ^ 40 * 3012305 * 2
def baseEnd_3012305 : Nat := 1031173561961294717689445

theorem tailTrace_3012305 : CollatzResearch.WordTrace tailWord_3012305 prefixEnd_3012305 1031173561961294717689445 := by
  unfold tailWord_3012305
  simp only [CollatzResearch.WordTrace]
  refine ⟨109867789351940920580798369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73245192901293947053865579 109867789351940920580798369)
  ·
    refine ⟨82400842013955690435598777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109867789351940920580798369 82400842013955690435598777)
    ·
      refine ⟨61800631510466767826699083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82400842013955690435598777 61800631510466767826699083)
      ·
        refine ⟨92700947265700151740048625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61800631510466767826699083 92700947265700151740048625)
        ·
          refine ⟨69525710449275113805036469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92700947265700151740048625 69525710449275113805036469)
          ·
            refine ⟨6518035354619541919222169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69525710449275113805036469 6518035354619541919222169)
            ·
              refine ⟨4888526515964656439416627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518035354619541919222169 4888526515964656439416627)
              ·
                refine ⟨7332789773946984659124941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888526515964656439416627 7332789773946984659124941)
                ·
                  refine ⟨2749796165230119247171853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7332789773946984659124941 2749796165230119247171853)
                  ·
                    refine ⟨1031173561961294717689445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749796165230119247171853 1031173561961294717689445)
                    ·
                      rfl

theorem cell22_3012305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_3012305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012305 prefixEnd_3012305 := by exact prefixLift 3012305
  have htrace : WordTrace (prefixWord ++ tailWord_3012305) baseStart_3012305 baseEnd_3012305 := by
    simpa [prefixWord, tailWord_3012305, baseEnd_3012305] using wordTrace_append hprefix tailTrace_3012305
  have hstable : (prefixWord ++ tailWord_3012305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012305).length < 2 ^ (prefixWord ++ tailWord_3012305).sum := by decide
  have hdescent : baseEnd_3012305 < baseStart_3012305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012363 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 6]
def baseStart_3012363 : Nat := 118140960795 + 3012363 * 2 ^ 59
def prefixEnd_3012363 : Nat := 4983230072969 + 3 ^ 40 * 3012363 * 2
def baseEnd_3012363 : Nat := 343731138848867299913089

theorem tailTrace_3012363 : CollatzResearch.WordTrace tailWord_3012363 prefixEnd_3012363 343731138848867299913089 := by
  unfold tailWord_3012363
  simp only [CollatzResearch.WordTrace]
  refine ⟨109869904785730796486409743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73246603190487197657606495 109869904785730796486409743)
  ·
    refine ⟨164804857178596194729614615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109869904785730796486409743 164804857178596194729614615)
    ·
      refine ⟨247207285767894292094421923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164804857178596194729614615 247207285767894292094421923)
      ·
        refine ⟨370810928651841438141632885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247207285767894292094421923 370810928651841438141632885)
        ·
          refine ⟨34763524561110134825778083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370810928651841438141632885 34763524561110134825778083)
          ·
            refine ⟨52145286841665202238667125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34763524561110134825778083 52145286841665202238667125)
            ·
              refine ⟨4888620641406112709875043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52145286841665202238667125 4888620641406112709875043)
              ·
                refine ⟨7332930962109169064812565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888620641406112709875043 7332930962109169064812565)
                ·
                  refine ⟨343731138848867299913089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7332930962109169064812565 343731138848867299913089)
                  ·
                    rfl

theorem cell22_3012363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_3012363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012363 prefixEnd_3012363 := by exact prefixLift 3012363
  have htrace : WordTrace (prefixWord ++ tailWord_3012363) baseStart_3012363 baseEnd_3012363 := by
    simpa [prefixWord, tailWord_3012363, baseEnd_3012363] using wordTrace_append hprefix tailTrace_3012363
  have hstable : (prefixWord ++ tailWord_3012363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012363).length < 2 ^ (prefixWord ++ tailWord_3012363).sum := by decide
  have hdescent : baseEnd_3012363 < baseStart_3012363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012410 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_3012410 : Nat := 118140960795 + 3012410 * 2 ^ 59
def prefixEnd_3012410 : Nat := 4983230072969 + 3 ^ 40 * 3012410 * 2
def baseEnd_3012410 : Nat := 1031209505607109443814123

theorem tailTrace_3012410 : CollatzResearch.WordTrace tailWord_3012410 prefixEnd_3012410 1031209505607109443814123 := by
  unfold tailWord_3012410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27467904754140130878342671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73247746011040349008913789 27467904754140130878342671)
  ·
    refine ⟨41201857131210196317514007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27467904754140130878342671 41201857131210196317514007)
    ·
      refine ⟨61802785696815294476271011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41201857131210196317514007 61802785696815294476271011)
      ·
        refine ⟨92704178545222941714406517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61802785696815294476271011 92704178545222941714406517)
        ·
          refine ⟨8691016738614650785725611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92704178545222941714406517 8691016738614650785725611)
          ·
            refine ⟨13036525107921976178588417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691016738614650785725611 13036525107921976178588417)
            ·
              refine ⟨9777393830941482133941313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13036525107921976178588417 9777393830941482133941313)
              ·
                refine ⟨7333045373206111600455985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9777393830941482133941313 7333045373206111600455985)
                ·
                  refine ⟨5499784029904583700341989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333045373206111600455985 5499784029904583700341989)
                  ·
                    refine ⟨1031209505607109443814123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499784029904583700341989 1031209505607109443814123)
                    ·
                      rfl

theorem cell22_3012410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_3012410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012410 prefixEnd_3012410 := by exact prefixLift 3012410
  have htrace : WordTrace (prefixWord ++ tailWord_3012410) baseStart_3012410 baseEnd_3012410 := by
    simpa [prefixWord, tailWord_3012410, baseEnd_3012410] using wordTrace_append hprefix tailTrace_3012410
  have hstable : (prefixWord ++ tailWord_3012410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012410).length < 2 ^ (prefixWord ++ tailWord_3012410).sum := by decide
  have hdescent : baseEnd_3012410 < baseStart_3012410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012414 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3012414 : Nat := 118140960795 + 3012414 * 2 ^ 59
def prefixEnd_3012414 : Nat := 4983230072969 + 3 ^ 40 * 3012414 * 2
def baseEnd_3012414 : Nat := 343736958296284922238037

theorem tailTrace_3012414 : CollatzResearch.WordTrace tailWord_3012414 prefixEnd_3012414 343736958296284922238037 := by
  unfold tailWord_3012414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733970613568254024564537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73247843272364021464344197 13733970613568254024564537)
  ·
    refine ⟨10300477960176190518423403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13733970613568254024564537 10300477960176190518423403)
    ·
      refine ⟨15450716940264285777635105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10300477960176190518423403 15450716940264285777635105)
      ·
        refine ⟨11588037705198214333226329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15450716940264285777635105 11588037705198214333226329)
        ·
          refine ⟨8691028278898660749919747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588037705198214333226329 8691028278898660749919747)
          ·
            refine ⟨13036542418347991124879621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691028278898660749919747 13036542418347991124879621)
            ·
              refine ⟨2444351703440248335914929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13036542418347991124879621 2444351703440248335914929)
              ·
                refine ⟨1833263777580186251936197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444351703440248335914929 1833263777580186251936197)
                ·
                  refine ⟨343736958296284922238037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833263777580186251936197 343736958296284922238037)
                  ·
                    rfl

theorem cell22_3012414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3012414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012414 prefixEnd_3012414 := by exact prefixLift 3012414
  have htrace : WordTrace (prefixWord ++ tailWord_3012414) baseStart_3012414 baseEnd_3012414 := by
    simpa [prefixWord, tailWord_3012414, baseEnd_3012414] using wordTrace_append hprefix tailTrace_3012414
  have hstable : (prefixWord ++ tailWord_3012414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012414).length < 2 ^ (prefixWord ++ tailWord_3012414).sum := by decide
  have hdescent : baseEnd_3012414 < baseStart_3012414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012429 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3012429 : Nat := 118140960795 + 3012429 * 2 ^ 59
def prefixEnd_3012429 : Nat := 4983230072969 + 3 ^ 40 * 3012429 * 2
def baseEnd_3012429 : Nat := 1031216009695399727589065

theorem tailTrace_3012429 : CollatzResearch.WordTrace tailWord_3012429 prefixEnd_3012429 1031216009695399727589065 := by
  unfold tailWord_3012429
  simp only [CollatzResearch.WordTrace]
  refine ⟨109872312003491689758312341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73248208002327793172208227 109872312003491689758312341)
  ·
    refine ⟨5150264625163672957420891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109872312003491689758312341 5150264625163672957420891)
    ·
      refine ⟨7725396937745509436131337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150264625163672957420891 7725396937745509436131337)
      ·
        refine ⟨5794047703309132077098503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7725396937745509436131337 5794047703309132077098503)
        ·
          refine ⟨8691071554963698115647755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794047703309132077098503 8691071554963698115647755)
          ·
            refine ⟨13036607332445547173471633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691071554963698115647755 13036607332445547173471633)
            ·
              refine ⟨9777455499334160380103725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13036607332445547173471633 9777455499334160380103725)
              ·
                refine ⟨3666545812250310142538897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9777455499334160380103725 3666545812250310142538897)
                ·
                  refine ⟨2749909359187732606904173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666545812250310142538897 2749909359187732606904173)
                  ·
                    refine ⟨1031216009695399727589065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749909359187732606904173 1031216009695399727589065)
                    ·
                      rfl

theorem cell22_3012429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3012429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012429 prefixEnd_3012429 := by exact prefixLift 3012429
  have htrace : WordTrace (prefixWord ++ tailWord_3012429) baseStart_3012429 baseEnd_3012429 := by
    simpa [prefixWord, tailWord_3012429, baseEnd_3012429] using wordTrace_append hprefix tailTrace_3012429
  have hstable : (prefixWord ++ tailWord_3012429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012429).length < 2 ^ (prefixWord ++ tailWord_3012429).sum := by decide
  have hdescent : baseEnd_3012429 < baseStart_3012429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012444 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3012444 : Nat := 118140960795 + 3012444 * 2 ^ 59
def prefixEnd_3012444 : Nat := 4983230072969 + 3 ^ 40 * 3012444 * 2
def baseEnd_3012444 : Nat := 1031221144501944688464019

theorem tailTrace_3012444 : CollatzResearch.WordTrace tailWord_3012444 prefixEnd_3012444 1031221144501944688464019 := by
  unfold tailWord_3012444
  simp only [CollatzResearch.WordTrace]
  refine ⟨54936429549218673660054193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73248572732291564880072257 54936429549218673660054193)
  ·
    refine ⟨41202322161914005245040645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54936429549218673660054193 41202322161914005245040645)
    ·
      refine ⟨7725435405358875983445121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41202322161914005245040645 7725435405358875983445121)
      ·
        refine ⟨5794076554019156987583841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7725435405358875983445121 5794076554019156987583841)
        ·
          refine ⟨4345557415514367740687881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794076554019156987583841 4345557415514367740687881)
          ·
            refine ⟨3259168061635775805515911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345557415514367740687881 3259168061635775805515911)
            ·
              refine ⟨4888752092453663708273867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259168061635775805515911 4888752092453663708273867)
              ·
                refine ⟨7333128138680495562410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888752092453663708273867 7333128138680495562410801)
                ·
                  refine ⟨5499846104010371671808101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333128138680495562410801 5499846104010371671808101)
                  ·
                    refine ⟨1031221144501944688464019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5499846104010371671808101 1031221144501944688464019)
                    ·
                      rfl

theorem cell22_3012444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3012444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012444 prefixEnd_3012444 := by exact prefixLift 3012444
  have htrace : WordTrace (prefixWord ++ tailWord_3012444) baseStart_3012444 baseEnd_3012444 := by
    simpa [prefixWord, tailWord_3012444, baseEnd_3012444] using wordTrace_append hprefix tailTrace_3012444
  have hstable : (prefixWord ++ tailWord_3012444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012444).length < 2 ^ (prefixWord ++ tailWord_3012444).sum := by decide
  have hdescent : baseEnd_3012444 < baseStart_3012444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012453 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 7]
def baseStart_3012453 : Nat := 118140960795 + 3012453 * 2 ^ 59
def prefixEnd_3012453 : Nat := 4983230072969 + 3 ^ 40 * 3012453 * 2
def baseEnd_3012453 : Nat := 343741408461957221662997

theorem tailTrace_3012453 : CollatzResearch.WordTrace tailWord_3012453 prefixEnd_3012453 343741408461957221662997 := by
  unfold tailWord_3012453
  simp only [CollatzResearch.WordTrace]
  refine ⟨109873187355404741857186013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73248791570269827904790675 109873187355404741857186013)
  ·
    refine ⟨41202445258276778196444755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109873187355404741857186013 41202445258276778196444755)
    ·
      refine ⟨61803667887415167294667133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41202445258276778196444755 61803667887415167294667133)
      ·
        refine ⟨23176375457780687735500175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61803667887415167294667133 23176375457780687735500175)
        ·
          refine ⟨34764563186671031603250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23176375457780687735500175 34764563186671031603250263)
          ·
            refine ⟨52146844780006547404875395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34764563186671031603250263 52146844780006547404875395)
            ·
              refine ⟨78220267170009821107313093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52146844780006547404875395 78220267170009821107313093)
              ·
                refine ⟨14666300094376841457621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78220267170009821107313093 14666300094376841457621205)
                ·
                  refine ⟨343741408461957221662997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14666300094376841457621205 343741408461957221662997)
                  ·
                    rfl

theorem cell22_3012453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_3012453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012453 prefixEnd_3012453 := by exact prefixLift 3012453
  have htrace : WordTrace (prefixWord ++ tailWord_3012453) baseStart_3012453 baseEnd_3012453 := by
    simpa [prefixWord, tailWord_3012453, baseEnd_3012453] using wordTrace_append hprefix tailTrace_3012453
  have hstable : (prefixWord ++ tailWord_3012453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012453).length < 2 ^ (prefixWord ++ tailWord_3012453).sum := by decide
  have hdescent : baseEnd_3012453 < baseStart_3012453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012528 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_3012528 : Nat := 118140960795 + 3012528 * 2 ^ 59
def prefixEnd_3012528 : Nat := 4983230072969 + 3 ^ 40 * 3012528 * 2
def baseEnd_3012528 : Nat := 1031249899418596469363761

theorem tailTrace_3012528 : CollatzResearch.WordTrace tailWord_3012528 prefixEnd_3012528 1031249899418596469363761 := by
  unfold tailWord_3012528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54937961415066514833083119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73250615220088686444110825 54937961415066514833083119)
  ·
    refine ⟨82406942122599772249624679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54937961415066514833083119 82406942122599772249624679)
    ·
      refine ⟨123610413183899658374437019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82406942122599772249624679 123610413183899658374437019)
      ·
        refine ⟨185415619775849487561655529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123610413183899658374437019 185415619775849487561655529)
        ·
          refine ⟨139061714831887115671241647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185415619775849487561655529 139061714831887115671241647)
          ·
            refine ⟨208592572247830673506862471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139061714831887115671241647 208592572247830673506862471)
            ·
              refine ⟨312888858371746010260293707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208592572247830673506862471 312888858371746010260293707)
              ·
                refine ⟨469333287557619015390440561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312888858371746010260293707 469333287557619015390440561)
                ·
                  refine ⟨351999965668214261542830421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469333287557619015390440561 351999965668214261542830421)
                  ·
                    refine ⟨1031249899418596469363761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 351999965668214261542830421 1031249899418596469363761)
                    ·
                      rfl

theorem cell22_3012528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_3012528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012528 prefixEnd_3012528 := by exact prefixLift 3012528
  have htrace : WordTrace (prefixWord ++ tailWord_3012528) baseStart_3012528 baseEnd_3012528 := by
    simpa [prefixWord, tailWord_3012528, baseEnd_3012528] using wordTrace_append hprefix tailTrace_3012528
  have hstable : (prefixWord ++ tailWord_3012528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012528).length < 2 ^ (prefixWord ++ tailWord_3012528).sum := by decide
  have hdescent : baseEnd_3012528 < baseStart_3012528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012583 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 4]
def baseStart_3012583 : Nat := 118140960795 + 3012583 * 2 ^ 59
def prefixEnd_3012583 : Nat := 4983230072969 + 3 ^ 40 * 3012583 * 2
def baseEnd_3012583 : Nat := 343756242347531553079531

theorem tailTrace_3012583 : CollatzResearch.WordTrace tailWord_3012583 prefixEnd_3012583 343756242347531553079531 := by
  unfold tailWord_3012583
  simp only [CollatzResearch.WordTrace]
  refine ⟨109877928844933774059418403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73251952563289182706278935 109877928844933774059418403)
  ·
    refine ⟨164816893267400661089127605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109877928844933774059418403 164816893267400661089127605)
    ·
      refine ⟨15451583743818811977105713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164816893267400661089127605 15451583743818811977105713)
      ·
        refine ⟨11588687807864108982829285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451583743818811977105713 11588687807864108982829285)
        ·
          refine ⟨2172878963974520434280491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11588687807864108982829285 2172878963974520434280491)
          ·
            refine ⟨3259318445961780651420737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172878963974520434280491 3259318445961780651420737)
            ·
              refine ⟨2444488834471335488565553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259318445961780651420737 2444488834471335488565553)
              ·
                refine ⟨1833366625853501616424165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444488834471335488565553 1833366625853501616424165)
                ·
                  refine ⟨343756242347531553079531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833366625853501616424165 343756242347531553079531)
                  ·
                    rfl

theorem cell22_3012583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 4].length) (baseStart_3012583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012583 prefixEnd_3012583 := by exact prefixLift 3012583
  have htrace : WordTrace (prefixWord ++ tailWord_3012583) baseStart_3012583 baseEnd_3012583 := by
    simpa [prefixWord, tailWord_3012583, baseEnd_3012583] using wordTrace_append hprefix tailTrace_3012583
  have hstable : (prefixWord ++ tailWord_3012583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012583).length < 2 ^ (prefixWord ++ tailWord_3012583).sum := by decide
  have hdescent : baseEnd_3012583 < baseStart_3012583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012620 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_3012620 : Nat := 118140960795 + 3012620 * 2 ^ 59
def prefixEnd_3012620 : Nat := 4983230072969 + 3 ^ 40 * 3012620 * 2
def baseEnd_3012620 : Nat := 1031281392898738896063479

theorem tailTrace_3012620 : CollatzResearch.WordTrace tailWord_3012620 prefixEnd_3012620 1031281392898738896063479 := by
  unfold tailWord_3012620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54939639172899864689257657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73252852230533152919010209 54939639172899864689257657)
  ·
    refine ⟨41204729379674898516943243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54939639172899864689257657 41204729379674898516943243)
    ·
      refine ⟨61807094069512347775414865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41204729379674898516943243 61807094069512347775414865)
      ·
        refine ⟨46355320552134260831561149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61807094069512347775414865 46355320552134260831561149)
        ·
          refine ⟨17383245207050347811835431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46355320552134260831561149 17383245207050347811835431)
          ·
            refine ⟨26074867810575521717753147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17383245207050347811835431 26074867810575521717753147)
            ·
              refine ⟨39112301715863282576629721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26074867810575521717753147 39112301715863282576629721)
              ·
                refine ⟨29334226286897461932472291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39112301715863282576629721 29334226286897461932472291)
                ·
                  refine ⟨44001339430346192898708437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29334226286897461932472291 44001339430346192898708437)
                  ·
                    refine ⟨1031281392898738896063479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44001339430346192898708437 1031281392898738896063479)
                    ·
                      rfl

theorem cell22_3012620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_3012620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012620 prefixEnd_3012620 := by exact prefixLift 3012620
  have htrace : WordTrace (prefixWord ++ tailWord_3012620) baseStart_3012620 baseEnd_3012620 := by
    simpa [prefixWord, tailWord_3012620, baseEnd_3012620] using wordTrace_append hprefix tailTrace_3012620
  have hstable : (prefixWord ++ tailWord_3012620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012620).length < 2 ^ (prefixWord ++ tailWord_3012620).sum := by decide
  have hdescent : baseEnd_3012620 < baseStart_3012620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012635 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_3012635 : Nat := 118140960795 + 3012635 * 2 ^ 59
def prefixEnd_3012635 : Nat := 4983230072969 + 3 ^ 40 * 3012635 * 2
def baseEnd_3012635 : Nat := 1031286527705283856938433

theorem tailTrace_3012635 : CollatzResearch.WordTrace tailWord_3012635 prefixEnd_3012635 1031286527705283856938433 := by
  unfold tailWord_3012635
  simp only [CollatzResearch.WordTrace]
  refine ⟨109879825440745386940311359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73253216960496924626874239 109879825440745386940311359)
  ·
    refine ⟨164819738161118080410467039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109879825440745386940311359 164819738161118080410467039)
    ·
      refine ⟨247229607241677120615700559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164819738161118080410467039 247229607241677120615700559)
      ·
        refine ⟨370844410862515680923550839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247229607241677120615700559 370844410862515680923550839)
        ·
          refine ⟨556266616293773521385326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370844410862515680923550839 556266616293773521385326259)
          ·
            refine ⟨834399924440660282077989389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556266616293773521385326259 834399924440660282077989389)
            ·
              refine ⟨312899971665247605779246021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 834399924440660282077989389 312899971665247605779246021)
              ·
                refine ⟨58668744687233926083608629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312899971665247605779246021 58668744687233926083608629)
                ·
                  refine ⟨5500194814428180570338309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58668744687233926083608629 5500194814428180570338309)
                  ·
                    refine ⟨1031286527705283856938433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500194814428180570338309 1031286527705283856938433)
                    ·
                      rfl

theorem cell22_3012635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_3012635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012635 prefixEnd_3012635 := by exact prefixLift 3012635
  have htrace : WordTrace (prefixWord ++ tailWord_3012635) baseStart_3012635 baseEnd_3012635 := by
    simpa [prefixWord, tailWord_3012635, baseEnd_3012635] using wordTrace_append hprefix tailTrace_3012635
  have hstable : (prefixWord ++ tailWord_3012635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012635).length < 2 ^ (prefixWord ++ tailWord_3012635).sum := by decide
  have hdescent : baseEnd_3012635 < baseStart_3012635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012637 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3012637 : Nat := 118140960795 + 3012637 * 2 ^ 59
def prefixEnd_3012637 : Nat := 4983230072969 + 3 ^ 40 * 3012637 * 2
def baseEnd_3012637 : Nat := 1031287212346156518388427

theorem tailTrace_3012637 : CollatzResearch.WordTrace tailWord_3012637 prefixEnd_3012637 1031287212346156518388427 := by
  unfold tailWord_3012637
  simp only [CollatzResearch.WordTrace]
  refine ⟨109879898386738141281884165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73253265591158760854589443 109879898386738141281884165)
  ·
    refine ⟨20602480947513401490353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109879898386738141281884165 20602480947513401490353281)
    ·
      refine ⟨15451860710635051117764961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20602480947513401490353281 15451860710635051117764961)
      ·
        refine ⟨11588895532976288338323721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451860710635051117764961 11588895532976288338323721)
        ·
          refine ⟨8691671649732216253742791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588895532976288338323721 8691671649732216253742791)
          ·
            refine ⟨13037507474598324380614187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691671649732216253742791 13037507474598324380614187)
            ·
              refine ⟨19556261211897486570921281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13037507474598324380614187 19556261211897486570921281)
              ·
                refine ⟨14667195908923114928190961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19556261211897486570921281 14667195908923114928190961)
                ·
                  refine ⟨11000396931692336196143221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14667195908923114928190961 11000396931692336196143221)
                  ·
                    refine ⟨1031287212346156518388427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11000396931692336196143221 1031287212346156518388427)
                    ·
                      rfl

theorem cell22_3012637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3012637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012637 prefixEnd_3012637 := by exact prefixLift 3012637
  have htrace : WordTrace (prefixWord ++ tailWord_3012637) baseStart_3012637 baseEnd_3012637 := by
    simpa [prefixWord, tailWord_3012637, baseEnd_3012637] using wordTrace_append hprefix tailTrace_3012637
  have hstable : (prefixWord ++ tailWord_3012637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012637).length < 2 ^ (prefixWord ++ tailWord_3012637).sum := by decide
  have hdescent : baseEnd_3012637 < baseStart_3012637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012669 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3012669 : Nat := 118140960795 + 3012669 * 2 ^ 59
def prefixEnd_3012669 : Nat := 4983230072969 + 3 ^ 40 * 3012669 * 2
def baseEnd_3012669 : Nat := 1031298166600119101588329

theorem tailTrace_3012669 : CollatzResearch.WordTrace tailWord_3012669 prefixEnd_3012669 1031298166600119101588329 := by
  unfold tailWord_3012669
  simp only [CollatzResearch.WordTrace]
  refine ⟨109881065522622210747049061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73254043681748140498032707 109881065522622210747049061)
  ·
    refine ⟨20602699785491664515071699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109881065522622210747049061 20602699785491664515071699)
    ·
      refine ⟨30904049678237496772607549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20602699785491664515071699 30904049678237496772607549)
      ·
        refine ⟨11589018629339061289727831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30904049678237496772607549 11589018629339061289727831)
        ·
          refine ⟨17383527944008591934591747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11589018629339061289727831 17383527944008591934591747)
          ·
            refine ⟨26075291916012887901887621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17383527944008591934591747 26075291916012887901887621)
            ·
              refine ⟨4889117234252416481603929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26075291916012887901887621 4889117234252416481603929)
              ·
                refine ⟨3666837925689312361202947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889117234252416481603929 3666837925689312361202947)
                ·
                  refine ⟨5500256888533968541804421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666837925689312361202947 5500256888533968541804421)
                  ·
                    refine ⟨1031298166600119101588329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500256888533968541804421 1031298166600119101588329)
                    ·
                      rfl

theorem cell22_3012669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3012669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012669 prefixEnd_3012669 := by exact prefixLift 3012669
  have htrace : WordTrace (prefixWord ++ tailWord_3012669) baseStart_3012669 baseEnd_3012669 := by
    simpa [prefixWord, tailWord_3012669, baseEnd_3012669] using wordTrace_append hprefix tailTrace_3012669
  have hstable : (prefixWord ++ tailWord_3012669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012669).length < 2 ^ (prefixWord ++ tailWord_3012669).sum := by decide
  have hdescent : baseEnd_3012669 < baseStart_3012669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012684 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_3012684 : Nat := 118140960795 + 3012684 * 2 ^ 59
def prefixEnd_3012684 : Nat := 4983230072969 + 3 ^ 40 * 3012684 * 2
def baseEnd_3012684 : Nat := 343767767135554687487761

theorem tailTrace_3012684 : CollatzResearch.WordTrace tailWord_3012684 prefixEnd_3012684 343767767135554687487761 := by
  unfold tailWord_3012684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940806308783934154422553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73254408411711912205896737 54940806308783934154422553)
  ·
    refine ⟨41205604731587950615816915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54940806308783934154422553 41205604731587950615816915)
    ·
      refine ⟨61808407097381925923725373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41205604731587950615816915 61808407097381925923725373)
      ·
        refine ⟨23178152661518222221397015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61808407097381925923725373 23178152661518222221397015)
        ·
          refine ⟨34767228992277333332095523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23178152661518222221397015 34767228992277333332095523)
          ·
            refine ⟨52150843488415999998143285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34767228992277333332095523 52150843488415999998143285)
            ·
              refine ⟨4889141577038999999825933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52150843488415999998143285 4889141577038999999825933)
              ·
                refine ⟨1833428091389624999934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889141577038999999825933 1833428091389624999934725)
                ·
                  refine ⟨343767767135554687487761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833428091389624999934725 343767767135554687487761)
                  ·
                    rfl

theorem cell22_3012684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_3012684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012684 prefixEnd_3012684 := by exact prefixLift 3012684
  have htrace : WordTrace (prefixWord ++ tailWord_3012684) baseStart_3012684 baseEnd_3012684 := by
    simpa [prefixWord, tailWord_3012684, baseEnd_3012684] using wordTrace_append hprefix tailTrace_3012684
  have hstable : (prefixWord ++ tailWord_3012684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012684).length < 2 ^ (prefixWord ++ tailWord_3012684).sum := by decide
  have hdescent : baseEnd_3012684 < baseStart_3012684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012695 : List Nat := [1, 1, 3, 2, 2, 1, 12]
def baseStart_3012695 : Nat := 118140960795 + 3012695 * 2 ^ 59
def prefixEnd_3012695 : Nat := 4983230072969 + 3 ^ 40 * 3012695 * 2
def baseEnd_3012695 : Nat := 38196558034498655571787

theorem tailTrace_3012695 : CollatzResearch.WordTrace tailWord_3012695 prefixEnd_3012695 38196558034498655571787 := by
  unfold tailWord_3012695
  simp only [CollatzResearch.WordTrace]
  refine ⟨109882013820528017187495539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73254675880352011458330359 109882013820528017187495539)
  ·
    refine ⟨164823020730792025781243309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109882013820528017187495539 164823020730792025781243309)
    ·
      refine ⟨61808632774047009667966241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164823020730792025781243309 61808632774047009667966241)
      ·
        refine ⟨46356474580535257250974681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61808632774047009667966241 46356474580535257250974681)
        ·
          refine ⟨34767355935401442938231011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46356474580535257250974681 34767355935401442938231011)
          ·
            refine ⟨52151033903102164407346517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34767355935401442938231011 52151033903102164407346517)
            ·
              refine ⟨38196558034498655571787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52151033903102164407346517 38196558034498655571787)
              ·
                rfl

theorem cell22_3012695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 12].length) (baseStart_3012695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012695 prefixEnd_3012695 := by exact prefixLift 3012695
  have htrace : WordTrace (prefixWord ++ tailWord_3012695) baseStart_3012695 baseEnd_3012695 := by
    simpa [prefixWord, tailWord_3012695, baseEnd_3012695] using wordTrace_append hprefix tailTrace_3012695
  have hstable : (prefixWord ++ tailWord_3012695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012695).length < 2 ^ (prefixWord ++ tailWord_3012695).sum := by decide
  have hdescent : baseEnd_3012695 < baseStart_3012695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012697 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_3012697 : Nat := 118140960795 + 3012697 * 2 ^ 59
def prefixEnd_3012697 : Nat := 4983230072969 + 3 ^ 40 * 3012697 * 2
def baseEnd_3012697 : Nat := 1031307751572336361888243

theorem tailTrace_3012697 : CollatzResearch.WordTrace tailWord_3012697 prefixEnd_3012697 1031307751572336361888243 := by
  unfold tailWord_3012697
  simp only [CollatzResearch.WordTrace]
  refine ⟨109882086766520771529068345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73254724511013847686045563 109882086766520771529068345)
  ·
    refine ⟨82411565074890578646801259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109882086766520771529068345 82411565074890578646801259)
    ·
      refine ⟨123617347612335867970201889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82411565074890578646801259 123617347612335867970201889)
      ·
        refine ⟨92713010709251900977651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123617347612335867970201889 92713010709251900977651417)
        ·
          refine ⟨69534758031938925733238563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92713010709251900977651417 69534758031938925733238563)
          ·
            refine ⟨104302137047908388599857845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69534758031938925733238563 104302137047908388599857845)
            ·
              refine ⟨9778325348241411431236673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104302137047908388599857845 9778325348241411431236673)
              ·
                refine ⟨7333744011181058573427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778325348241411431236673 7333744011181058573427505)
                ·
                  refine ⟨5500308008385793930070629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7333744011181058573427505 5500308008385793930070629)
                  ·
                    refine ⟨1031307751572336361888243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500308008385793930070629 1031307751572336361888243)
                    ·
                      rfl

theorem cell22_3012697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_3012697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012697 prefixEnd_3012697 := by exact prefixLift 3012697
  have htrace : WordTrace (prefixWord ++ tailWord_3012697) baseStart_3012697 baseEnd_3012697 := by
    simpa [prefixWord, tailWord_3012697, baseEnd_3012697] using wordTrace_append hprefix tailTrace_3012697
  have hstable : (prefixWord ++ tailWord_3012697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012697).length < 2 ^ (prefixWord ++ tailWord_3012697).sum := by decide
  have hdescent : baseEnd_3012697 < baseStart_3012697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012701 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 6]
def baseStart_3012701 : Nat := 118140960795 + 3012701 * 2 ^ 59
def prefixEnd_3012701 : Nat := 4983230072969 + 3 ^ 40 * 3012701 * 2
def baseEnd_3012701 : Nat := 343769706951360561596077

theorem tailTrace_3012701 : CollatzResearch.WordTrace tailWord_3012701 prefixEnd_3012701 343769706951360561596077 := by
  unfold tailWord_3012701
  simp only [CollatzResearch.WordTrace]
  refine ⟨109882232658506280212213957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73254821772337520141475971 109882232658506280212213957)
  ·
    refine ⟨20602918623469927539790117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109882232658506280212213957 20602918623469927539790117)
    ·
      refine ⟨3863047241900611413710647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20602918623469927539790117 3863047241900611413710647)
      ·
        refine ⟨5794570862850917120565971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863047241900611413710647 5794570862850917120565971)
        ·
          refine ⟨8691856294276375680848957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794570862850917120565971 8691856294276375680848957)
          ·
            refine ⟨3259446110353640880318359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8691856294276375680848957 3259446110353640880318359)
            ·
              refine ⟨4889169165530461320477539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259446110353640880318359 4889169165530461320477539)
              ·
                refine ⟨7333753748295691980716309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889169165530461320477539 7333753748295691980716309)
                ·
                  refine ⟨343769706951360561596077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333753748295691980716309 343769706951360561596077)
                  ·
                    rfl

theorem cell22_3012701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_3012701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012701 prefixEnd_3012701 := by exact prefixLift 3012701
  have htrace : WordTrace (prefixWord ++ tailWord_3012701) baseStart_3012701 baseEnd_3012701 := by
    simpa [prefixWord, tailWord_3012701, baseEnd_3012701] using wordTrace_append hprefix tailTrace_3012701
  have hstable : (prefixWord ++ tailWord_3012701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012701).length < 2 ^ (prefixWord ++ tailWord_3012701).sum := by decide
  have hdescent : baseEnd_3012701 < baseStart_3012701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012716 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_3012716 : Nat := 118140960795 + 3012716 * 2 ^ 59
def prefixEnd_3012716 : Nat := 4983230072969 + 3 ^ 40 * 3012716 * 2
def baseEnd_3012716 : Nat := 1031314255660626645663185

theorem tailTrace_3012716 : CollatzResearch.WordTrace tailWord_3012716 prefixEnd_3012716 1031314255660626645663185 := by
  unfold tailWord_3012716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54941389876725968887005001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73255186502301291849340001 54941389876725968887005001)
  ·
    refine ⟨41206042407544476665253751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54941389876725968887005001 41206042407544476665253751)
    ·
      refine ⟨61809063611316714997880627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41206042407544476665253751 61809063611316714997880627)
      ·
        refine ⟨92713595416975072496820941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61809063611316714997880627 92713595416975072496820941)
        ·
          refine ⟨34767598281365652186307853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92713595416975072496820941 34767598281365652186307853)
          ·
            refine ⟨13037849355512119569865445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34767598281365652186307853 13037849355512119569865445)
            ·
              refine ⟨2444596754158522419349771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13037849355512119569865445 2444596754158522419349771)
              ·
                refine ⟨3666895131237783629024657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444596754158522419349771 3666895131237783629024657)
                ·
                  refine ⟨2750171348428337721768493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666895131237783629024657 2750171348428337721768493)
                  ·
                    refine ⟨1031314255660626645663185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750171348428337721768493 1031314255660626645663185)
                    ·
                      rfl

theorem cell22_3012716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_3012716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012716 prefixEnd_3012716 := by exact prefixLift 3012716
  have htrace : WordTrace (prefixWord ++ tailWord_3012716) baseStart_3012716 baseEnd_3012716 := by
    simpa [prefixWord, tailWord_3012716, baseEnd_3012716] using wordTrace_append hprefix tailTrace_3012716
  have hstable : (prefixWord ++ tailWord_3012716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012716).length < 2 ^ (prefixWord ++ tailWord_3012716).sum := by decide
  have hdescent : baseEnd_3012716 < baseStart_3012716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012778 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3012778 : Nat := 118140960795 + 3012778 * 2 ^ 59
def prefixEnd_3012778 : Nat := 4983230072969 + 3 ^ 40 * 3012778 * 2
def baseEnd_3012778 : Nat := 1031335479527679150612995

theorem tailTrace_3012778 : CollatzResearch.WordTrace tailWord_3012778 prefixEnd_3012778 1031335479527679150612995 := by
  unfold tailWord_3012778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471260269806830590691747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73256694052818214908511325 27471260269806830590691747)
  ·
    refine ⟨41206890404710245886037621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471260269806830590691747 41206890404710245886037621)
    ·
      refine ⟨3863145975441585551816027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41206890404710245886037621 3863145975441585551816027)
      ·
        refine ⟨5794718963162378327724041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863145975441585551816027 5794718963162378327724041)
        ·
          refine ⟨4346039222371783745793031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794718963162378327724041 4346039222371783745793031)
          ·
            refine ⟨6519058833557675618689547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346039222371783745793031 6519058833557675618689547)
            ·
              refine ⟨9778588250336513428034321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6519058833557675618689547 9778588250336513428034321)
              ·
                refine ⟨7333941187752385071025741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778588250336513428034321 7333941187752385071025741)
                ·
                  refine ⟨2750227945407144401634653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7333941187752385071025741 2750227945407144401634653)
                  ·
                    refine ⟨1031335479527679150612995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750227945407144401634653 1031335479527679150612995)
                    ·
                      rfl

theorem cell22_3012778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3012778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012778 prefixEnd_3012778 := by exact prefixLift 3012778
  have htrace : WordTrace (prefixWord ++ tailWord_3012778) baseStart_3012778 baseEnd_3012778 := by
    simpa [prefixWord, tailWord_3012778, baseEnd_3012778] using wordTrace_append hprefix tailTrace_3012778
  have hstable : (prefixWord ++ tailWord_3012778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012778).length < 2 ^ (prefixWord ++ tailWord_3012778).sum := by decide
  have hdescent : baseEnd_3012778 < baseStart_3012778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012817 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3012817 : Nat := 118140960795 + 3012817 * 2 ^ 59
def prefixEnd_3012817 : Nat := 4983230072969 + 3 ^ 40 * 3012817 * 2
def baseEnd_3012817 : Nat := 1031348830024696048887875

theorem tailTrace_3012817 : CollatzResearch.WordTrace tailWord_3012817 prefixEnd_3012817 1031348830024696048887875 := by
  unfold tailWord_3012817
  simp only [CollatzResearch.WordTrace]
  refine ⟨109886463526086032023436705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73257642350724021348957803 109886463526086032023436705)
  ·
    refine ⟨82414847644564524017577529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109886463526086032023436705 82414847644564524017577529)
    ·
      refine ⟨61811135733423393013183147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82414847644564524017577529 61811135733423393013183147)
      ·
        refine ⟨92716703600135089519774721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61811135733423393013183147 92716703600135089519774721)
        ·
          refine ⟨69537527700101317139831041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92716703600135089519774721 69537527700101317139831041)
          ·
            refine ⟨52153145775075987854873281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69537527700101317139831041 52153145775075987854873281)
            ·
              refine ⟨39114859331306990891154961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52153145775075987854873281 39114859331306990891154961)
              ·
                refine ⟨29336144498480243168366221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39114859331306990891154961 29336144498480243168366221)
                ·
                  refine ⟨11001054186930091188137333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29336144498480243168366221 11001054186930091188137333)
                  ·
                    refine ⟨1031348830024696048887875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11001054186930091188137333 1031348830024696048887875)
                    ·
                      rfl

theorem cell22_3012817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3012817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012817 prefixEnd_3012817 := by exact prefixLift 3012817
  have htrace : WordTrace (prefixWord ++ tailWord_3012817) baseStart_3012817 baseEnd_3012817 := by
    simpa [prefixWord, tailWord_3012817, baseEnd_3012817] using wordTrace_append hprefix tailTrace_3012817
  have hstable : (prefixWord ++ tailWord_3012817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012817).length < 2 ^ (prefixWord ++ tailWord_3012817).sum := by decide
  have hdescent : baseEnd_3012817 < baseStart_3012817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012832 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_3012832 : Nat := 118140960795 + 3012832 * 2 ^ 59
def prefixEnd_3012832 : Nat := 4983230072969 + 3 ^ 40 * 3012832 * 2
def baseEnd_3012832 : Nat := 1031353964831241009762829

theorem tailTrace_3012832 : CollatzResearch.WordTrace tailWord_3012832 prefixEnd_3012832 1031353964831241009762829 := by
  unfold tailWord_3012832
  simp only [CollatzResearch.WordTrace]
  refine ⟨54943505310515844792616375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73258007080687793056821833 54943505310515844792616375)
  ·
    refine ⟨82415257965773767188924563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54943505310515844792616375 82415257965773767188924563)
    ·
      refine ⟨123622886948660650783386845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82415257965773767188924563 123622886948660650783386845)
      ·
        refine ⟨46358582605747744043770067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123622886948660650783386845 46358582605747744043770067)
        ·
          refine ⟨69537873908621616065655101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46358582605747744043770067 69537873908621616065655101)
          ·
            refine ⟨26076702715733106024620663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69537873908621616065655101 26076702715733106024620663)
            ·
              refine ⟨39115054073599659036930995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26076702715733106024620663 39115054073599659036930995)
              ·
                refine ⟨58672581110399488555396493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39115054073599659036930995 58672581110399488555396493)
                ·
                  refine ⟨22002217916399808208273685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58672581110399488555396493 22002217916399808208273685)
                  ·
                    refine ⟨1031353964831241009762829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22002217916399808208273685 1031353964831241009762829)
                    ·
                      rfl

theorem cell22_3012832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_3012832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012832 prefixEnd_3012832 := by exact prefixLift 3012832
  have htrace : WordTrace (prefixWord ++ tailWord_3012832) baseStart_3012832 baseEnd_3012832 := by
    simpa [prefixWord, tailWord_3012832, baseEnd_3012832] using wordTrace_append hprefix tailTrace_3012832
  have hstable : (prefixWord ++ tailWord_3012832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012832).length < 2 ^ (prefixWord ++ tailWord_3012832).sum := by decide
  have hdescent : baseEnd_3012832 < baseStart_3012832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012866 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3012866 : Nat := 118140960795 + 3012866 * 2 ^ 59
def prefixEnd_3012866 : Nat := 4983230072969 + 3 ^ 40 * 3012866 * 2
def baseEnd_3012866 : Nat := 1031365603726076254412725

theorem tailTrace_3012866 : CollatzResearch.WordTrace tailWord_3012866 prefixEnd_3012866 1031365603726076254412725 := by
  unfold tailWord_3012866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27472062675727128347992613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73258833801939008927980301 27472062675727128347992613)
  ·
    refine ⟨5151011751698836565248615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27472062675727128347992613 5151011751698836565248615)
    ·
      refine ⟨7726517627548254847872923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151011751698836565248615 7726517627548254847872923)
      ·
        refine ⟨11589776441322382271809385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7726517627548254847872923 11589776441322382271809385)
        ·
          refine ⟨8692332330991786703857039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11589776441322382271809385 8692332330991786703857039)
          ·
            refine ⟨13038498496487680055785559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692332330991786703857039 13038498496487680055785559)
            ·
              refine ⟨19557747744731520083678339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038498496487680055785559 19557747744731520083678339)
              ·
                refine ⟨29336621617097280125517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19557747744731520083678339 29336621617097280125517509)
                ·
                  refine ⟨5500616553205740023534533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29336621617097280125517509 5500616553205740023534533)
                  ·
                    refine ⟨1031365603726076254412725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500616553205740023534533 1031365603726076254412725)
                    ·
                      rfl

theorem cell22_3012866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3012866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012866 prefixEnd_3012866 := by exact prefixLift 3012866
  have htrace : WordTrace (prefixWord ++ tailWord_3012866) baseStart_3012866 baseEnd_3012866 := by
    simpa [prefixWord, tailWord_3012866, baseEnd_3012866] using wordTrace_append hprefix tailTrace_3012866
  have hstable : (prefixWord ++ tailWord_3012866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012866).length < 2 ^ (prefixWord ++ tailWord_3012866).sum := by decide
  have hdescent : baseEnd_3012866 < baseStart_3012866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012924 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3012924 : Nat := 118140960795 + 3012924 * 2 ^ 59
def prefixEnd_3012924 : Nat := 4983230072969 + 3 ^ 40 * 3012924 * 2
def baseEnd_3012924 : Nat := 1031385458311383436462547

theorem tailTrace_3012924 : CollatzResearch.WordTrace tailWord_3012924 prefixEnd_3012924 1031385458311383436462547 := by
  unfold tailWord_3012924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945183068349194648790913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73260244091132259531721217 54945183068349194648790913)
  ·
    refine ⟨41208887301261895986593185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54945183068349194648790913 41208887301261895986593185)
    ·
      refine ⟨30906665475946421989944889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41208887301261895986593185 30906665475946421989944889)
      ·
        refine ⟨23179999106959816492458667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30906665475946421989944889 23179999106959816492458667)
        ·
          refine ⟨34769998660439724738688001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23179999106959816492458667 34769998660439724738688001)
          ·
            refine ⟨26077498995329793554016001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34769998660439724738688001 26077498995329793554016001)
            ·
              refine ⟨19558124246497345165512001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26077498995329793554016001 19558124246497345165512001)
              ·
                refine ⟨14668593184873008874134001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19558124246497345165512001 14668593184873008874134001)
                ·
                  refine ⟨11001444888654756655600501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14668593184873008874134001 11001444888654756655600501)
                  ·
                    refine ⟨1031385458311383436462547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11001444888654756655600501 1031385458311383436462547)
                    ·
                      rfl

theorem cell22_3012924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3012924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012924 prefixEnd_3012924 := by exact prefixLift 3012924
  have htrace : WordTrace (prefixWord ++ tailWord_3012924) baseStart_3012924 baseEnd_3012924 := by
    simpa [prefixWord, tailWord_3012924, baseEnd_3012924] using wordTrace_append hprefix tailTrace_3012924
  have hstable : (prefixWord ++ tailWord_3012924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012924).length < 2 ^ (prefixWord ++ tailWord_3012924).sum := by decide
  have hdescent : baseEnd_3012924 < baseStart_3012924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012926 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3012926 : Nat := 118140960795 + 3012926 * 2 ^ 59
def prefixEnd_3012926 : Nat := 4983230072969 + 3 ^ 40 * 3012926 * 2
def baseEnd_3012926 : Nat := 343795380984085365970847

theorem tailTrace_3012926 : CollatzResearch.WordTrace tailWord_3012926 prefixEnd_3012926 343795380984085365970847 := by
  unfold tailWord_3012926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736304885336392954894329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73260292721794095759436421 13736304885336392954894329)
  ·
    refine ⟨10302228664002294716170747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13736304885336392954894329 10302228664002294716170747)
    ·
      refine ⟨15453342996003442074256121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10302228664002294716170747 15453342996003442074256121)
      ·
        refine ⟨11590007247002581555692091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15453342996003442074256121 11590007247002581555692091)
        ·
          refine ⟨17385010870503872333538137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590007247002581555692091 17385010870503872333538137)
          ·
            refine ⟨13038758152877904250153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17385010870503872333538137 13038758152877904250153603)
            ·
              refine ⟨19558137229316856375230405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038758152877904250153603 19558137229316856375230405)
              ·
                refine ⟨3667150730496910570355701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19558137229316856375230405 3667150730496910570355701)
                ·
                  refine ⟨343795380984085365970847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667150730496910570355701 343795380984085365970847)
                  ·
                    rfl

theorem cell22_3012926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3012926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012926 prefixEnd_3012926 := by exact prefixLift 3012926
  have htrace : WordTrace (prefixWord ++ tailWord_3012926) baseStart_3012926 baseEnd_3012926 := by
    simpa [prefixWord, tailWord_3012926, baseEnd_3012926] using wordTrace_append hprefix tailTrace_3012926
  have hstable : (prefixWord ++ tailWord_3012926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012926).length < 2 ^ (prefixWord ++ tailWord_3012926).sum := by decide
  have hdescent : baseEnd_3012926 < baseStart_3012926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012969 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_3012969 : Nat := 118140960795 + 3012969 * 2 ^ 59
def prefixEnd_3012969 : Nat := 4983230072969 + 3 ^ 40 * 3012969 * 2
def baseEnd_3012969 : Nat := 1031400862731018319087409

theorem tailTrace_3012969 : CollatzResearch.WordTrace tailWord_3012969 prefixEnd_3012969 1031400862731018319087409 := by
  unfold tailWord_3012969
  simp only [CollatzResearch.WordTrace]
  refine ⟨109892007421535361982969961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73261338281023574655313307 109892007421535361982969961)
  ·
    refine ⟨82419005566151521487227471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109892007421535361982969961 82419005566151521487227471)
    ·
      refine ⟨123628508349227282230841207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82419005566151521487227471 123628508349227282230841207)
      ·
        refine ⟨185442762523840923346261811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123628508349227282230841207 185442762523840923346261811)
        ·
          refine ⟨278164143785761385019392717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185442762523840923346261811 278164143785761385019392717)
          ·
            refine ⟨104311553919660519382272269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278164143785761385019392717 104311553919660519382272269)
            ·
              refine ⟨39116832719872694768352101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104311553919660519382272269 39116832719872694768352101)
              ·
                refine ⟨7334406134976130269066019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39116832719872694768352101 7334406134976130269066019)
                ·
                  refine ⟨11001609202464195403599029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334406134976130269066019 11001609202464195403599029)
                  ·
                    refine ⟨1031400862731018319087409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11001609202464195403599029 1031400862731018319087409)
                    ·
                      rfl

theorem cell22_3012969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_3012969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012969 prefixEnd_3012969 := by exact prefixLift 3012969
  have htrace : WordTrace (prefixWord ++ tailWord_3012969) baseStart_3012969 baseEnd_3012969 := by
    simpa [prefixWord, tailWord_3012969, baseEnd_3012969] using wordTrace_append hprefix tailTrace_3012969
  have hstable : (prefixWord ++ tailWord_3012969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012969).length < 2 ^ (prefixWord ++ tailWord_3012969).sum := by decide
  have hdescent : baseEnd_3012969 < baseStart_3012969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3012999 : List Nat := [1, 1, 4, 2, 2, 1, 2, 9]
def baseStart_3012999 : Nat := 118140960795 + 3012999 * 2 ^ 59
def prefixEnd_3012999 : Nat := 4983230072969 + 3 ^ 40 * 3012999 * 2
def baseEnd_3012999 : Nat := 114601236927123137870813

theorem tailTrace_3012999 : CollatzResearch.WordTrace tailWord_3012999 prefixEnd_3012999 114601236927123137870813 := by
  unfold tailWord_3012999
  simp only [CollatzResearch.WordTrace]
  refine ⟨109893101611426677106562051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73262067740951118071041367 109893101611426677106562051)
  ·
    refine ⟨164839652417140015659843077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109893101611426677106562051 164839652417140015659843077)
    ·
      refine ⟨30907434828213752936220577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164839652417140015659843077 30907434828213752936220577)
      ·
        refine ⟨23180576121160314702165433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30907434828213752936220577 23180576121160314702165433)
        ·
          refine ⟨17385432090870236026624075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23180576121160314702165433 17385432090870236026624075)
          ·
            refine ⟨26078148136305354039936113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17385432090870236026624075 26078148136305354039936113)
            ·
              refine ⟨19558611102229015529952085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26078148136305354039936113 19558611102229015529952085)
              ·
                refine ⟨114601236927123137870813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19558611102229015529952085 114601236927123137870813)
                ·
                  rfl

theorem cell22_3012999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 9].length) (baseStart_3012999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3012999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3012999 prefixEnd_3012999 := by exact prefixLift 3012999
  have htrace : WordTrace (prefixWord ++ tailWord_3012999) baseStart_3012999 baseEnd_3012999 := by
    simpa [prefixWord, tailWord_3012999, baseEnd_3012999] using wordTrace_append hprefix tailTrace_3012999
  have hstable : (prefixWord ++ tailWord_3012999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3012999).length < 2 ^ (prefixWord ++ tailWord_3012999).sum := by decide
  have hdescent : baseEnd_3012999 < baseStart_3012999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3012999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013016 : List Nat := [2, 1, 2, 5, 1, 2, 1, 8]
def baseStart_3013016 : Nat := 118140960795 + 3013016 * 2 ^ 59
def prefixEnd_3013016 : Nat := 4983230072969 + 3 ^ 40 * 3013016 * 2
def baseEnd_3013016 : Nat := 114601883532391762573585

theorem tailTrace_3013016 : CollatzResearch.WordTrace tailWord_3013016 prefixEnd_3013016 114601883532391762573585 := by
  unfold tailWord_3013016
  simp only [CollatzResearch.WordTrace]
  refine ⟨54946860826182544504965451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73262481101576726006620601 54946860826182544504965451)
  ·
    refine ⟨82420291239273816757448177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54946860826182544504965451 82420291239273816757448177)
    ·
      refine ⟨61815218429455362568086133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82420291239273816757448177 61815218429455362568086133)
      ·
        refine ⟨5795176727761440240758075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61815218429455362568086133 5795176727761440240758075)
        ·
          refine ⟨8692765091642160361137113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795176727761440240758075 8692765091642160361137113)
          ·
            refine ⟨6519573818731620270852835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8692765091642160361137113 6519573818731620270852835)
            ·
              refine ⟨9779360728097430406279253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6519573818731620270852835 9779360728097430406279253)
              ·
                refine ⟨114601883532391762573585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9779360728097430406279253 114601883532391762573585)
                ·
                  rfl

theorem cell22_3013016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_3013016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013016 prefixEnd_3013016 := by exact prefixLift 3013016
  have htrace : WordTrace (prefixWord ++ tailWord_3013016) baseStart_3013016 baseEnd_3013016 := by
    simpa [prefixWord, tailWord_3013016, baseEnd_3013016] using wordTrace_append hprefix tailTrace_3013016
  have hstable : (prefixWord ++ tailWord_3013016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013016).length < 2 ^ (prefixWord ++ tailWord_3013016).sum := by decide
  have hdescent : baseEnd_3013016 < baseStart_3013016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013022 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3013022 : Nat := 118140960795 + 3013022 * 2 ^ 59
def prefixEnd_3013022 : Nat := 4983230072969 + 3 ^ 40 * 3013022 * 2
def baseEnd_3013022 : Nat := 343806335238047949170749

theorem tailTrace_3013022 : CollatzResearch.WordTrace tailWord_3013022 prefixEnd_3013022 343806335238047949170749 := by
  unfold tailWord_3013022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736742561292919004331165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73262626993562234689766213 13736742561292919004331165)
  ·
    refine ⟨5151278460484844626624187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13736742561292919004331165 5151278460484844626624187)
    ·
      refine ⟨7726917690727266939936281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151278460484844626624187 7726917690727266939936281)
      ·
        refine ⟨5795188268045450204952211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726917690727266939936281 5795188268045450204952211)
        ·
          refine ⟨8692782402068175307428317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795188268045450204952211 8692782402068175307428317)
          ·
            refine ⟨3259793400775565740285619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8692782402068175307428317 3259793400775565740285619)
            ·
              refine ⟨4889690101163348610428429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259793400775565740285619 4889690101163348610428429)
              ·
                refine ⟨1833633787936255728910661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889690101163348610428429 1833633787936255728910661)
                ·
                  refine ⟨343806335238047949170749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833633787936255728910661 343806335238047949170749)
                  ·
                    rfl

theorem cell22_3013022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3013022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013022 prefixEnd_3013022 := by exact prefixLift 3013022
  have htrace : WordTrace (prefixWord ++ tailWord_3013022) baseStart_3013022 baseEnd_3013022 := by
    simpa [prefixWord, tailWord_3013022, baseEnd_3013022] using wordTrace_append hprefix tailTrace_3013022
  have hstable : (prefixWord ++ tailWord_3013022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013022).length < 2 ^ (prefixWord ++ tailWord_3013022).sum := by decide
  have hdescent : baseEnd_3013022 < baseStart_3013022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013059 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_3013059 : Nat := 118140960795 + 3013059 * 2 ^ 59
def prefixEnd_3013059 : Nat := 4983230072969 + 3 ^ 40 * 3013059 * 2
def baseEnd_3013059 : Nat := 1031431671570288084337133

theorem tailTrace_3013059 : CollatzResearch.WordTrace tailWord_3013059 prefixEnd_3013059 1031431671570288084337133 := by
  unfold tailWord_3013059
  simp only [CollatzResearch.WordTrace]
  refine ⟨109895289991209307353746231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73263526660806204902497487 109895289991209307353746231)
  ·
    refine ⟨164842934986813961030619347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109895289991209307353746231 164842934986813961030619347)
    ·
      refine ⟨247264402480220941545929021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164842934986813961030619347 247264402480220941545929021)
      ·
        refine ⟨92724150930082853079723383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247264402480220941545929021 92724150930082853079723383)
        ·
          refine ⟨139086226395124279619585075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92724150930082853079723383 139086226395124279619585075)
          ·
            refine ⟨208629339592686419429377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139086226395124279619585075 208629339592686419429377613)
            ·
              refine ⟨78236002347257407286016605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208629339592686419429377613 78236002347257407286016605)
              ·
                refine ⟨29338500880221527732256227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78236002347257407286016605 29338500880221527732256227)
                ·
                  refine ⟨44007751320332291598384341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29338500880221527732256227 44007751320332291598384341)
                  ·
                    refine ⟨1031431671570288084337133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44007751320332291598384341 1031431671570288084337133)
                    ·
                      rfl

theorem cell22_3013059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_3013059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013059 prefixEnd_3013059 := by exact prefixLift 3013059
  have htrace : WordTrace (prefixWord ++ tailWord_3013059) baseStart_3013059 baseEnd_3013059 := by
    simpa [prefixWord, tailWord_3013059, baseEnd_3013059] using wordTrace_append hprefix tailTrace_3013059
  have hstable : (prefixWord ++ tailWord_3013059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013059).length < 2 ^ (prefixWord ++ tailWord_3013059).sum := by decide
  have hdescent : baseEnd_3013059 < baseStart_3013059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013155 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 2, 3]
def baseStart_3013155 : Nat := 118140960795 + 3013155 * 2 ^ 59
def prefixEnd_3013155 : Nat := 4983230072969 + 3 ^ 40 * 3013155 * 2
def baseEnd_3013155 : Nat := 1031464534332175833936839

theorem tailTrace_3013155 : CollatzResearch.WordTrace tailWord_3013155 prefixEnd_3013155 1031464534332175833936839 := by
  unfold tailWord_3013155
  simp only [CollatzResearch.WordTrace]
  refine ⟨109898791398861515749240919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73265860932574343832827279 109898791398861515749240919)
  ·
    refine ⟨164848187098292273623861379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109898791398861515749240919 164848187098292273623861379)
    ·
      refine ⟨247272280647438410435792069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164848187098292273623861379 247272280647438410435792069)
      ·
        refine ⟨46363552621394701956711013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247272280647438410435792069 46363552621394701956711013)
        ·
          refine ⟨8693166116511506616883315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46363552621394701956711013 8693166116511506616883315)
          ·
            refine ⟨13039749174767259925324973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693166116511506616883315 13039749174767259925324973)
            ·
              refine ⟨4889905940537722471996865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13039749174767259925324973 4889905940537722471996865)
              ·
                refine ⟨3667429455403291853997649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889905940537722471996865 3667429455403291853997649)
                ·
                  refine ⟨2750572091552468890498237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667429455403291853997649 2750572091552468890498237)
                  ·
                    refine ⟨1031464534332175833936839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750572091552468890498237 1031464534332175833936839)
                    ·
                      rfl

theorem cell22_3013155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].length) (baseStart_3013155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013155 prefixEnd_3013155 := by exact prefixLift 3013155
  have htrace : WordTrace (prefixWord ++ tailWord_3013155) baseStart_3013155 baseEnd_3013155 := by
    simpa [prefixWord, tailWord_3013155, baseEnd_3013155] using wordTrace_append hprefix tailTrace_3013155
  have hstable : (prefixWord ++ tailWord_3013155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013155).length < 2 ^ (prefixWord ++ tailWord_3013155).sum := by decide
  have hdescent : baseEnd_3013155 < baseStart_3013155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013183 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 3, 3]
def baseStart_3013183 : Nat := 118140960795 + 3013183 * 2 ^ 59
def prefixEnd_3013183 : Nat := 4983230072969 + 3 ^ 40 * 3013183 * 2
def baseEnd_3013183 : Nat := 1031474119304393094236753

theorem tailTrace_3013183 : CollatzResearch.WordTrace tailWord_3013183 prefixEnd_3013183 1031474119304393094236753 := by
  unfold tailWord_3013183
  simp only [CollatzResearch.WordTrace]
  refine ⟨109899812642760076531260203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73266541761840051020840135 109899812642760076531260203)
  ·
    refine ⟨164849718964140114796890305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109899812642760076531260203 164849718964140114796890305)
    ·
      refine ⟨123637289223105086097667729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164849718964140114796890305 123637289223105086097667729)
      ·
        refine ⟨92727966917328814573250797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123637289223105086097667729 92727966917328814573250797)
        ·
          refine ⟨34772987593998305464969049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92727966917328814573250797 34772987593998305464969049)
          ·
            refine ⟨26079740695498729098726787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34772987593998305464969049 26079740695498729098726787)
            ·
              refine ⟨39119611043248093648090181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26079740695498729098726787 39119611043248093648090181)
              ·
                refine ⟨7334927070609017559016909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39119611043248093648090181 7334927070609017559016909)
                ·
                  refine ⟨2750597651478381584631341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7334927070609017559016909 2750597651478381584631341)
                  ·
                    refine ⟨1031474119304393094236753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750597651478381584631341 1031474119304393094236753)
                    ·
                      rfl

theorem cell22_3013183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_3013183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013183 prefixEnd_3013183 := by exact prefixLift 3013183
  have htrace : WordTrace (prefixWord ++ tailWord_3013183) baseStart_3013183 baseEnd_3013183 := by
    simpa [prefixWord, tailWord_3013183, baseEnd_3013183] using wordTrace_append hprefix tailTrace_3013183
  have hstable : (prefixWord ++ tailWord_3013183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013183).length < 2 ^ (prefixWord ++ tailWord_3013183).sum := by decide
  have hdescent : baseEnd_3013183 < baseStart_3013183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013185 : List Nat := [1, 2, 5, 1, 1, 4, 2, 6]
def baseStart_3013185 : Nat := 118140960795 + 3013185 * 2 ^ 59
def prefixEnd_3013185 : Nat := 4983230072969 + 3 ^ 40 * 3013185 * 2
def baseEnd_3013185 : Nat := 114608311549473972854083

theorem tailTrace_3013185 : CollatzResearch.WordTrace tailWord_3013185 prefixEnd_3013185 114608311549473972854083 := by
  unfold tailWord_3013185
  simp only [CollatzResearch.WordTrace]
  refine ⟨109899885588752830872833009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73266590392501887248555339 109899885588752830872833009)
  ·
    refine ⟨82424914191564623154624757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109899885588752830872833009 82424914191564623154624757)
    ·
      refine ⟨7727335705459183420746071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82424914191564623154624757 7727335705459183420746071)
      ·
        refine ⟨11591003558188775131119107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7727335705459183420746071 11591003558188775131119107)
        ·
          refine ⟨17386505337283162696678661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11591003558188775131119107 17386505337283162696678661)
          ·
            refine ⟨3259969750740593005627249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17386505337283162696678661 3259969750740593005627249)
            ·
              refine ⟨2444977313055444754220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259969750740593005627249 2444977313055444754220437)
              ·
                refine ⟨114608311549473972854083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2444977313055444754220437 114608311549473972854083)
                ·
                  rfl

theorem cell22_3013185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 6].length) (baseStart_3013185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013185 prefixEnd_3013185 := by exact prefixLift 3013185
  have htrace : WordTrace (prefixWord ++ tailWord_3013185) baseStart_3013185 baseEnd_3013185 := by
    simpa [prefixWord, tailWord_3013185, baseEnd_3013185] using wordTrace_append hprefix tailTrace_3013185
  have hstable : (prefixWord ++ tailWord_3013185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013185).length < 2 ^ (prefixWord ++ tailWord_3013185).sum := by decide
  have hdescent : baseEnd_3013185 < baseStart_3013185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013196 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_3013196 : Nat := 118140960795 + 3013196 * 2 ^ 59
def prefixEnd_3013196 : Nat := 4983230072969 + 3 ^ 40 * 3013196 * 2
def baseEnd_3013196 : Nat := 343826189823355131220571

theorem tailTrace_3013196 : CollatzResearch.WordTrace tailWord_3013196 prefixEnd_3013196 343826189823355131220571 := by
  unfold tailWord_3013196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54950143395856489875741721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73266857861141986500988961 54950143395856489875741721)
  ·
    refine ⟨41212607546892367406806291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54950143395856489875741721 41212607546892367406806291)
    ·
      refine ⟨61818911320338551110209437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41212607546892367406806291 61818911320338551110209437)
      ·
        refine ⟨23182091745126956666328539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61818911320338551110209437 23182091745126956666328539)
        ·
          refine ⟨34773137617690434999492809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23182091745126956666328539 34773137617690434999492809)
          ·
            refine ⟨26079853213267826249619607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34773137617690434999492809 26079853213267826249619607)
            ·
              refine ⟨39119779819901739374429411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26079853213267826249619607 39119779819901739374429411)
              ·
                refine ⟨58679669729852609061644117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39119779819901739374429411 58679669729852609061644117)
                ·
                  refine ⟨343826189823355131220571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58679669729852609061644117 343826189823355131220571)
                  ·
                    rfl

theorem cell22_3013196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_3013196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013196 prefixEnd_3013196 := by exact prefixLift 3013196
  have htrace : WordTrace (prefixWord ++ tailWord_3013196) baseStart_3013196 baseEnd_3013196 := by
    simpa [prefixWord, tailWord_3013196, baseEnd_3013196] using wordTrace_append hprefix tailTrace_3013196
  have hstable : (prefixWord ++ tailWord_3013196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013196).length < 2 ^ (prefixWord ++ tailWord_3013196).sum := by decide
  have hdescent : baseEnd_3013196 < baseStart_3013196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013200 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_3013200 : Nat := 118140960795 + 3013200 * 2 ^ 59
def prefixEnd_3013200 : Nat := 4983230072969 + 3 ^ 40 * 3013200 * 2
def baseEnd_3013200 : Nat := 1031479938751810716561701

theorem tailTrace_3013200 : CollatzResearch.WordTrace tailWord_3013200 prefixEnd_3013200 1031479938751810716561701 := by
  unfold tailWord_3013200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54950216341849244217314527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73266955122465658956419369 54950216341849244217314527)
  ·
    refine ⟨82425324512773866325971791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54950216341849244217314527 82425324512773866325971791)
    ·
      refine ⟨123637986769160799488957687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82425324512773866325971791 123637986769160799488957687)
      ·
        refine ⟨185456980153741199233436531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123637986769160799488957687 185456980153741199233436531)
        ·
          refine ⟨278185470230611798850154797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185456980153741199233436531 278185470230611798850154797)
          ·
            refine ⟨104319551336479424568808049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278185470230611798850154797 104319551336479424568808049)
            ·
              refine ⟨78239663502359568426606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104319551336479424568808049 78239663502359568426606037)
              ·
                refine ⟨1833742113336552384998579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78239663502359568426606037 1833742113336552384998579)
                ·
                  refine ⟨2750613170004828577497869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833742113336552384998579 2750613170004828577497869)
                  ·
                    refine ⟨1031479938751810716561701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750613170004828577497869 1031479938751810716561701)
                    ·
                      rfl

theorem cell22_3013200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_3013200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013200 prefixEnd_3013200 := by exact prefixLift 3013200
  have htrace : WordTrace (prefixWord ++ tailWord_3013200) baseStart_3013200 baseEnd_3013200 := by
    simpa [prefixWord, tailWord_3013200, baseEnd_3013200] using wordTrace_append hprefix tailTrace_3013200
  have hstable : (prefixWord ++ tailWord_3013200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013200).length < 2 ^ (prefixWord ++ tailWord_3013200).sum := by decide
  have hdescent : baseEnd_3013200 < baseStart_3013200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013230 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_3013230 : Nat := 118140960795 + 3013230 * 2 ^ 59
def prefixEnd_3013230 : Nat := 4983230072969 + 3 ^ 40 * 3013230 * 2
def baseEnd_3013230 : Nat := 343830069454966879437203

theorem tailTrace_3013230 : CollatzResearch.WordTrace tailWord_3013230 prefixEnd_3013230 343830069454966879437203 := by
  unfold tailWord_3013230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737690859198725444777643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73267684582393202372147429 13737690859198725444777643)
  ·
    refine ⟨20606536288798088167166465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13737690859198725444777643 20606536288798088167166465)
    ·
      refine ⟨15454902216598566125374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20606536288798088167166465 15454902216598566125374849)
      ·
        refine ⟨11591176662448924594031137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15454902216598566125374849 11591176662448924594031137)
        ·
          refine ⟨8693382496836693445523353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11591176662448924594031137 8693382496836693445523353)
          ·
            refine ⟨6520036872627520084142515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8693382496836693445523353 6520036872627520084142515)
            ·
              refine ⟨9780055308941280126213773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520036872627520084142515 9780055308941280126213773)
              ·
                refine ⟨3667520740852980047330165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9780055308941280126213773 3667520740852980047330165)
                ·
                  refine ⟨343830069454966879437203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667520740852980047330165 343830069454966879437203)
                  ·
                    rfl

theorem cell22_3013230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_3013230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013230 prefixEnd_3013230 := by exact prefixLift 3013230
  have htrace : WordTrace (prefixWord ++ tailWord_3013230) baseStart_3013230 baseEnd_3013230 := by
    simpa [prefixWord, tailWord_3013230, baseEnd_3013230] using wordTrace_append hprefix tailTrace_3013230
  have hstable : (prefixWord ++ tailWord_3013230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013230).length < 2 ^ (prefixWord ++ tailWord_3013230).sum := by decide
  have hdescent : baseEnd_3013230 < baseStart_3013230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013243 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 1, 4]
def baseStart_3013243 : Nat := 118140960795 + 3013243 * 2 ^ 59
def prefixEnd_3013243 : Nat := 4983230072969 + 3 ^ 40 * 3013243 * 2
def baseEnd_3013243 : Nat := 1031494658530572937736569

theorem tailTrace_3013243 : CollatzResearch.WordTrace tailWord_3013243 prefixEnd_3013243 1031494658530572937736569 := by
  unfold tailWord_3013243
  simp only [CollatzResearch.WordTrace]
  refine ⟨109902001022542706778444383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73268000681695137852296255 109902001022542706778444383)
  ·
    refine ⟨164853001533814060167666575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109902001022542706778444383 164853001533814060167666575)
    ·
      refine ⟨247279502300721090251499863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164853001533814060167666575 247279502300721090251499863)
      ·
        refine ⟨370919253451081635377249795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247279502300721090251499863 370919253451081635377249795)
        ·
          refine ⟨556378880176622453065874693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370919253451081635377249795 556378880176622453065874693)
          ·
            refine ⟨104321040033116709949851505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 556378880176622453065874693 104321040033116709949851505)
            ·
              refine ⟨78240780024837532462388629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104321040033116709949851505 78240780024837532462388629)
              ·
                refine ⟨3667536563664259334174467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78240780024837532462388629 3667536563664259334174467)
                ·
                  refine ⟨5501304845496389001261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667536563664259334174467 5501304845496389001261701)
                  ·
                    refine ⟨1031494658530572937736569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501304845496389001261701 1031494658530572937736569)
                    ·
                      rfl

theorem cell22_3013243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_3013243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013243 prefixEnd_3013243 := by exact prefixLift 3013243
  have htrace : WordTrace (prefixWord ++ tailWord_3013243) baseStart_3013243 baseEnd_3013243 := by
    simpa [prefixWord, tailWord_3013243, baseEnd_3013243] using wordTrace_append hprefix tailTrace_3013243
  have hstable : (prefixWord ++ tailWord_3013243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013243).length < 2 ^ (prefixWord ++ tailWord_3013243).sum := by decide
  have hdescent : baseEnd_3013243 < baseStart_3013243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013324 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_3013324 : Nat := 118140960795 + 3013324 * 2 ^ 59
def prefixEnd_3013324 : Nat := 4983230072969 + 3 ^ 40 * 3013324 * 2
def baseEnd_3013324 : Nat := 1031522386485915726461321

theorem tailTrace_3013324 : CollatzResearch.WordTrace tailWord_3013324 prefixEnd_3013324 1031522386485915726461321 := by
  unfold tailWord_3013324
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952477667624628806071513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73269970223499505074762017 54952477667624628806071513)
  ·
    refine ⟨41214358250718471604553635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54952477667624628806071513 41214358250718471604553635)
    ·
      refine ⟨61821537376077707406830453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41214358250718471604553635 61821537376077707406830453)
      ·
        refine ⟨5795769129007285069390355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61821537376077707406830453 5795769129007285069390355)
        ·
          refine ⟨8693653693510927604085533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795769129007285069390355 8693653693510927604085533)
          ·
            refine ⟨3260120135066597851532075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8693653693510927604085533 3260120135066597851532075)
            ·
              refine ⟨4890180202599896777298113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260120135066597851532075 4890180202599896777298113)
              ·
                refine ⟨3667635151949922582973585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4890180202599896777298113 3667635151949922582973585)
                ·
                  refine ⟨2750726363962441937230189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667635151949922582973585 2750726363962441937230189)
                  ·
                    refine ⟨1031522386485915726461321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750726363962441937230189 1031522386485915726461321)
                    ·
                      rfl

theorem cell22_3013324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_3013324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013324 prefixEnd_3013324 := by exact prefixLift 3013324
  have htrace : WordTrace (prefixWord ++ tailWord_3013324) baseStart_3013324 baseEnd_3013324 := by
    simpa [prefixWord, tailWord_3013324, baseEnd_3013324] using wordTrace_append hprefix tailTrace_3013324
  have hstable : (prefixWord ++ tailWord_3013324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013324).length < 2 ^ (prefixWord ++ tailWord_3013324).sum := by decide
  have hdescent : baseEnd_3013324 < baseStart_3013324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013335 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 3, 3]
def baseStart_3013335 : Nat := 118140960795 + 3013335 * 2 ^ 59
def prefixEnd_3013335 : Nat := 4983230072969 + 3 ^ 40 * 3013335 * 2
def baseEnd_3013335 : Nat := 1031526152010715364436287

theorem tailTrace_3013335 : CollatzResearch.WordTrace tailWord_3013335 prefixEnd_3013335 1031526152010715364436287 := by
  unfold tailWord_3013335
  simp only [CollatzResearch.WordTrace]
  refine ⟨109905356538209406490793459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73270237692139604327195639 109905356538209406490793459)
  ·
    refine ⟨164858034807314109736190189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109905356538209406490793459 164858034807314109736190189)
    ·
      refine ⟨61821763052742791151071321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164858034807314109736190189 61821763052742791151071321)
      ·
        refine ⟨46366322289557093363303491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61821763052742791151071321 46366322289557093363303491)
        ·
          refine ⟨69549483434335640044955237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46366322289557093363303491 69549483434335640044955237)
          ·
            refine ⟨13040528143937932508429107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69549483434335640044955237 13040528143937932508429107)
            ·
              refine ⟨19560792215906898762643661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13040528143937932508429107 19560792215906898762643661)
              ·
                refine ⟨7335297080965087035991373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19560792215906898762643661 7335297080965087035991373)
                ·
                  refine ⟨2750736405361907638496765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7335297080965087035991373 2750736405361907638496765)
                  ·
                    refine ⟨1031526152010715364436287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750736405361907638496765 1031526152010715364436287)
                    ·
                      rfl

theorem cell22_3013335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_3013335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013335 prefixEnd_3013335 := by exact prefixLift 3013335
  have htrace : WordTrace (prefixWord ++ tailWord_3013335) baseStart_3013335 baseEnd_3013335 := by
    simpa [prefixWord, tailWord_3013335, baseEnd_3013335] using wordTrace_append hprefix tailTrace_3013335
  have hstable : (prefixWord ++ tailWord_3013335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013335).length < 2 ^ (prefixWord ++ tailWord_3013335).sum := by decide
  have hdescent : baseEnd_3013335 < baseStart_3013335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013399 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 5]
def baseStart_3013399 : Nat := 118140960795 + 3013399 * 2 ^ 59
def prefixEnd_3013399 : Nat := 4983230072969 + 3 ^ 40 * 3013399 * 2
def baseEnd_3013399 : Nat := 343849353506213510278697

theorem tailTrace_3013399 : CollatzResearch.WordTrace tailWord_3013399 prefixEnd_3013399 343849353506213510278697 := by
  unfold tailWord_3013399
  simp only [CollatzResearch.WordTrace]
  refine ⟨109907690809977545421123251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73271793873318363614082167 109907690809977545421123251)
  ·
    refine ⟨164861536214966318131684877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109907690809977545421123251 164861536214966318131684877)
    ·
      refine ⟨61823076080612369299381829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164861536214966318131684877 61823076080612369299381829)
      ·
        refine ⟨11591826765114819243634093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61823076080612369299381829 11591826765114819243634093)
        ·
          refine ⟨4346935036918057216362785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11591826765114819243634093 4346935036918057216362785)
          ·
            refine ⟨3260201277688542912272089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4346935036918057216362785 3260201277688542912272089)
            ·
              refine ⟨2445150958266407184204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260201277688542912272089 2445150958266407184204067)
              ·
                refine ⟨3667726437399610776306101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445150958266407184204067 3667726437399610776306101)
                ·
                  refine ⟨343849353506213510278697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667726437399610776306101 343849353506213510278697)
                  ·
                    rfl

theorem cell22_3013399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 5].length) (baseStart_3013399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013399 prefixEnd_3013399 := by exact prefixLift 3013399
  have htrace : WordTrace (prefixWord ++ tailWord_3013399) baseStart_3013399 baseEnd_3013399 := by
    simpa [prefixWord, tailWord_3013399, baseEnd_3013399] using wordTrace_append hprefix tailTrace_3013399
  have hstable : (prefixWord ++ tailWord_3013399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013399).length < 2 ^ (prefixWord ++ tailWord_3013399).sum := by decide
  have hdescent : baseEnd_3013399 < baseStart_3013399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013412 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_3013412 : Nat := 118140960795 + 3013412 * 2 ^ 59
def prefixEnd_3013412 : Nat := 4983230072969 + 3 ^ 40 * 3013412 * 2
def baseEnd_3013412 : Nat := 1031552510684312830261051

theorem tailTrace_3013412 : CollatzResearch.WordTrace tailWord_3013412 prefixEnd_3013412 1031552510684312830261051 := by
  unfold tailWord_3013412
  simp only [CollatzResearch.WordTrace]
  refine ⟨54954082479465224320673245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73272109972620299094230993 54954082479465224320673245)
  ·
    refine ⟨20607780929799459120252467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54954082479465224320673245 20607780929799459120252467)
    ·
      refine ⟨30911671394699188680378701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20607780929799459120252467 30911671394699188680378701)
      ·
        refine ⟨11591876773012195755142013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30911671394699188680378701 11591876773012195755142013)
        ·
          refine ⟨4346953789879573408178255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11591876773012195755142013 4346953789879573408178255)
          ·
            refine ⟨6520430684819360112267383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346953789879573408178255 6520430684819360112267383)
            ·
              refine ⟨9780646027229040168401075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520430684819360112267383 9780646027229040168401075)
              ·
                refine ⟨14670969040843560252601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780646027229040168401075 14670969040843560252601613)
                ·
                  refine ⟨5501613390316335094725605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14670969040843560252601613 5501613390316335094725605)
                  ·
                    refine ⟨1031552510684312830261051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501613390316335094725605 1031552510684312830261051)
                    ·
                      rfl

theorem cell22_3013412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_3013412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013412 prefixEnd_3013412 := by exact prefixLift 3013412
  have htrace : WordTrace (prefixWord ++ tailWord_3013412) baseStart_3013412 baseEnd_3013412 := by
    simpa [prefixWord, tailWord_3013412, baseEnd_3013412] using wordTrace_append hprefix tailTrace_3013412
  have hstable : (prefixWord ++ tailWord_3013412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013412).length < 2 ^ (prefixWord ++ tailWord_3013412).sum := by decide
  have hdescent : baseEnd_3013412 < baseStart_3013412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013425 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3013425 : Nat := 118140960795 + 3013425 * 2 ^ 59
def prefixEnd_3013425 : Nat := 4983230072969 + 3 ^ 40 * 3013425 * 2
def baseEnd_3013425 : Nat := 1031556960849985129686011

theorem tailTrace_3013425 : CollatzResearch.WordTrace tailWord_3013425 prefixEnd_3013425 1031556960849985129686011 := by
  unfold tailWord_3013425
  simp only [CollatzResearch.WordTrace]
  refine ⟨109908639107883351861569729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73272426071922234574379819 109908639107883351861569729)
  ·
    refine ⟨82431479330912513896177297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109908639107883351861569729 82431479330912513896177297)
    ·
      refine ⟨61823609498184385422132973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82431479330912513896177297 61823609498184385422132973)
      ·
        refine ⟨23183853561819144533299865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61823609498184385422132973 23183853561819144533299865)
        ·
          refine ⟨17387890171364358399974899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23183853561819144533299865 17387890171364358399974899)
          ·
            refine ⟨26081835257046537599962349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17387890171364358399974899 26081835257046537599962349)
            ·
              refine ⟨9780688221392451599985881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26081835257046537599962349 9780688221392451599985881)
              ·
                refine ⟨7335516166044338699989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9780688221392451599985881 7335516166044338699989411)
                ·
                  refine ⟨11003274249066508049984117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7335516166044338699989411 11003274249066508049984117)
                  ·
                    refine ⟨1031556960849985129686011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11003274249066508049984117 1031556960849985129686011)
                    ·
                      rfl

theorem cell22_3013425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3013425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013425 prefixEnd_3013425 := by exact prefixLift 3013425
  have htrace : WordTrace (prefixWord ++ tailWord_3013425) baseStart_3013425 baseEnd_3013425 := by
    simpa [prefixWord, tailWord_3013425, baseEnd_3013425] using wordTrace_append hprefix tailTrace_3013425
  have hstable : (prefixWord ++ tailWord_3013425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013425).length < 2 ^ (prefixWord ++ tailWord_3013425).sum := by decide
  have hdescent : baseEnd_3013425 < baseStart_3013425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013429 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3013429 : Nat := 118140960795 + 3013429 * 2 ^ 59
def prefixEnd_3013429 : Nat := 4983230072969 + 3 ^ 40 * 3013429 * 2
def baseEnd_3013429 : Nat := 1031558330131730452585999

theorem tailTrace_3013429 : CollatzResearch.WordTrace tailWord_3013429 prefixEnd_3013429 1031558330131730452585999 := by
  unfold tailWord_3013429
  simp only [CollatzResearch.WordTrace]
  refine ⟨109908784999868860544715341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73272523333245907029810227 109908784999868860544715341)
  ·
    refine ⟨41215794374950822704268253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109908784999868860544715341 41215794374950822704268253)
    ·
      refine ⟨15455922890606558514100595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41215794374950822704268253 15455922890606558514100595)
      ·
        refine ⟨23183884335909837771150893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15455922890606558514100595 23183884335909837771150893)
        ·
          refine ⟨8693956625966189164181585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23183884335909837771150893 8693956625966189164181585)
          ·
            refine ⟨6520467469474641873136189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8693956625966189164181585 6520467469474641873136189)
            ·
              refine ⟨2445175301052990702426071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6520467469474641873136189 2445175301052990702426071)
              ·
                refine ⟨3667762951579486053639107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445175301052990702426071 3667762951579486053639107)
                ·
                  refine ⟨5501644427369229080458661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667762951579486053639107 5501644427369229080458661)
                  ·
                    refine ⟨1031558330131730452585999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501644427369229080458661 1031558330131730452585999)
                    ·
                      rfl

theorem cell22_3013429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3013429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013429 prefixEnd_3013429 := by exact prefixLift 3013429
  have htrace : WordTrace (prefixWord ++ tailWord_3013429) baseStart_3013429 baseEnd_3013429 := by
    simpa [prefixWord, tailWord_3013429, baseEnd_3013429] using wordTrace_append hprefix tailTrace_3013429
  have hstable : (prefixWord ++ tailWord_3013429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013429).length < 2 ^ (prefixWord ++ tailWord_3013429).sum := by decide
  have hdescent : baseEnd_3013429 < baseStart_3013429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013515 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_3013515 : Nat := 118140960795 + 3013515 * 2 ^ 59
def prefixEnd_3013515 : Nat := 4983230072969 + 3 ^ 40 * 3013515 * 2
def baseEnd_3013515 : Nat := 1031587769689254894935735

theorem tailTrace_3013515 : CollatzResearch.WordTrace tailWord_3013515 prefixEnd_3013515 1031587769689254894935735 := by
  unfold tailWord_3013515
  simp only [CollatzResearch.WordTrace]
  refine ⟨109911921677557297232345999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73274614451704864821563999 109911921677557297232345999)
  ·
    refine ⟨164867882516335945848518999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109911921677557297232345999 164867882516335945848518999)
    ·
      refine ⟨247301823774503918772778499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164867882516335945848518999 247301823774503918772778499)
      ·
        refine ⟨370952735661755878159167749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247301823774503918772778499 370952735661755878159167749)
        ·
          refine ⟨69553637936579227154843953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370952735661755878159167749 69553637936579227154843953)
          ·
            refine ⟨52165228452434420366132965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69553637936579227154843953 52165228452434420366132965)
            ·
              refine ⟨9780980334831453818649931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52165228452434420366132965 9780980334831453818649931)
              ·
                refine ⟨14671470502247180727974897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780980334831453818649931 14671470502247180727974897)
                ·
                  refine ⟨11003602876685385545981173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14671470502247180727974897 11003602876685385545981173)
                  ·
                    refine ⟨1031587769689254894935735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11003602876685385545981173 1031587769689254894935735)
                    ·
                      rfl

theorem cell22_3013515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_3013515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013515 prefixEnd_3013515 := by exact prefixLift 3013515
  have htrace : WordTrace (prefixWord ++ tailWord_3013515) baseStart_3013515 baseEnd_3013515 := by
    simpa [prefixWord, tailWord_3013515, baseEnd_3013515] using wordTrace_append hprefix tailTrace_3013515
  have hstable : (prefixWord ++ tailWord_3013515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013515).length < 2 ^ (prefixWord ++ tailWord_3013515).sum := by decide
  have hdescent : baseEnd_3013515 < baseStart_3013515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013538 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3013538 : Nat := 118140960795 + 3013538 * 2 ^ 59
def prefixEnd_3013538 : Nat := 4983230072969 + 3 ^ 40 * 3013538 * 2
def baseEnd_3013538 : Nat := 1031595643059290501610665

theorem tailTrace_3013538 : CollatzResearch.WordTrace tailWord_3013538 prefixEnd_3013538 1031595643059290501610665 := by
  unfold tailWord_3013538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478190139118493040108317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73275173704315981440288845 27478190139118493040108317)
  ·
    refine ⟨10304321302169434890040619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27478190139118493040108317 10304321302169434890040619)
    ·
      refine ⟨15456481953254152335060929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10304321302169434890040619 15456481953254152335060929)
      ·
        refine ⟨11592361464940614251295697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15456481953254152335060929 11592361464940614251295697)
        ·
          refine ⟨8694271098705460688471773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11592361464940614251295697 8694271098705460688471773)
          ·
            refine ⟨3260351662014547758176915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8694271098705460688471773 3260351662014547758176915)
            ·
              refine ⟨4890527493021821637265373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260351662014547758176915 4890527493021821637265373)
              ·
                refine ⟨1833947809883183113974515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4890527493021821637265373 1833947809883183113974515)
                ·
                  refine ⟨2750921714824774670961773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833947809883183113974515 2750921714824774670961773)
                  ·
                    refine ⟨1031595643059290501610665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750921714824774670961773 1031595643059290501610665)
                    ·
                      rfl

theorem cell22_3013538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3013538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013538 prefixEnd_3013538 := by exact prefixLift 3013538
  have htrace : WordTrace (prefixWord ++ tailWord_3013538) baseStart_3013538 baseEnd_3013538 := by
    simpa [prefixWord, tailWord_3013538, baseEnd_3013538] using wordTrace_append hprefix tailTrace_3013538
  have hstable : (prefixWord ++ tailWord_3013538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013538).length < 2 ^ (prefixWord ++ tailWord_3013538).sum := by decide
  have hdescent : baseEnd_3013538 < baseStart_3013538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013575 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3013575 : Nat := 118140960795 + 3013575 * 2 ^ 59
def prefixEnd_3013575 : Nat := 4983230072969 + 3 ^ 40 * 3013575 * 2
def baseEnd_3013575 : Nat := 1031608308915434738435551

theorem tailTrace_3013575 : CollatzResearch.WordTrace tailWord_3013575 prefixEnd_3013575 1031608308915434738435551 := by
  unfold tailWord_3013575
  simp only [CollatzResearch.WordTrace]
  refine ⟨109914110057339927479530179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73276073371559951653020119 109914110057339927479530179)
  ·
    refine ⟨164871165086009891219295269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109914110057339927479530179 164871165086009891219295269)
    ·
      refine ⟨30913343453626854603617863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164871165086009891219295269 30913343453626854603617863)
      ·
        refine ⟨46370015180440281905426795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30913343453626854603617863 46370015180440281905426795)
        ·
          refine ⟨69555022770660422858140193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46370015180440281905426795 69555022770660422858140193)
          ·
            refine ⟨52166267077995317143605145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69555022770660422858140193 52166267077995317143605145)
            ·
              refine ⟨39124700308496487857703859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52166267077995317143605145 39124700308496487857703859)
              ·
                refine ⟨58687050462744731786555789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39124700308496487857703859 58687050462744731786555789)
                ·
                  refine ⟨22007643923529274419958421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58687050462744731786555789 22007643923529274419958421)
                  ·
                    refine ⟨1031608308915434738435551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22007643923529274419958421 1031608308915434738435551)
                    ·
                      rfl

theorem cell22_3013575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3013575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013575 prefixEnd_3013575 := by exact prefixLift 3013575
  have htrace : WordTrace (prefixWord ++ tailWord_3013575) baseStart_3013575 baseEnd_3013575 := by
    simpa [prefixWord, tailWord_3013575, baseEnd_3013575] using wordTrace_append hprefix tailTrace_3013575
  have hstable : (prefixWord ++ tailWord_3013575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013575).length < 2 ^ (prefixWord ++ tailWord_3013575).sum := by decide
  have hdescent : baseEnd_3013575 < baseStart_3013575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013592 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3013592 : Nat := 118140960795 + 3013592 * 2 ^ 59
def prefixEnd_3013592 : Nat := 4983230072969 + 3 ^ 40 * 3013592 * 2
def baseEnd_3013592 : Nat := 1031614128362852360760499

theorem tailTrace_3013592 : CollatzResearch.WordTrace tailWord_3013592 prefixEnd_3013592 1031614128362852360760499 := by
  unfold tailWord_3013592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54957365049139169691449515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73276486732185559588599353 54957365049139169691449515)
  ·
    refine ⟨82436047573708754537174273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54957365049139169691449515 82436047573708754537174273)
    ·
      refine ⟨61827035680281565902880705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82436047573708754537174273 61827035680281565902880705)
      ·
        refine ⟨46370276760211174427160529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61827035680281565902880705 46370276760211174427160529)
        ·
          refine ⟨34777707570158380820370397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46370276760211174427160529 34777707570158380820370397)
          ·
            refine ⟨13041640338809392807638899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34777707570158380820370397 13041640338809392807638899)
            ·
              refine ⟨19562460508214089211458349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13041640338809392807638899 19562460508214089211458349)
              ·
                refine ⟨7335922690580283454296881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19562460508214089211458349 7335922690580283454296881)
                ·
                  refine ⟨5501942017935212590722661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7335922690580283454296881 5501942017935212590722661)
                  ·
                    refine ⟨1031614128362852360760499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5501942017935212590722661 1031614128362852360760499)
                    ·
                      rfl

theorem cell22_3013592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3013592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013592 prefixEnd_3013592 := by exact prefixLift 3013592
  have htrace : WordTrace (prefixWord ++ tailWord_3013592) baseStart_3013592 baseEnd_3013592 := by
    simpa [prefixWord, tailWord_3013592, baseEnd_3013592] using wordTrace_append hprefix tailTrace_3013592
  have hstable : (prefixWord ++ tailWord_3013592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013592).length < 2 ^ (prefixWord ++ tailWord_3013592).sum := by decide
  have hdescent : baseEnd_3013592 < baseStart_3013592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013635 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 11]
def baseStart_3013635 : Nat := 118140960795 + 3013635 * 2 ^ 59
def prefixEnd_3013635 : Nat := 4983230072969 + 3 ^ 40 * 3013635 * 2
def baseEnd_3013635 : Nat := 343876282713871527311789

theorem tailTrace_3013635 : CollatzResearch.WordTrace tailWord_3013635 prefixEnd_3013635 343876282713871527311789 := by
  unfold tailWord_3013635
  simp only [CollatzResearch.WordTrace]
  refine ⟨109916298437122557726714359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73277532291415038484476239 109916298437122557726714359)
  ·
    refine ⟨164874447655683836590071539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109916298437122557726714359 164874447655683836590071539)
    ·
      refine ⟨247311671483525754885107309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164874447655683836590071539 247311671483525754885107309)
      ·
        refine ⟨92741876806322158081915241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247311671483525754885107309 92741876806322158081915241)
        ·
          refine ⟨69556407604741618561436431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92741876806322158081915241 69556407604741618561436431)
          ·
            refine ⟨104334611407112427842154647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69556407604741618561436431 104334611407112427842154647)
            ·
              refine ⟨156501917110668641763231971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104334611407112427842154647 156501917110668641763231971)
              ·
                refine ⟨234752875666002962644847957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156501917110668641763231971 234752875666002962644847957)
                ·
                  refine ⟨343876282713871527311789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 234752875666002962644847957 343876282713871527311789)
                  ·
                    rfl

theorem cell22_3013635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_3013635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013635 prefixEnd_3013635 := by exact prefixLift 3013635
  have htrace : WordTrace (prefixWord ++ tailWord_3013635) baseStart_3013635 baseEnd_3013635 := by
    simpa [prefixWord, tailWord_3013635, baseEnd_3013635] using wordTrace_append hprefix tailTrace_3013635
  have hstable : (prefixWord ++ tailWord_3013635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013635).length < 2 ^ (prefixWord ++ tailWord_3013635).sum := by decide
  have hdescent : baseEnd_3013635 < baseStart_3013635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013639 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3013639 : Nat := 118140960795 + 3013639 * 2 ^ 59
def prefixEnd_3013639 : Nat := 4983230072969 + 3 ^ 40 * 3013639 * 2
def baseEnd_3013639 : Nat := 1031630217423359904835355

theorem tailTrace_3013639 : CollatzResearch.WordTrace tailWord_3013639 prefixEnd_3013639 1031630217423359904835355 := by
  unfold tailWord_3013639
  simp only [CollatzResearch.WordTrace]
  refine ⟨109916444329108066409859971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73277629552738710939906647 109916444329108066409859971)
  ·
    refine ⟨164874666493662099614789957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109916444329108066409859971 164874666493662099614789957)
    ·
      refine ⟨30913999967561643677773117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164874666493662099614789957 30913999967561643677773117)
      ·
        refine ⟨11592749987835616379164919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30913999967561643677773117 11592749987835616379164919)
        ·
          refine ⟨17389124981753424568747379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11592749987835616379164919 17389124981753424568747379)
          ·
            refine ⟨26083687472630136853121069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17389124981753424568747379 26083687472630136853121069)
            ·
              refine ⟨9781382802236301319920401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26083687472630136853121069 9781382802236301319920401)
              ·
                refine ⟨7336037101677225989940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781382802236301319920401 7336037101677225989940301)
                ·
                  refine ⟨2751013913128959746227613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7336037101677225989940301 2751013913128959746227613)
                  ·
                    refine ⟨1031630217423359904835355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751013913128959746227613 1031630217423359904835355)
                    ·
                      rfl

theorem cell22_3013639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3013639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013639 prefixEnd_3013639 := by exact prefixLift 3013639
  have htrace : WordTrace (prefixWord ++ tailWord_3013639) baseStart_3013639 baseEnd_3013639 := by
    simpa [prefixWord, tailWord_3013639, baseEnd_3013639] using wordTrace_append hprefix tailTrace_3013639
  have hstable : (prefixWord ++ tailWord_3013639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013639).length < 2 ^ (prefixWord ++ tailWord_3013639).sum := by decide
  have hdescent : baseEnd_3013639 < baseStart_3013639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013656 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_3013656 : Nat := 118140960795 + 3013656 * 2 ^ 59
def prefixEnd_3013656 : Nat := 4983230072969 + 3 ^ 40 * 3013656 * 2
def baseEnd_3013656 : Nat := 1031636036870777527160303

theorem tailTrace_3013656 : CollatzResearch.WordTrace tailWord_3013656 prefixEnd_3013656 1031636036870777527160303 := by
  unfold tailWord_3013656
  simp only [CollatzResearch.WordTrace]
  refine ⟨54958532185023239156614411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73278042913364318875485881 54958532185023239156614411)
  ·
    refine ⟨82437798277534858734921617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54958532185023239156614411 82437798277534858734921617)
    ·
      refine ⟨61828348708151144051191213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82437798277534858734921617 61828348708151144051191213)
      ·
        refine ⟨23185630765556679019196705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61828348708151144051191213 23185630765556679019196705)
        ·
          refine ⟨17389223074167509264397529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23185630765556679019196705 17389223074167509264397529)
          ·
            refine ⟨13041917305625631948298147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17389223074167509264397529 13041917305625631948298147)
            ·
              refine ⟨19562875958438447922447221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13041917305625631948298147 19562875958438447922447221)
              ·
                refine ⟨1834019621103604492729427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19562875958438447922447221 1834019621103604492729427)
                ·
                  refine ⟨2751029431655406739094141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834019621103604492729427 2751029431655406739094141)
                  ·
                    refine ⟨1031636036870777527160303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751029431655406739094141 1031636036870777527160303)
                    ·
                      rfl

theorem cell22_3013656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_3013656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013656 prefixEnd_3013656 := by exact prefixLift 3013656
  have htrace : WordTrace (prefixWord ++ tailWord_3013656) baseStart_3013656 baseEnd_3013656 := by
    simpa [prefixWord, tailWord_3013656, baseEnd_3013656] using wordTrace_append hprefix tailTrace_3013656
  have hstable : (prefixWord ++ tailWord_3013656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013656).length < 2 ^ (prefixWord ++ tailWord_3013656).sum := by decide
  have hdescent : baseEnd_3013656 < baseStart_3013656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013667 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_3013667 : Nat := 118140960795 + 3013667 * 2 ^ 59
def prefixEnd_3013667 : Nat := 4983230072969 + 3 ^ 40 * 3013667 * 2
def baseEnd_3013667 : Nat := 1031639802395577165135269

theorem tailTrace_3013667 : CollatzResearch.WordTrace tailWord_3013667 prefixEnd_3013667 1031639802395577165135269 := by
  unfold tailWord_3013667
  simp only [CollatzResearch.WordTrace]
  refine ⟨109917465573006627191879255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73278310382004418127919503 109917465573006627191879255)
  ·
    refine ⟨164876198359509940787818883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109917465573006627191879255 164876198359509940787818883)
    ·
      refine ⟨247314297539264911181728325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164876198359509940787818883 247314297539264911181728325)
      ·
        refine ⟨46371430788612170846574061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247314297539264911181728325 46371430788612170846574061)
        ·
          refine ⟨17389286545729564067465273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46371430788612170846574061 17389286545729564067465273)
          ·
            refine ⟨13041964909297173050598955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17389286545729564067465273 13041964909297173050598955)
            ·
              refine ⟨19562947363945759575898433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13041964909297173050598955 19562947363945759575898433)
              ·
                refine ⟨14672210522959319681923825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19562947363945759575898433 14672210522959319681923825)
                ·
                  refine ⟨11004157892219489761442869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14672210522959319681923825 11004157892219489761442869)
                  ·
                    refine ⟨1031639802395577165135269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11004157892219489761442869 1031639802395577165135269)
                    ·
                      rfl

theorem cell22_3013667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_3013667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013667 prefixEnd_3013667 := by exact prefixLift 3013667
  have htrace : WordTrace (prefixWord ++ tailWord_3013667) baseStart_3013667 baseEnd_3013667 := by
    simpa [prefixWord, tailWord_3013667, baseEnd_3013667] using wordTrace_append hprefix tailTrace_3013667
  have hstable : (prefixWord ++ tailWord_3013667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013667).length < 2 ^ (prefixWord ++ tailWord_3013667).sum := by decide
  have hdescent : baseEnd_3013667 < baseStart_3013667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013699 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 1, 4]
def baseStart_3013699 : Nat := 118140960795 + 3013699 * 2 ^ 59
def prefixEnd_3013699 : Nat := 4983230072969 + 3 ^ 40 * 3013699 * 2
def baseEnd_3013699 : Nat := 1031650756649539748335171

theorem tailTrace_3013699 : CollatzResearch.WordTrace tailWord_3013699 prefixEnd_3013699 1031650756649539748335171 := by
  unfold tailWord_3013699
  simp only [CollatzResearch.WordTrace]
  refine ⟨109918632708890696657044151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73279088472593797771362767 109918632708890696657044151)
  ·
    refine ⟨164877949063336044985566227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109918632708890696657044151 164877949063336044985566227)
    ·
      refine ⟨247316923595004067478349341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164877949063336044985566227 247316923595004067478349341)
      ·
        refine ⟨92743846348126525304381003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247316923595004067478349341 92743846348126525304381003)
        ·
          refine ⟨139115769522189787956571505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92743846348126525304381003 139115769522189787956571505)
          ·
            refine ⟨104336827141642340967428629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139115769522189787956571505 104336827141642340967428629)
            ·
              refine ⟨4890788772264484732848217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104336827141642340967428629 4890788772264484732848217)
              ·
                refine ⟨3668091579198363549636163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4890788772264484732848217 3668091579198363549636163)
                ·
                  refine ⟨5502137368797545324454245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668091579198363549636163 5502137368797545324454245)
                  ·
                    refine ⟨1031650756649539748335171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502137368797545324454245 1031650756649539748335171)
                    ·
                      rfl

theorem cell22_3013699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_3013699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013699 prefixEnd_3013699 := by exact prefixLift 3013699
  have htrace : WordTrace (prefixWord ++ tailWord_3013699) baseStart_3013699 baseEnd_3013699 := by
    simpa [prefixWord, tailWord_3013699, baseEnd_3013699] using wordTrace_append hprefix tailTrace_3013699
  have hstable : (prefixWord ++ tailWord_3013699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013699).length < 2 ^ (prefixWord ++ tailWord_3013699).sum := by decide
  have hdescent : baseEnd_3013699 < baseStart_3013699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013712 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_3013712 : Nat := 118140960795 + 3013712 * 2 ^ 59
def prefixEnd_3013712 : Nat := 4983230072969 + 3 ^ 40 * 3013712 * 2
def baseEnd_3013712 : Nat := 1031655206815212047760131

theorem tailTrace_3013712 : CollatzResearch.WordTrace tailWord_3013712 prefixEnd_3013712 1031655206815212047760131 := by
  unfold tailWord_3013712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54959553428921799938633695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73279404571895733251511593 54959553428921799938633695)
  ·
    refine ⟨82439330143382699907950543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54959553428921799938633695 82439330143382699907950543)
    ·
      refine ⟨123658995215074049861925815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82439330143382699907950543 123658995215074049861925815)
      ·
        refine ⟨185488492822611074792888723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123658995215074049861925815 185488492822611074792888723)
        ·
          refine ⟨278232739233916612189333085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185488492822611074792888723 278232739233916612189333085)
          ·
            refine ⟨104337277212718729570999907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278232739233916612189333085 104337277212718729570999907)
            ·
              refine ⟨156505915819078094356499861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104337277212718729570999907 156505915819078094356499861)
              ·
                refine ⟨7336214804019285672960931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156505915819078094356499861 7336214804019285672960931)
                ·
                  refine ⟨11004322206028928509441397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7336214804019285672960931 11004322206028928509441397)
                  ·
                    refine ⟨1031655206815212047760131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11004322206028928509441397 1031655206815212047760131)
                    ·
                      rfl

theorem cell22_3013712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_3013712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013712 prefixEnd_3013712 := by exact prefixLift 3013712
  have htrace : WordTrace (prefixWord ++ tailWord_3013712) baseStart_3013712 baseEnd_3013712 := by
    simpa [prefixWord, tailWord_3013712, baseEnd_3013712] using wordTrace_append hprefix tailTrace_3013712
  have hstable : (prefixWord ++ tailWord_3013712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013712).length < 2 ^ (prefixWord ++ tailWord_3013712).sum := by decide
  have hdescent : baseEnd_3013712 < baseStart_3013712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013729 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3013729 : Nat := 118140960795 + 3013729 * 2 ^ 59
def prefixEnd_3013729 : Nat := 4983230072969 + 3 ^ 40 * 3013729 * 2
def baseEnd_3013729 : Nat := 1031661026262629670085079

theorem tailTrace_3013729 : CollatzResearch.WordTrace tailWord_3013729 prefixEnd_3013729 1031661026262629670085079 := by
  unfold tailWord_3013729
  simp only [CollatzResearch.WordTrace]
  refine ⟨109919726898782011780636241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73279817932521341187090827 109919726898782011780636241)
  ·
    refine ⟨82439795174086508835477181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109919726898782011780636241 82439795174086508835477181)
    ·
      refine ⟨30914923190282440813303943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82439795174086508835477181 30914923190282440813303943)
      ·
        refine ⟨46372384785423661219955915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30914923190282440813303943 46372384785423661219955915)
        ·
          refine ⟨69558577178135491829933873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46372384785423661219955915 69558577178135491829933873)
          ·
            refine ⟨52168932883601618872450405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69558577178135491829933873 52168932883601618872450405)
            ·
              refine ⟨9781674915675303538584451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52168932883601618872450405 9781674915675303538584451)
              ·
                refine ⟨14672512373512955307876677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9781674915675303538584451 14672512373512955307876677)
                ·
                  refine ⟨2751096070033679120226877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14672512373512955307876677 2751096070033679120226877)
                  ·
                    refine ⟨1031661026262629670085079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751096070033679120226877 1031661026262629670085079)
                    ·
                      rfl

theorem cell22_3013729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3013729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013729 prefixEnd_3013729 := by exact prefixLift 3013729
  have htrace : WordTrace (prefixWord ++ tailWord_3013729) baseStart_3013729 baseEnd_3013729 := by
    simpa [prefixWord, tailWord_3013729, baseEnd_3013729] using wordTrace_append hprefix tailTrace_3013729
  have hstable : (prefixWord ++ tailWord_3013729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013729).length < 2 ^ (prefixWord ++ tailWord_3013729).sum := by decide
  have hdescent : baseEnd_3013729 < baseStart_3013729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013746 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_3013746 : Nat := 118140960795 + 3013746 * 2 ^ 59
def prefixEnd_3013746 : Nat := 4983230072969 + 3 ^ 40 * 3013746 * 2
def baseEnd_3013746 : Nat := 1031666845710047292410027

theorem tailTrace_3013746 : CollatzResearch.WordTrace tailWord_3013746 prefixEnd_3013746 1031666845710047292410027 := by
  unfold tailWord_3013746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480086734930105921001273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73280231293146949122670061 27480086734930105921001273)
  ·
    refine ⟨20610065051197579440750955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27480086734930105921001273 20610065051197579440750955)
    ·
      refine ⟨30915097576796369161126433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610065051197579440750955 30915097576796369161126433)
      ·
        refine ⟨23186323182597276870844825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30915097576796369161126433 23186323182597276870844825)
        ·
          refine ⟨17389742386947957653133619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23186323182597276870844825 17389742386947957653133619)
          ·
            refine ⟨26084613580421936479700429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17389742386947957653133619 26084613580421936479700429)
            ·
              refine ⟨9781730092658226179887661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26084613580421936479700429 9781730092658226179887661)
              ·
                refine ⟨3668148784746834817457873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9781730092658226179887661 3668148784746834817457873)
                ·
                  refine ⟨2751111588560126113093405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668148784746834817457873 2751111588560126113093405)
                  ·
                    refine ⟨1031666845710047292410027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751111588560126113093405 1031666845710047292410027)
                    ·
                      rfl

theorem cell22_3013746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_3013746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013746 prefixEnd_3013746 := by exact prefixLift 3013746
  have htrace : WordTrace (prefixWord ++ tailWord_3013746) baseStart_3013746 baseEnd_3013746 := by
    simpa [prefixWord, tailWord_3013746, baseEnd_3013746] using wordTrace_append hprefix tailTrace_3013746
  have hstable : (prefixWord ++ tailWord_3013746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013746).length < 2 ^ (prefixWord ++ tailWord_3013746).sum := by decide
  have hdescent : baseEnd_3013746 < baseStart_3013746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013761 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3013761 : Nat := 118140960795 + 3013761 * 2 ^ 59
def prefixEnd_3013761 : Nat := 4983230072969 + 3 ^ 40 * 3013761 * 2
def baseEnd_3013761 : Nat := 1031671980516592253284981

theorem tailTrace_3013761 : CollatzResearch.WordTrace tailWord_3013761 prefixEnd_3013761 1031671980516592253284981 := by
  unfold tailWord_3013761
  simp only [CollatzResearch.WordTrace]
  refine ⟨109920894034666081245801137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73280596023110720830534091 109920894034666081245801137)
  ·
    refine ⟨82440670525999560934350853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109920894034666081245801137 82440670525999560934350853)
    ·
      refine ⟨15457625723624917675190785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82440670525999560934350853 15457625723624917675190785)
      ·
        refine ⟨11593219292718688256393089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15457625723624917675190785 11593219292718688256393089)
        ·
          refine ⟨8694914469539016192294817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11593219292718688256393089 8694914469539016192294817)
          ·
            refine ⟨6521185852154262144221113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8694914469539016192294817 6521185852154262144221113)
            ·
              refine ⟨4890889389115696608165835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6521185852154262144221113 4890889389115696608165835)
              ·
                refine ⟨7336334083673544912248753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890889389115696608165835 7336334083673544912248753)
                ·
                  refine ⟨5502250562755158684186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336334083673544912248753 5502250562755158684186565)
                  ·
                    refine ⟨1031671980516592253284981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502250562755158684186565 1031671980516592253284981)
                    ·
                      rfl

theorem cell22_3013761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3013761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013761 prefixEnd_3013761 := by exact prefixLift 3013761
  have htrace : WordTrace (prefixWord ++ tailWord_3013761) baseStart_3013761 baseEnd_3013761 := by
    simpa [prefixWord, tailWord_3013761, baseEnd_3013761] using wordTrace_append hprefix tailTrace_3013761
  have hstable : (prefixWord ++ tailWord_3013761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013761).length < 2 ^ (prefixWord ++ tailWord_3013761).sum := by decide
  have hdescent : baseEnd_3013761 < baseStart_3013761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013772 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_3013772 : Nat := 118140960795 + 3013772 * 2 ^ 59
def prefixEnd_3013772 : Nat := 4983230072969 + 3 ^ 40 * 3013772 * 2
def baseEnd_3013772 : Nat := 1031675746041391891259947

theorem tailTrace_3013772 : CollatzResearch.WordTrace tailWord_3013772 prefixEnd_3013772 1031675746041391891259947 := by
  unfold tailWord_3013772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54960647618813115062225785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73280863491750820082967713 54960647618813115062225785)
  ·
    refine ⟨41220485714109836296669339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54960647618813115062225785 41220485714109836296669339)
    ·
      refine ⟨61830728571164754445004009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41220485714109836296669339 61830728571164754445004009)
      ·
        refine ⟨46373046428373565833753007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61830728571164754445004009 46373046428373565833753007)
        ·
          refine ⟨69559569642560348750629511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46373046428373565833753007 69559569642560348750629511)
          ·
            refine ⟨104339354463840523125944267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69559569642560348750629511 104339354463840523125944267)
            ·
              refine ⟨156509031695760784688916401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104339354463840523125944267 156509031695760784688916401)
              ·
                refine ⟨117381773771820588516687301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156509031695760784688916401 117381773771820588516687301)
                ·
                  refine ⟨22009082582216360346878869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117381773771820588516687301 22009082582216360346878869)
                  ·
                    refine ⟨1031675746041391891259947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22009082582216360346878869 1031675746041391891259947)
                    ·
                      rfl

theorem cell22_3013772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_3013772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013772 prefixEnd_3013772 := by exact prefixLift 3013772
  have htrace : WordTrace (prefixWord ++ tailWord_3013772) baseStart_3013772 baseEnd_3013772 := by
    simpa [prefixWord, tailWord_3013772, baseEnd_3013772] using wordTrace_append hprefix tailTrace_3013772
  have hstable : (prefixWord ++ tailWord_3013772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013772).length < 2 ^ (prefixWord ++ tailWord_3013772).sum := by decide
  have hdescent : baseEnd_3013772 < baseStart_3013772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3013825 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3013825 : Nat := 118140960795 + 3013825 * 2 ^ 59
def prefixEnd_3013825 : Nat := 4983230072969 + 3 ^ 40 * 3013825 * 2
def baseEnd_3013825 : Nat := 1031693889024517419684785

theorem tailTrace_3013825 : CollatzResearch.WordTrace tailWord_3013825 prefixEnd_3013825 1031693889024517419684785 := by
  unfold tailWord_3013825
  simp only [CollatzResearch.WordTrace]
  refine ⟨109923228306434220176130929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73282152204289480117420619 109923228306434220176130929)
  ·
    refine ⟨82442421229825665132098197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109923228306434220176130929 82442421229825665132098197)
    ·
      refine ⟨3864488495148078053067103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82442421229825665132098197 3864488495148078053067103)
      ·
        refine ⟨5796732742722117079600655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864488495148078053067103 5796732742722117079600655)
        ·
          refine ⟨8695099114083175619400983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796732742722117079600655 8695099114083175619400983)
          ·
            refine ⟨13042648671124763429101475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695099114083175619400983 13042648671124763429101475)
            ·
              refine ⟨19563973006687145143652213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13042648671124763429101475 19563973006687145143652213)
              ·
                refine ⟨1834122469376919857217395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19563973006687145143652213 1834122469376919857217395)
                ·
                  refine ⟨2751183704065379785826093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834122469376919857217395 2751183704065379785826093)
                  ·
                    refine ⟨1031693889024517419684785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2751183704065379785826093 1031693889024517419684785)
                    ·
                      rfl

theorem cell22_3013825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3013825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3013825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3013825 prefixEnd_3013825 := by exact prefixLift 3013825
  have htrace : WordTrace (prefixWord ++ tailWord_3013825) baseStart_3013825 baseEnd_3013825 := by
    simpa [prefixWord, tailWord_3013825, baseEnd_3013825] using wordTrace_append hprefix tailTrace_3013825
  have hstable : (prefixWord ++ tailWord_3013825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3013825).length < 2 ^ (prefixWord ++ tailWord_3013825).sum := by decide
  have hdescent : baseEnd_3013825 < baseStart_3013825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3013825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
