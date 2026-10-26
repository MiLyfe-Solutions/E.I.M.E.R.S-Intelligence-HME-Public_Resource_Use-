import V185TrunkScan23Chunk0081

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_487212 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_487212 : Nat := 118140960795 + 487212 * 2 ^ 59
def prefixEnd_487212 : Nat := 4983230072969 + 3 ^ 40 * 487212 * 2
def baseEnd_487212 : Nat := 250173936638453014509359

theorem tailTrace_487212 : CollatzResearch.WordTrace tailWord_487212 prefixEnd_487212 250173936638453014509359 := by
  unfold tailWord_487212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885040755460804015043945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11846721007281072020058593 8885040755460804015043945)
  ·
    refine ⟨6663780566595603011282959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885040755460804015043945 6663780566595603011282959)
    ·
      refine ⟨9995670849893404516924439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6663780566595603011282959 9995670849893404516924439)
      ·
        refine ⟨14993506274840106775386659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995670849893404516924439 14993506274840106775386659)
        ·
          refine ⟨22490259412260160163079989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993506274840106775386659 22490259412260160163079989)
          ·
            refine ⟨2108461819899390015288749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22490259412260160163079989 2108461819899390015288749)
            ·
              refine ⟨790673182462271255733281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108461819899390015288749 790673182462271255733281)
              ·
                refine ⟨593004886846703441799961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790673182462271255733281 593004886846703441799961)
                ·
                  refine ⟨444753665135027581349971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593004886846703441799961 444753665135027581349971)
                  ·
                    refine ⟨667130497702541372024957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444753665135027581349971 667130497702541372024957)
                    ·
                      refine ⟨250173936638453014509359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667130497702541372024957 250173936638453014509359)
                      ·
                        rfl

theorem cell23_487212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_487212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487212 prefixEnd_487212 := by exact prefixLift 487212
  have htrace : WordTrace (prefixWord ++ tailWord_487212) baseStart_487212 baseEnd_487212 := by
    simpa [prefixWord, tailWord_487212, baseEnd_487212] using wordTrace_append hprefix tailTrace_487212
  have hstable : (prefixWord ++ tailWord_487212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487212).length < 2 ^ (prefixWord ++ tailWord_487212).sum := by decide
  have hdescent : baseEnd_487212 < baseStart_487212 := by decide
  rcases family_descends (prefixWord ++ tailWord_487212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487228 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_487228 : Nat := 118140960795 + 487228 * 2 ^ 59
def prefixEnd_487228 : Nat := 4983230072969 + 3 ^ 40 * 487228 * 2
def baseEnd_487228 : Nat := 83394050776308317303095

theorem tailTrace_487228 : CollatzResearch.WordTrace tailWord_487228 prefixEnd_487228 83394050776308317303095 := by
  unfold tailWord_487228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885332539431821381335169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11847110052575761841780225 8885332539431821381335169)
  ·
    refine ⟨6663999404573866036001377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885332539431821381335169 6663999404573866036001377)
    ·
      refine ⟨4997999553430399527001033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6663999404573866036001377 4997999553430399527001033)
      ·
        refine ⟨3748499665072799645250775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997999553430399527001033 3748499665072799645250775)
        ·
          refine ⟨5622749497609199467876163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748499665072799645250775 5622749497609199467876163)
          ·
            refine ⟨8434124246413799201814245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622749497609199467876163 8434124246413799201814245)
            ·
              refine ⟨1581398296202587350340171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8434124246413799201814245 1581398296202587350340171)
              ·
                refine ⟨2372097444303881025510257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581398296202587350340171 2372097444303881025510257)
                ·
                  refine ⟨1779073083227910769132693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372097444303881025510257 1779073083227910769132693)
                  ·
                    refine ⟨83394050776308317303095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1779073083227910769132693 83394050776308317303095)
                    ·
                      rfl

theorem cell23_487228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_487228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487228 prefixEnd_487228 := by exact prefixLift 487228
  have htrace : WordTrace (prefixWord ++ tailWord_487228) baseStart_487228 baseEnd_487228 := by
    simpa [prefixWord, tailWord_487228, baseEnd_487228] using wordTrace_append hprefix tailTrace_487228
  have hstable : (prefixWord ++ tailWord_487228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487228).length < 2 ^ (prefixWord ++ tailWord_487228).sum := by decide
  have hdescent : baseEnd_487228 < baseStart_487228 := by decide
  rcases family_descends (prefixWord ++ tailWord_487228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487255 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_487255 : Nat := 118140960795 + 487255 * 2 ^ 59
def prefixEnd_487255 : Nat := 4983230072969 + 3 ^ 40 * 487255 * 2
def baseEnd_487255 : Nat := 250196016306596346271661

theorem tailTrace_487255 : CollatzResearch.WordTrace tailWord_487255 prefixEnd_487255 250196016306596346271661 := by
  unfold tailWord_487255
  simp only [CollatzResearch.WordTrace]
  refine ⟨17771649849765826373903219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11847766566510550915935479 17771649849765826373903219)
  ·
    refine ⟨26657474774648739560854829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17771649849765826373903219 26657474774648739560854829)
    ·
      refine ⟨9996553040493277335320561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26657474774648739560854829 9996553040493277335320561)
      ·
        refine ⟨7497414780369958001490421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9996553040493277335320561 7497414780369958001490421)
        ·
          refine ⟨702882635659683562639727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7497414780369958001490421 702882635659683562639727)
          ·
            refine ⟨1054323953489525343959591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702882635659683562639727 1054323953489525343959591)
            ·
              refine ⟨1581485930234288015939387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054323953489525343959591 1581485930234288015939387)
              ·
                refine ⟨2372228895351432023909081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581485930234288015939387 2372228895351432023909081)
                ·
                  refine ⟨1779171671513574017931811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372228895351432023909081 1779171671513574017931811)
                  ·
                    refine ⟨2668757507270361026897717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779171671513574017931811 2668757507270361026897717)
                    ·
                      refine ⟨250196016306596346271661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2668757507270361026897717 250196016306596346271661)
                      ·
                        rfl

theorem cell23_487255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_487255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487255 prefixEnd_487255 := by exact prefixLift 487255
  have htrace : WordTrace (prefixWord ++ tailWord_487255) baseStart_487255 baseEnd_487255 := by
    simpa [prefixWord, tailWord_487255, baseEnd_487255] using wordTrace_append hprefix tailTrace_487255
  have hstable : (prefixWord ++ tailWord_487255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487255).length < 2 ^ (prefixWord ++ tailWord_487255).sum := by decide
  have hdescent : baseEnd_487255 < baseStart_487255 := by decide
  rcases family_descends (prefixWord ++ tailWord_487255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487285 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_487285 : Nat := 118140960795 + 487285 * 2 ^ 59
def prefixEnd_487285 : Nat := 4983230072969 + 3 ^ 40 * 487285 * 2
def baseEnd_487285 : Nat := 250211420726231228896523

theorem tailTrace_487285 : CollatzResearch.WordTrace tailWord_487285 prefixEnd_487285 250211420726231228896523 := by
  unfold tailWord_487285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772744039657141497495309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11848496026438094331663539 17772744039657141497495309)
  ·
    refine ⟨6664779014871428061560741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17772744039657141497495309 6664779014871428061560741)
    ·
      refine ⟨1249646065288392761542639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6664779014871428061560741 1249646065288392761542639)
      ·
        refine ⟨1874469097932589142313959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249646065288392761542639 1874469097932589142313959)
        ·
          refine ⟨2811703646898883713470939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874469097932589142313959 2811703646898883713470939)
          ·
            refine ⟨4217555470348325570206409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811703646898883713470939 4217555470348325570206409)
            ·
              refine ⟨3163166602761244177654807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217555470348325570206409 3163166602761244177654807)
              ·
                refine ⟨4744749904141866266482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163166602761244177654807 4744749904141866266482211)
                ·
                  refine ⟨7117124856212799399723317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744749904141866266482211 7117124856212799399723317)
                  ·
                    refine ⟨667230455269949943724061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7117124856212799399723317 667230455269949943724061)
                    ·
                      refine ⟨250211420726231228896523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667230455269949943724061 250211420726231228896523)
                      ·
                        rfl

theorem cell23_487285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_487285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487285 prefixEnd_487285 := by exact prefixLift 487285
  have htrace : WordTrace (prefixWord ++ tailWord_487285) baseStart_487285 baseEnd_487285 := by
    simpa [prefixWord, tailWord_487285, baseEnd_487285] using wordTrace_append hprefix tailTrace_487285
  have hstable : (prefixWord ++ tailWord_487285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487285).length < 2 ^ (prefixWord ++ tailWord_487285).sum := by decide
  have hdescent : baseEnd_487285 < baseStart_487285 := by decide
  rcases family_descends (prefixWord ++ tailWord_487285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487305 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_487305 : Nat := 118140960795 + 487305 * 2 ^ 59
def prefixEnd_487305 : Nat := 4983230072969 + 3 ^ 40 * 487305 * 2
def baseEnd_487305 : Nat := 83407230113107050215477

theorem tailTrace_487305 : CollatzResearch.WordTrace tailWord_487305 prefixEnd_487305 83407230113107050215477 := by
  unfold tailWord_487305
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773473499584684913223369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11848982333056456608815579 17773473499584684913223369)
  ·
    refine ⟨13330105124688513684917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17773473499584684913223369 13330105124688513684917527)
    ·
      refine ⟨19995157687032770527376291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13330105124688513684917527 19995157687032770527376291)
      ·
        refine ⟨29992736530549155791064437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19995157687032770527376291 29992736530549155791064437)
        ·
          refine ⟨2811819049738983355412291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29992736530549155791064437 2811819049738983355412291)
          ·
            refine ⟨4217728574608475033118437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811819049738983355412291 4217728574608475033118437)
            ·
              refine ⟨790824107739089068709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4217728574608475033118437 790824107739089068709707)
              ·
                refine ⟨1186236161608633603064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790824107739089068709707 1186236161608633603064561)
                ·
                  refine ⟨889677121206475202298421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186236161608633603064561 889677121206475202298421)
                  ·
                    refine ⟨83407230113107050215477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889677121206475202298421 83407230113107050215477)
                    ·
                      rfl

theorem cell23_487305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_487305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487305 prefixEnd_487305 := by exact prefixLift 487305
  have htrace : WordTrace (prefixWord ++ tailWord_487305) baseStart_487305 baseEnd_487305 := by
    simpa [prefixWord, tailWord_487305, baseEnd_487305] using wordTrace_append hprefix tailTrace_487305
  have hstable : (prefixWord ++ tailWord_487305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487305).length < 2 ^ (prefixWord ++ tailWord_487305).sum := by decide
  have hdescent : baseEnd_487305 < baseStart_487305 := by decide
  rcases family_descends (prefixWord ++ tailWord_487305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487326 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_487326 : Nat := 118140960795 + 487326 * 2 ^ 59
def prefixEnd_487326 : Nat := 4983230072969 + 3 ^ 40 * 487326 * 2
def baseEnd_487326 : Nat := 27803608159229507609315

theorem tailTrace_487326 : CollatzResearch.WordTrace tailWord_487326 prefixEnd_487326 27803608159229507609315 := by
  unfold tailWord_487326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221779929063575687467229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11849492955005736999825221 2221779929063575687467229)
  ·
    refine ⟨833167473398840882800211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2221779929063575687467229 833167473398840882800211)
    ·
      refine ⟨1249751210098261324200317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833167473398840882800211 1249751210098261324200317)
      ·
        refine ⟨468656703786847996575119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1249751210098261324200317 468656703786847996575119)
        ·
          refine ⟨702985055680271994862679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468656703786847996575119 702985055680271994862679)
          ·
            refine ⟨1054477583520407992294019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702985055680271994862679 1054477583520407992294019)
            ·
              refine ⟨1581716375280611988441029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054477583520407992294019 1581716375280611988441029)
              ·
                refine ⟨296571820365114747832693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1581716375280611988441029 296571820365114747832693)
                ·
                  refine ⟨27803608159229507609315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296571820365114747832693 27803608159229507609315)
                  ·
                    rfl

theorem cell23_487326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_487326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487326 prefixEnd_487326 := by exact prefixLift 487326
  have htrace : WordTrace (prefixWord ++ tailWord_487326) baseStart_487326 baseEnd_487326 := by
    simpa [prefixWord, tailWord_487326, baseEnd_487326] using wordTrace_append hprefix tailTrace_487326
  have hstable : (prefixWord ++ tailWord_487326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487326).length < 2 ^ (prefixWord ++ tailWord_487326).sum := by decide
  have hdescent : baseEnd_487326 < baseStart_487326 := by decide
  rcases family_descends (prefixWord ++ tailWord_487326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487328 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_487328 : Nat := 118140960795 + 487328 * 2 ^ 59
def prefixEnd_487328 : Nat := 4983230072969 + 3 ^ 40 * 487328 * 2
def baseEnd_487328 : Nat := 250233500394374560658825

theorem tailTrace_487328 : CollatzResearch.WordTrace tailWord_487328 prefixEnd_487328 250233500394374560658825 := by
  unfold tailWord_487328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887156189250679920655319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11849541585667573227540425 8887156189250679920655319)
  ·
    refine ⟨13330734283876019880982979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887156189250679920655319 13330734283876019880982979)
    ·
      refine ⟨19996101425814029821474469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13330734283876019880982979 19996101425814029821474469)
      ·
        refine ⟨3749269017340130591526463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19996101425814029821474469 3749269017340130591526463)
        ·
          refine ⟨5623903526010195887289695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749269017340130591526463 5623903526010195887289695)
          ·
            refine ⟨8435855289015293830934543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623903526010195887289695 8435855289015293830934543)
            ·
              refine ⟨12653782933522940746401815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435855289015293830934543 12653782933522940746401815)
              ·
                refine ⟨18980674400284411119602723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653782933522940746401815 18980674400284411119602723)
                ·
                  refine ⟨28471011600426616679404085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18980674400284411119602723 28471011600426616679404085)
                  ·
                    refine ⟨2669157337539995313694133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28471011600426616679404085 2669157337539995313694133)
                    ·
                      refine ⟨250233500394374560658825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2669157337539995313694133 250233500394374560658825)
                      ·
                        rfl

theorem cell23_487328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_487328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487328 prefixEnd_487328 := by exact prefixLift 487328
  have htrace : WordTrace (prefixWord ++ tailWord_487328) baseStart_487328 baseEnd_487328 := by
    simpa [prefixWord, tailWord_487328, baseEnd_487328] using wordTrace_append hprefix tailTrace_487328
  have hstable : (prefixWord ++ tailWord_487328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487328).length < 2 ^ (prefixWord ++ tailWord_487328).sum := by decide
  have hdescent : baseEnd_487328 < baseStart_487328 := by decide
  rcases family_descends (prefixWord ++ tailWord_487328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487356 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_487356 : Nat := 118140960795 + 487356 * 2 ^ 59
def prefixEnd_487356 : Nat := 4983230072969 + 3 ^ 40 * 487356 * 2
def baseEnd_487356 : Nat := 83415959284233483702899

theorem tailTrace_487356 : CollatzResearch.WordTrace tailWord_487356 prefixEnd_487356 83415959284233483702899 := by
  unfold tailWord_487356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887666811199960311664961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11850222414933280415553281 8887666811199960311664961)
  ·
    refine ⟨6665750108399970233748721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8887666811199960311664961 6665750108399970233748721)
    ·
      refine ⟨4999312581299977675311541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6665750108399970233748721 4999312581299977675311541)
      ·
        refine ⟨468685554496872907060457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4999312581299977675311541 468685554496872907060457)
        ·
          refine ⟨351514165872654680295343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468685554496872907060457 351514165872654680295343)
          ·
            refine ⟨527271248808982020443015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351514165872654680295343 527271248808982020443015)
            ·
              refine ⟨790906873213473030664523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527271248808982020443015 790906873213473030664523)
              ·
                refine ⟨1186360309820209545996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790906873213473030664523 1186360309820209545996785)
                ·
                  refine ⟨889770232365157159497589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186360309820209545996785 889770232365157159497589)
                  ·
                    refine ⟨83415959284233483702899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889770232365157159497589 83415959284233483702899)
                    ·
                      rfl

theorem cell23_487356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_487356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487356 prefixEnd_487356 := by exact prefixLift 487356
  have htrace : WordTrace (prefixWord ++ tailWord_487356) baseStart_487356 baseEnd_487356 := by
    simpa [prefixWord, tailWord_487356, baseEnd_487356] using wordTrace_append hprefix tailTrace_487356
  have hstable : (prefixWord ++ tailWord_487356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487356).length < 2 ^ (prefixWord ++ tailWord_487356).sum := by decide
  have hdescent : baseEnd_487356 < baseStart_487356 := by decide
  rcases family_descends (prefixWord ++ tailWord_487356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487399 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 6]
def baseStart_487399 : Nat := 118140960795 + 487399 * 2 ^ 59
def prefixEnd_487399 : Nat := 4983230072969 + 3 ^ 40 * 487399 * 2
def baseEnd_487399 : Nat := 27807773057871531430111

theorem tailTrace_487399 : CollatzResearch.WordTrace tailWord_487399 prefixEnd_487399 27807773057871531430111 := by
  unfold tailWord_487399
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776901961244138967145251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11851267974162759311430167 17776901961244138967145251)
  ·
    refine ⟨26665352941866208450717877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17776901961244138967145251 26665352941866208450717877)
    ·
      refine ⟨2499876838299957042254801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26665352941866208450717877 2499876838299957042254801)
      ·
        refine ⟨1874907628724967781691101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499876838299957042254801 1874907628724967781691101)
        ·
          refine ⟨703090360771862918134163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1874907628724967781691101 703090360771862918134163)
          ·
            refine ⟨1054635541157794377201245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703090360771862918134163 1054635541157794377201245)
            ·
              refine ⟨395488327934172891450467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054635541157794377201245 395488327934172891450467)
              ·
                refine ⟨593232491901259337175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395488327934172891450467 593232491901259337175701)
                ·
                  refine ⟨27807773057871531430111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593232491901259337175701 27807773057871531430111)
                  ·
                    rfl

theorem cell23_487399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 6].length) (baseStart_487399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487399 prefixEnd_487399 := by exact prefixLift 487399
  have htrace : WordTrace (prefixWord ++ tailWord_487399) baseStart_487399 baseEnd_487399 := by
    simpa [prefixWord, tailWord_487399, baseEnd_487399] using wordTrace_append hprefix tailTrace_487399
  have hstable : (prefixWord ++ tailWord_487399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487399).length < 2 ^ (prefixWord ++ tailWord_487399).sum := by decide
  have hdescent : baseEnd_487399 < baseStart_487399 := by decide
  rcases family_descends (prefixWord ++ tailWord_487399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487402 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_487402 : Nat := 118140960795 + 487402 * 2 ^ 59
def prefixEnd_487402 : Nat := 4983230072969 + 3 ^ 40 * 487402 * 2
def baseEnd_487402 : Nat := 250271497962807271133485

theorem tailTrace_487402 : CollatzResearch.WordTrace tailWord_487402 prefixEnd_487402 250271497962807271133485 := by
  unfold tailWord_487402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444252845058317619876115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11851340920155513653002973 4444252845058317619876115)
  ·
    refine ⟨6666379267587476429814173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444252845058317619876115 6666379267587476429814173)
    ·
      refine ⟨2499892225345303661180315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6666379267587476429814173 2499892225345303661180315)
      ·
        refine ⟨3749838338017955491770473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499892225345303661180315 3749838338017955491770473)
        ·
          refine ⟨2812378753513466618827855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749838338017955491770473 2812378753513466618827855)
          ·
            refine ⟨4218568130270199928241783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812378753513466618827855 4218568130270199928241783)
            ·
              refine ⟨6327852195405299892362675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218568130270199928241783 6327852195405299892362675)
              ·
                refine ⟨9491778293107949838544013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327852195405299892362675 9491778293107949838544013)
                ·
                  refine ⟨3559416859915481189454005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9491778293107949838544013 3559416859915481189454005)
                  ·
                    refine ⟨333695330617076361511313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3559416859915481189454005 333695330617076361511313)
                    ·
                      refine ⟨250271497962807271133485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333695330617076361511313 250271497962807271133485)
                      ·
                        rfl

theorem cell23_487402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_487402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487402 prefixEnd_487402 := by exact prefixLift 487402
  have htrace : WordTrace (prefixWord ++ tailWord_487402) baseStart_487402 baseEnd_487402 := by
    simpa [prefixWord, tailWord_487402, baseEnd_487402] using wordTrace_append hprefix tailTrace_487402
  have hstable : (prefixWord ++ tailWord_487402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487402).length < 2 ^ (prefixWord ++ tailWord_487402).sum := by decide
  have hdescent : baseEnd_487402 < baseStart_487402 := by decide
  rcases family_descends (prefixWord ++ tailWord_487402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487425 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_487425 : Nat := 118140960795 + 487425 * 2 ^ 59
def prefixEnd_487425 : Nat := 4983230072969 + 3 ^ 40 * 487425 * 2
def baseEnd_487425 : Nat := 83427769339286893715293

theorem tailTrace_487425 : CollatzResearch.WordTrace tailWord_487425 prefixEnd_487425 83427769339286893715293 := by
  unfold tailWord_487425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777850259149945407591729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11851900172766630271727819 17777850259149945407591729)
  ·
    refine ⟨13333387694362459055693797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17777850259149945407591729 13333387694362459055693797)
    ·
      refine ⟨2500010192692961072942587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13333387694362459055693797 2500010192692961072942587)
      ·
        refine ⟨3750015289039441609413881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500010192692961072942587 3750015289039441609413881)
        ·
          refine ⟨2812511466779581207060411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750015289039441609413881 2812511466779581207060411)
          ·
            refine ⟨4218767200169371810590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812511466779581207060411 4218767200169371810590617)
            ·
              refine ⟨3164075400127028857942963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218767200169371810590617 3164075400127028857942963)
              ·
                refine ⟨4746113100190543286914445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164075400127028857942963 4746113100190543286914445)
                ·
                  refine ⟨1779792412571453732592917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4746113100190543286914445 1779792412571453732592917)
                  ·
                    refine ⟨83427769339286893715293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1779792412571453732592917 83427769339286893715293)
                    ·
                      rfl

theorem cell23_487425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_487425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487425 prefixEnd_487425 := by exact prefixLift 487425
  have htrace : WordTrace (prefixWord ++ tailWord_487425) baseStart_487425 baseEnd_487425 := by
    simpa [prefixWord, tailWord_487425, baseEnd_487425] using wordTrace_append hprefix tailTrace_487425
  have hstable : (prefixWord ++ tailWord_487425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487425).length < 2 ^ (prefixWord ++ tailWord_487425).sum := by decide
  have hdescent : baseEnd_487425 < baseStart_487425 := by decide
  rcases family_descends (prefixWord ++ tailWord_487425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487430 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_487430 : Nat := 118140960795 + 487430 * 2 ^ 59
def prefixEnd_487430 : Nat := 4983230072969 + 3 ^ 40 * 487430 * 2
def baseEnd_487430 : Nat := 250285875421133161583357

theorem tailTrace_487430 : CollatzResearch.WordTrace tailWord_487430 prefixEnd_487430 250285875421133161583357 := by
  unfold tailWord_487430
  simp only [CollatzResearch.WordTrace]
  refine ⟨555563519504119726922617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11852021749421220841015829 555563519504119726922617)
  ·
    refine ⟨416672639628089795191963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 555563519504119726922617 416672639628089795191963)
    ·
      refine ⟨625008959442134692787945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416672639628089795191963 625008959442134692787945)
      ·
        refine ⟨468756719581601019590959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625008959442134692787945 468756719581601019590959)
        ·
          refine ⟨703135079372401529386439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468756719581601019590959 703135079372401529386439)
          ·
            refine ⟨1054702619058602294079659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703135079372401529386439 1054702619058602294079659)
            ·
              refine ⟨1582053928587903441119489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054702619058602294079659 1582053928587903441119489)
              ·
                refine ⟨1186540446440927580839617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582053928587903441119489 1186540446440927580839617)
                ·
                  refine ⟨889905334830695685629713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186540446440927580839617 889905334830695685629713)
                  ·
                    refine ⟨667429001123021764222285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 889905334830695685629713 667429001123021764222285)
                    ·
                      refine ⟨250285875421133161583357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667429001123021764222285 250285875421133161583357)
                      ·
                        rfl

theorem cell23_487430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_487430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487430 prefixEnd_487430 := by exact prefixLift 487430
  have htrace : WordTrace (prefixWord ++ tailWord_487430) baseStart_487430 baseEnd_487430 := by
    simpa [prefixWord, tailWord_487430, baseEnd_487430] using wordTrace_append hprefix tailTrace_487430
  have hstable : (prefixWord ++ tailWord_487430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487430).length < 2 ^ (prefixWord ++ tailWord_487430).sum := by decide
  have hdescent : baseEnd_487430 < baseStart_487430 := by decide
  rcases family_descends (prefixWord ++ tailWord_487430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487432 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_487432 : Nat := 118140960795 + 487432 * 2 ^ 59
def prefixEnd_487432 : Nat := 4983230072969 + 3 ^ 40 * 487432 * 2
def baseEnd_487432 : Nat := 250286902382442153758347

theorem tailTrace_487432 : CollatzResearch.WordTrace tailWord_487432 prefixEnd_487432 250286902382442153758347 := by
  unfold tailWord_487432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889052785062292801548275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11852070380083057068731033 8889052785062292801548275)
  ·
    refine ⟨13333579177593439202322413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8889052785062292801548275 13333579177593439202322413)
    ·
      refine ⟨5000092191597539700870905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13333579177593439202322413 5000092191597539700870905)
      ·
        refine ⟨3750069143698154775653179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000092191597539700870905 3750069143698154775653179)
        ·
          refine ⟨5625103715547232163479769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750069143698154775653179 5625103715547232163479769)
          ·
            refine ⟨4218827786660424122609827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625103715547232163479769 4218827786660424122609827)
            ·
              refine ⟨6328241679990636183914741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218827786660424122609827 6328241679990636183914741)
              ·
                refine ⟨593272657499122142242007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6328241679990636183914741 593272657499122142242007)
                ·
                  refine ⟨889908986248683213363011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593272657499122142242007 889908986248683213363011)
                  ·
                    refine ⟨1334863479373024820044517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 889908986248683213363011 1334863479373024820044517)
                    ·
                      refine ⟨250286902382442153758347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1334863479373024820044517 250286902382442153758347)
                      ·
                        rfl

theorem cell23_487432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_487432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487432 prefixEnd_487432 := by exact prefixLift 487432
  have htrace : WordTrace (prefixWord ++ tailWord_487432) baseStart_487432 baseEnd_487432 := by
    simpa [prefixWord, tailWord_487432, baseEnd_487432] using wordTrace_append hprefix tailTrace_487432
  have hstable : (prefixWord ++ tailWord_487432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487432).length < 2 ^ (prefixWord ++ tailWord_487432).sum := by decide
  have hdescent : baseEnd_487432 < baseStart_487432 := by decide
  rcases family_descends (prefixWord ++ tailWord_487432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487437 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_487437 : Nat := 118140960795 + 487437 * 2 ^ 59
def prefixEnd_487437 : Nat := 4983230072969 + 3 ^ 40 * 487437 * 2
def baseEnd_487437 : Nat := 83429823261904878065275

theorem tailTrace_487437 : CollatzResearch.WordTrace tailWord_487437 prefixEnd_487437 83429823261904878065275 := by
  unfold tailWord_487437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778287935106471457028565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852191956737647638019043 17778287935106471457028565)
  ·
    refine ⟨416678623479057924774107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17778287935106471457028565 416678623479057924774107)
    ·
      refine ⟨625017935218586887161161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416678623479057924774107 625017935218586887161161)
      ·
        refine ⟨468763451413940165370871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625017935218586887161161 468763451413940165370871)
        ·
          refine ⟨703145177120910248056307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468763451413940165370871 703145177120910248056307)
          ·
            refine ⟨1054717765681365372084461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703145177120910248056307 1054717765681365372084461)
            ·
              refine ⟨395519162130512014531673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054717765681365372084461 395519162130512014531673)
              ·
                refine ⟨296639371597884010898755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395519162130512014531673 296639371597884010898755)
                ·
                  refine ⟨444959057396826016348133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296639371597884010898755 444959057396826016348133)
                  ·
                    refine ⟨83429823261904878065275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444959057396826016348133 83429823261904878065275)
                    ·
                      rfl

theorem cell23_487437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_487437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487437 prefixEnd_487437 := by exact prefixLift 487437
  have htrace : WordTrace (prefixWord ++ tailWord_487437) baseStart_487437 baseEnd_487437 := by
    simpa [prefixWord, tailWord_487437, baseEnd_487437] using wordTrace_append hprefix tailTrace_487437
  have hstable : (prefixWord ++ tailWord_487437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487437).length < 2 ^ (prefixWord ++ tailWord_487437).sum := by decide
  have hdescent : baseEnd_487437 < baseStart_487437 := by decide
  rcases family_descends (prefixWord ++ tailWord_487437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487452 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_487452 : Nat := 118140960795 + 487452 * 2 ^ 59
def prefixEnd_487452 : Nat := 4983230072969 + 3 ^ 40 * 487452 * 2
def baseEnd_487452 : Nat := 250297171995532075508255

theorem tailTrace_487452 : CollatzResearch.WordTrace tailWord_487452 prefixEnd_487452 250297171995532075508255 := by
  unfold tailWord_487452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889417515026064509412305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11852556686701419345883073 8889417515026064509412305)
  ·
    refine ⟨6667063136269548382059229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8889417515026064509412305 6667063136269548382059229)
    ·
      refine ⟨2500148676101080643272211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6667063136269548382059229 2500148676101080643272211)
      ·
        refine ⟨3750223014151620964908317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500148676101080643272211 3750223014151620964908317)
        ·
          refine ⟨1406333630306857861840619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3750223014151620964908317 1406333630306857861840619)
          ·
            refine ⟨2109500445460286792760929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406333630306857861840619 2109500445460286792760929)
            ·
              refine ⟨1582125334095215094570697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109500445460286792760929 1582125334095215094570697)
              ·
                refine ⟨1186594000571411320928023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582125334095215094570697 1186594000571411320928023)
                ·
                  refine ⟨1779891000857116981392035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186594000571411320928023 1779891000857116981392035)
                  ·
                    refine ⟨2669836501285675472088053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779891000857116981392035 2669836501285675472088053)
                    ·
                      refine ⟨250297171995532075508255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2669836501285675472088053 250297171995532075508255)
                      ·
                        rfl

theorem cell23_487452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_487452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487452 prefixEnd_487452 := by exact prefixLift 487452
  have htrace : WordTrace (prefixWord ++ tailWord_487452) baseStart_487452 baseEnd_487452 := by
    simpa [prefixWord, tailWord_487452, baseEnd_487452] using wordTrace_append hprefix tailTrace_487452
  have hstable : (prefixWord ++ tailWord_487452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487452).length < 2 ^ (prefixWord ++ tailWord_487452).sum := by decide
  have hdescent : baseEnd_487452 < baseStart_487452 := by decide
  rcases family_descends (prefixWord ++ tailWord_487452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487455 : List Nat := [1, 1, 2, 4, 1, 2, 4, 8]
def baseStart_487455 : Nat := 118140960795 + 487455 * 2 ^ 59
def prefixEnd_487455 : Nat := 4983230072969 + 3 ^ 40 * 487455 * 2
def baseEnd_487455 : Nat := 9270322682870206065583

theorem tailTrace_487455 : CollatzResearch.WordTrace tailWord_487455 prefixEnd_487455 9270322682870206065583 := by
  unfold tailWord_487455
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778944449041260531183819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852629632694173687455879 17778944449041260531183819)
  ·
    refine ⟨26668416673561890796775729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17778944449041260531183819 26668416673561890796775729)
    ·
      refine ⟨20001312505171418097581797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26668416673561890796775729 20001312505171418097581797)
      ·
        refine ⟨3750246094719640893296587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20001312505171418097581797 3750246094719640893296587)
        ·
          refine ⟨5625369142079461339944881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750246094719640893296587 5625369142079461339944881)
          ·
            refine ⟨4219026856559596004958661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625369142079461339944881 4219026856559596004958661)
            ·
              refine ⟨791067535604924250929749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4219026856559596004958661 791067535604924250929749)
              ·
                refine ⟨9270322682870206065583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 791067535604924250929749 9270322682870206065583)
                ·
                  rfl

theorem cell23_487455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 8].length) (baseStart_487455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487455 prefixEnd_487455 := by exact prefixLift 487455
  have htrace : WordTrace (prefixWord ++ tailWord_487455) baseStart_487455 baseEnd_487455 := by
    simpa [prefixWord, tailWord_487455, baseEnd_487455] using wordTrace_append hprefix tailTrace_487455
  have hstable : (prefixWord ++ tailWord_487455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487455).length < 2 ^ (prefixWord ++ tailWord_487455).sum := by decide
  have hdescent : baseEnd_487455 < baseStart_487455 := by decide
  rcases family_descends (prefixWord ++ tailWord_487455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487463 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 1, 5]
def baseStart_487463 : Nat := 118140960795 + 487463 * 2 ^ 59
def prefixEnd_487463 : Nat := 4983230072969 + 3 ^ 40 * 487463 * 2
def baseEnd_487463 : Nat := 83434273427577177490235

theorem tailTrace_487463 : CollatzResearch.WordTrace tailWord_487463 prefixEnd_487463 83434273427577177490235 := by
  unfold tailWord_487463
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779236233012277897475043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852824155341518598316695 17779236233012277897475043)
  ·
    refine ⟨26668854349518416846212565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779236233012277897475043 26668854349518416846212565)
    ·
      refine ⟨625051273816837894833107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26668854349518416846212565 625051273816837894833107)
      ·
        refine ⟨937576910725256842249661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625051273816837894833107 937576910725256842249661)
        ·
          refine ⟨351591341521971315843623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937576910725256842249661 351591341521971315843623)
          ·
            refine ⟨527387012282956973765435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351591341521971315843623 527387012282956973765435)
            ·
              refine ⟨791080518424435460648153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527387012282956973765435 791080518424435460648153)
              ·
                refine ⟨593310388818326595486115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791080518424435460648153 593310388818326595486115)
                ·
                  refine ⟨889965583227489893229173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593310388818326595486115 889965583227489893229173)
                  ·
                    refine ⟨83434273427577177490235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889965583227489893229173 83434273427577177490235)
                    ·
                      rfl

theorem cell23_487463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_487463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487463 prefixEnd_487463 := by exact prefixLift 487463
  have htrace : WordTrace (prefixWord ++ tailWord_487463) baseStart_487463 baseEnd_487463 := by
    simpa [prefixWord, tailWord_487463, baseEnd_487463] using wordTrace_append hprefix tailTrace_487463
  have hstable : (prefixWord ++ tailWord_487463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487463).length < 2 ^ (prefixWord ++ tailWord_487463).sum := by decide
  have hdescent : baseEnd_487463 < baseStart_487463 := by decide
  rcases family_descends (prefixWord ++ tailWord_487463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487466 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_487466 : Nat := 118140960795 + 487466 * 2 ^ 59
def prefixEnd_487466 : Nat := 4983230072969 + 3 ^ 40 * 487466 * 2
def baseEnd_487466 : Nat := 250304360724695020733191

theorem tailTrace_487466 : CollatzResearch.WordTrace tailWord_487466 prefixEnd_487466 250304360724695020733191 := by
  unfold tailWord_487466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444836413000352352458563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11852897101334272939889501 4444836413000352352458563)
  ·
    refine ⟨6667254619500528528687845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444836413000352352458563 6667254619500528528687845)
    ·
      refine ⟨1250110241156349099128971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6667254619500528528687845 1250110241156349099128971)
      ·
        refine ⟨1875165361734523648693457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250110241156349099128971 1875165361734523648693457)
        ·
          refine ⟨1406374021300892736520093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875165361734523648693457 1406374021300892736520093)
          ·
            refine ⟨527390257987834776195035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1406374021300892736520093 527390257987834776195035)
            ·
              refine ⟨791085386981752164292553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527390257987834776195035 791085386981752164292553)
              ·
                refine ⟨593314040236314123219415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791085386981752164292553 593314040236314123219415)
                ·
                  refine ⟨889971060354471184829123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593314040236314123219415 889971060354471184829123)
                  ·
                    refine ⟨1334956590531706777243685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 889971060354471184829123 1334956590531706777243685)
                    ·
                      refine ⟨250304360724695020733191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1334956590531706777243685 250304360724695020733191)
                      ·
                        rfl

theorem cell23_487466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_487466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487466 prefixEnd_487466 := by exact prefixLift 487466
  have htrace : WordTrace (prefixWord ++ tailWord_487466) baseStart_487466 baseEnd_487466 := by
    simpa [prefixWord, tailWord_487466, baseEnd_487466] using wordTrace_append hprefix tailTrace_487466
  have hstable : (prefixWord ++ tailWord_487466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487466).length < 2 ^ (prefixWord ++ tailWord_487466).sum := by decide
  have hdescent : baseEnd_487466 < baseStart_487466 := by decide
  rcases family_descends (prefixWord ++ tailWord_487466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487486 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_487486 : Nat := 118140960795 + 487486 * 2 ^ 59
def prefixEnd_487486 : Nat := 4983230072969 + 3 ^ 40 * 487486 * 2
def baseEnd_487486 : Nat := 250314630337784942483099

theorem tailTrace_487486 : CollatzResearch.WordTrace tailWord_487486 prefixEnd_487486 250314630337784942483099 := by
  unfold tailWord_487486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222509388991119103195289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11853383407952635217041541 2222509388991119103195289)
  ·
    refine ⟨1666882041743339327396467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222509388991119103195289 1666882041743339327396467)
    ·
      refine ⟨2500323062615008991094701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666882041743339327396467 2500323062615008991094701)
      ·
        refine ⟨937621148480628371660513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2500323062615008991094701 937621148480628371660513)
        ·
          refine ⟨703215861360471278745385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937621148480628371660513 703215861360471278745385)
          ·
            refine ⟨527411896020353459059039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703215861360471278745385 527411896020353459059039)
            ·
              refine ⟨791117844030530188588559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527411896020353459059039 791117844030530188588559)
              ·
                refine ⟨1186676766045795282882839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791117844030530188588559 1186676766045795282882839)
                ·
                  refine ⟨1780015149068692924324259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186676766045795282882839 1780015149068692924324259)
                  ·
                    refine ⟨2670022723603039386486389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1780015149068692924324259 2670022723603039386486389)
                    ·
                      refine ⟨250314630337784942483099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2670022723603039386486389 250314630337784942483099)
                      ·
                        rfl

theorem cell23_487486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_487486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487486 prefixEnd_487486 := by exact prefixLift 487486
  have htrace : WordTrace (prefixWord ++ tailWord_487486) baseStart_487486 baseEnd_487486 := by
    simpa [prefixWord, tailWord_487486, baseEnd_487486] using wordTrace_append hprefix tailTrace_487486
  have hstable : (prefixWord ++ tailWord_487486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487486).length < 2 ^ (prefixWord ++ tailWord_487486).sum := by decide
  have hdescent : baseEnd_487486 < baseStart_487486 := by decide
  rcases family_descends (prefixWord ++ tailWord_487486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487509 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_487509 : Nat := 118140960795 + 487509 * 2 ^ 59
def prefixEnd_487509 : Nat := 4983230072969 + 3 ^ 40 * 487509 * 2
def baseEnd_487509 : Nat := 250326440392838352495493

theorem tailTrace_487509 : CollatzResearch.WordTrace tailWord_487509 prefixEnd_487509 250326440392838352495493 := by
  unfold tailWord_487509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780913990845627753649581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11853942660563751835766387 17780913990845627753649581)
  ·
    refine ⟨6667842746567110407618593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17780913990845627753649581 6667842746567110407618593)
    ·
      refine ⟨5000882059925332805713945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6667842746567110407618593 5000882059925332805713945)
      ·
        refine ⟨3750661544943999604285459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000882059925332805713945 3750661544943999604285459)
        ·
          refine ⟨5625992317415999406428189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750661544943999604285459 5625992317415999406428189)
          ·
            refine ⟨2109747119030999777410571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5625992317415999406428189 2109747119030999777410571)
            ·
              refine ⟨3164620678546499666115857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109747119030999777410571 3164620678546499666115857)
              ·
                refine ⟨2373465508909874749586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164620678546499666115857 2373465508909874749586893)
                ·
                  refine ⟨890049565841203031095085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2373465508909874749586893 890049565841203031095085)
                  ·
                    refine ⟨333768587190451136660657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890049565841203031095085 333768587190451136660657)
                    ·
                      refine ⟨250326440392838352495493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333768587190451136660657 250326440392838352495493)
                      ·
                        rfl

theorem cell23_487509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_487509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487509 prefixEnd_487509 := by exact prefixLift 487509
  have htrace : WordTrace (prefixWord ++ tailWord_487509) baseStart_487509 baseEnd_487509 := by
    simpa [prefixWord, tailWord_487509, baseEnd_487509] using wordTrace_append hprefix tailTrace_487509
  have hstable : (prefixWord ++ tailWord_487509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487509).length < 2 ^ (prefixWord ++ tailWord_487509).sum := by decide
  have hdescent : baseEnd_487509 < baseStart_487509 := by decide
  rcases family_descends (prefixWord ++ tailWord_487509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487516 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_487516 : Nat := 118140960795 + 487516 * 2 ^ 59
def prefixEnd_487516 : Nat := 4983230072969 + 3 ^ 40 * 487516 * 2
def baseEnd_487516 : Nat := 250330034757419825107961

theorem tailTrace_487516 : CollatzResearch.WordTrace tailWord_487516 prefixEnd_487516 250330034757419825107961 := by
  unfold tailWord_487516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890584650910133974577201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11854112867880178632769601 8890584650910133974577201)
  ·
    refine ⟨6667938488182600480932901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8890584650910133974577201 6667938488182600480932901)
    ·
      refine ⟨1250238466534237590174919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6667938488182600480932901 1250238466534237590174919)
      ·
        refine ⟨1875357699801356385262379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250238466534237590174919 1875357699801356385262379)
        ·
          refine ⟨2813036549702034577893569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875357699801356385262379 2813036549702034577893569)
          ·
            refine ⟨2109777412276525933420177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813036549702034577893569 2109777412276525933420177)
            ·
              refine ⟨1582333059207394450065133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109777412276525933420177 1582333059207394450065133)
              ·
                refine ⟨593374897202772918774425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582333059207394450065133 593374897202772918774425)
                ·
                  refine ⟨445031172902079689080819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593374897202772918774425 445031172902079689080819)
                  ·
                    refine ⟨667546759353119533621229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445031172902079689080819 667546759353119533621229)
                    ·
                      refine ⟨250330034757419825107961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667546759353119533621229 250330034757419825107961)
                      ·
                        rfl

theorem cell23_487516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_487516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487516 prefixEnd_487516 := by exact prefixLift 487516
  have htrace : WordTrace (prefixWord ++ tailWord_487516) baseStart_487516 baseEnd_487516 := by
    simpa [prefixWord, tailWord_487516, baseEnd_487516] using wordTrace_append hprefix tailTrace_487516
  have hstable : (prefixWord ++ tailWord_487516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487516).length < 2 ^ (prefixWord ++ tailWord_487516).sum := by decide
  have hdescent : baseEnd_487516 < baseStart_487516 := by decide
  rcases family_descends (prefixWord ++ tailWord_487516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487543 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_487543 : Nat := 118140960795 + 487543 * 2 ^ 59
def prefixEnd_487543 : Nat := 4983230072969 + 3 ^ 40 * 487543 * 2
def baseEnd_487543 : Nat := 250343898735091219470337

theorem tailTrace_487543 : CollatzResearch.WordTrace tailWord_487543 prefixEnd_487543 250343898735091219470337 := by
  unfold tailWord_487543
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782154072722451560387283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11854769381814967706924855 17782154072722451560387283)
  ·
    refine ⟨26673231109083677340580925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17782154072722451560387283 26673231109083677340580925)
    ·
      refine ⟨10002461665906379002717847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26673231109083677340580925 10002461665906379002717847)
      ·
        refine ⟨15003692498859568504076771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10002461665906379002717847 15003692498859568504076771)
        ·
          refine ⟨22505538748289352756115157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15003692498859568504076771 22505538748289352756115157)
          ·
            refine ⟨527473564413031705221449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22505538748289352756115157 527473564413031705221449)
            ·
              refine ⟨395605173309773778916087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527473564413031705221449 395605173309773778916087)
              ·
                refine ⟨593407759964660668374131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395605173309773778916087 593407759964660668374131)
                ·
                  refine ⟨890111639946991002561197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593407759964660668374131 890111639946991002561197)
                  ·
                    refine ⟨333791864980121625960449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890111639946991002561197 333791864980121625960449)
                    ·
                      refine ⟨250343898735091219470337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333791864980121625960449 250343898735091219470337)
                      ·
                        rfl

theorem cell23_487543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_487543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487543 prefixEnd_487543 := by exact prefixLift 487543
  have htrace : WordTrace (prefixWord ++ tailWord_487543) baseStart_487543 baseEnd_487543 := by
    simpa [prefixWord, tailWord_487543, baseEnd_487543] using wordTrace_append hprefix tailTrace_487543
  have hstable : (prefixWord ++ tailWord_487543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487543).length < 2 ^ (prefixWord ++ tailWord_487543).sum := by decide
  have hdescent : baseEnd_487543 < baseStart_487543 := by decide
  rcases family_descends (prefixWord ++ tailWord_487543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487556 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_487556 : Nat := 118140960795 + 487556 * 2 ^ 59
def prefixEnd_487556 : Nat := 4983230072969 + 3 ^ 40 * 487556 * 2
def baseEnd_487556 : Nat := 250350573983599668607777

theorem tailTrace_487556 : CollatzResearch.WordTrace tailWord_487556 prefixEnd_487556 250350573983599668607777 := by
  unfold tailWord_487556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891314110837677390305261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11855085481116903187073681 8891314110837677390305261)
  ·
    refine ⟨3334242791564129021364473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8891314110837677390305261 3334242791564129021364473)
    ·
      refine ⟨2500682093673096766023355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334242791564129021364473 2500682093673096766023355)
      ·
        refine ⟨3751023140509645149035033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500682093673096766023355 3751023140509645149035033)
        ·
          refine ⟨2813267355382233861776275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751023140509645149035033 2813267355382233861776275)
          ·
            refine ⟨4219901033073350792664413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813267355382233861776275 4219901033073350792664413)
            ·
              refine ⟨1582462887402506547249155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219901033073350792664413 1582462887402506547249155)
              ·
                refine ⟨2373694331103759820873733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582462887402506547249155 2373694331103759820873733)
                ·
                  refine ⟨445067687081954966413825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373694331103759820873733 445067687081954966413825)
                  ·
                    refine ⟨333800765311466224810369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445067687081954966413825 333800765311466224810369)
                    ·
                      refine ⟨250350573983599668607777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333800765311466224810369 250350573983599668607777)
                      ·
                        rfl

theorem cell23_487556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_487556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487556 prefixEnd_487556 := by exact prefixLift 487556
  have htrace : WordTrace (prefixWord ++ tailWord_487556) baseStart_487556 baseEnd_487556 := by
    simpa [prefixWord, tailWord_487556, baseEnd_487556] using wordTrace_append hprefix tailTrace_487556
  have hstable : (prefixWord ++ tailWord_487556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487556).length < 2 ^ (prefixWord ++ tailWord_487556).sum := by decide
  have hdescent : baseEnd_487556 < baseStart_487556 := by decide
  rcases family_descends (prefixWord ++ tailWord_487556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487562 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_487562 : Nat := 118140960795 + 487562 * 2 ^ 59
def prefixEnd_487562 : Nat := 4983230072969 + 3 ^ 40 * 487562 * 2
def baseEnd_487562 : Nat := 27817072763058516125861

theorem tailTrace_487562 : CollatzResearch.WordTrace tailWord_487562 prefixEnd_487562 27817072763058516125861 := by
  unfold tailWord_487562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445711764913404451332235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11855231373102411870219293 4445711764913404451332235)
  ·
    refine ⟨6668567647370106676998353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4445711764913404451332235 6668567647370106676998353)
    ·
      refine ⟨5001425735527580007748765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6668567647370106676998353 5001425735527580007748765)
      ·
        refine ⟨1875534650822842502905787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5001425735527580007748765 1875534650822842502905787)
        ·
          refine ⟨2813301976234263754358681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875534650822842502905787 2813301976234263754358681)
          ·
            refine ⟨2109976482175697815769011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813301976234263754358681 2109976482175697815769011)
            ·
              refine ⟨3164964723263546723653517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109976482175697815769011 3164964723263546723653517)
              ·
                refine ⟨1186861771223830021370069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3164964723263546723653517 1186861771223830021370069)
                ·
                  refine ⟨27817072763058516125861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1186861771223830021370069 27817072763058516125861)
                  ·
                    rfl

theorem cell23_487562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_487562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487562 prefixEnd_487562 := by exact prefixLift 487562
  have htrace : WordTrace (prefixWord ++ tailWord_487562) baseStart_487562 baseEnd_487562 := by
    simpa [prefixWord, tailWord_487562, baseEnd_487562] using wordTrace_append hprefix tailTrace_487562
  have hstable : (prefixWord ++ tailWord_487562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487562).length < 2 ^ (prefixWord ++ tailWord_487562).sum := by decide
  have hdescent : baseEnd_487562 < baseStart_487562 := by decide
  rcases family_descends (prefixWord ++ tailWord_487562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487573 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_487573 : Nat := 118140960795 + 487573 * 2 ^ 59
def prefixEnd_487573 : Nat := 4983230072969 + 3 ^ 40 * 487573 * 2
def baseEnd_487573 : Nat := 250359303154726102095199

theorem tailTrace_487573 : CollatzResearch.WordTrace tailWord_487573 prefixEnd_487573 250359303154726102095199 := by
  unfold tailWord_487573
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783248262613766683979373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855498841742511122652915 17783248262613766683979373)
  ·
    refine ⟨6668718098480162506492265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17783248262613766683979373 6668718098480162506492265)
    ·
      refine ⟨5001538573860121879869199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6668718098480162506492265 5001538573860121879869199)
      ·
        refine ⟨7502307860790182819803799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001538573860121879869199 7502307860790182819803799)
        ·
          refine ⟨11253461791185274229705699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502307860790182819803799 11253461791185274229705699)
          ·
            refine ⟨16880192686777911344558549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253461791185274229705699 16880192686777911344558549)
            ·
              refine ⟨395629516096357297138091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16880192686777911344558549 395629516096357297138091)
              ·
                refine ⟨593444274144535945707137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395629516096357297138091 593444274144535945707137)
                ·
                  refine ⟨445083205608401959280353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593444274144535945707137 445083205608401959280353)
                  ·
                    refine ⟨333812404206301469460265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445083205608401959280353 333812404206301469460265)
                    ·
                      refine ⟨250359303154726102095199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 333812404206301469460265 250359303154726102095199)
                      ·
                        rfl

theorem cell23_487573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_487573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487573 prefixEnd_487573 := by exact prefixLift 487573
  have htrace : WordTrace (prefixWord ++ tailWord_487573) baseStart_487573 baseEnd_487573 := by
    simpa [prefixWord, tailWord_487573, baseEnd_487573] using wordTrace_append hprefix tailTrace_487573
  have hstable : (prefixWord ++ tailWord_487573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487573).length < 2 ^ (prefixWord ++ tailWord_487573).sum := by decide
  have hdescent : baseEnd_487573 < baseStart_487573 := by decide
  rcases family_descends (prefixWord ++ tailWord_487573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487595 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_487595 : Nat := 118140960795 + 487595 * 2 ^ 59
def prefixEnd_487595 : Nat := 4983230072969 + 3 ^ 40 * 487595 * 2
def baseEnd_487595 : Nat := 250370599729125016020097

theorem tailTrace_487595 : CollatzResearch.WordTrace tailWord_487595 prefixEnd_487595 250370599729125016020097 := by
  unfold tailWord_487595
  simp only [CollatzResearch.WordTrace]
  refine ⟨17784050668534064441280239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11856033779022709627520159 17784050668534064441280239)
  ·
    refine ⟨26676076002801096661920359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17784050668534064441280239 26676076002801096661920359)
    ·
      refine ⟨40014114004201644992880539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26676076002801096661920359 40014114004201644992880539)
      ·
        refine ⟨60021171006302467489320809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40014114004201644992880539 60021171006302467489320809)
        ·
          refine ⟨45015878254726850616990607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60021171006302467489320809 45015878254726850616990607)
          ·
            refine ⟨67523817382090275925485911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45015878254726850616990607 67523817382090275925485911)
            ·
              refine ⟨101285726073135413888228867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67523817382090275925485911 101285726073135413888228867)
              ·
                refine ⟨151928589109703120832343301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101285726073135413888228867 151928589109703120832343301)
                ·
                  refine ⟨28486610458069335156064369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151928589109703120832343301 28486610458069335156064369)
                  ·
                    refine ⟨21364957843552001367048277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28486610458069335156064369 21364957843552001367048277)
                    ·
                      refine ⟨250370599729125016020097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21364957843552001367048277 250370599729125016020097)
                      ·
                        rfl

theorem cell23_487595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_487595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487595 prefixEnd_487595 := by exact prefixLift 487595
  have htrace : WordTrace (prefixWord ++ tailWord_487595) baseStart_487595 baseEnd_487595 := by
    simpa [prefixWord, tailWord_487595, baseEnd_487595] using wordTrace_append hprefix tailTrace_487595
  have hstable : (prefixWord ++ tailWord_487595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487595).length < 2 ^ (prefixWord ++ tailWord_487595).sum := by decide
  have hdescent : baseEnd_487595 < baseStart_487595 := by decide
  rcases family_descends (prefixWord ++ tailWord_487595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487602 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_487602 : Nat := 118140960795 + 487602 * 2 ^ 59
def prefixEnd_487602 : Nat := 4983230072969 + 3 ^ 40 * 487602 * 2
def baseEnd_487602 : Nat := 250374194093706488632565

theorem tailTrace_487602 : CollatzResearch.WordTrace tailWord_487602 prefixEnd_487602 250374194093706488632565 := by
  unfold tailWord_487602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446076494877176159196265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11856203986339136424523373 4446076494877176159196265)
  ·
    refine ⟨3334557371157882119397199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446076494877176159196265 3334557371157882119397199)
    ·
      refine ⟨5001836056736823179095799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334557371157882119397199 5001836056736823179095799)
      ·
        refine ⟨7502754085105234768643699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001836056736823179095799 7502754085105234768643699)
        ·
          refine ⟨11254131127657852152965549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502754085105234768643699 11254131127657852152965549)
          ·
            refine ⟨4220299172871694557362081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11254131127657852152965549 4220299172871694557362081)
            ·
              refine ⟨3165224379653770918021561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220299172871694557362081 3165224379653770918021561)
              ·
                refine ⟨2373918284740328188516171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165224379653770918021561 2373918284740328188516171)
                ·
                  refine ⟨3560877427110492282774257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373918284740328188516171 3560877427110492282774257)
                  ·
                    refine ⟨2670658070332869212080693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560877427110492282774257 2670658070332869212080693)
                    ·
                      refine ⟨250374194093706488632565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2670658070332869212080693 250374194093706488632565)
                      ·
                        rfl

theorem cell23_487602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_487602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487602 prefixEnd_487602 := by exact prefixLift 487602
  have htrace : WordTrace (prefixWord ++ tailWord_487602) baseStart_487602 baseEnd_487602 := by
    simpa [prefixWord, tailWord_487602, baseEnd_487602] using wordTrace_append hprefix tailTrace_487602
  have hstable : (prefixWord ++ tailWord_487602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487602).length < 2 ^ (prefixWord ++ tailWord_487602).sum := by decide
  have hdescent : baseEnd_487602 < baseStart_487602 := by decide
  rcases family_descends (prefixWord ++ tailWord_487602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487642 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_487642 : Nat := 118140960795 + 487642 * 2 ^ 59
def prefixEnd_487642 : Nat := 4983230072969 + 3 ^ 40 * 487642 * 2
def baseEnd_487642 : Nat := 250394733319886332132381

theorem tailTrace_487642 : CollatzResearch.WordTrace tailWord_487642 prefixEnd_487642 250394733319886332132381 := by
  unfold tailWord_487642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446441224840947867060295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11857176599575860978827453 4446441224840947867060295)
  ·
    refine ⟨6669661837261421800590443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446441224840947867060295 6669661837261421800590443)
    ·
      refine ⟨10004492755892132700885665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669661837261421800590443 10004492755892132700885665)
      ·
        refine ⟨7503369566919099525664249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10004492755892132700885665 7503369566919099525664249)
        ·
          refine ⟨5627527175189324644248187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7503369566919099525664249 5627527175189324644248187)
          ·
            refine ⟨8441290762783986966372281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627527175189324644248187 8441290762783986966372281)
            ·
              refine ⟨6330968072087990224779211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441290762783986966372281 6330968072087990224779211)
              ·
                refine ⟨9496452108131985337168817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330968072087990224779211 9496452108131985337168817)
                ·
                  refine ⟨7122339081098989002876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496452108131985337168817 7122339081098989002876613)
                  ·
                    refine ⟨1335438577706060438039365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122339081098989002876613 1335438577706060438039365)
                    ·
                      refine ⟨250394733319886332132381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1335438577706060438039365 250394733319886332132381)
                      ·
                        rfl

theorem cell23_487642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_487642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487642 prefixEnd_487642 := by exact prefixLift 487642
  have htrace : WordTrace (prefixWord ++ tailWord_487642) baseStart_487642 baseEnd_487642 := by
    simpa [prefixWord, tailWord_487642, baseEnd_487642] using wordTrace_append hprefix tailTrace_487642
  have hstable : (prefixWord ++ tailWord_487642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487642).length < 2 ^ (prefixWord ++ tailWord_487642).sum := by decide
  have hdescent : baseEnd_487642 < baseStart_487642 := by decide
  rcases family_descends (prefixWord ++ tailWord_487642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487666 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_487666 : Nat := 118140960795 + 487666 * 2 ^ 59
def prefixEnd_487666 : Nat := 4983230072969 + 3 ^ 40 * 487666 * 2
def baseEnd_487666 : Nat := 250407056855594238232271

theorem tailTrace_487666 : CollatzResearch.WordTrace tailWord_487666 prefixEnd_487666 250407056855594238232271 := by
  unfold tailWord_487666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446660062819210891778713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11857760167517895711409901 4446660062819210891778713)
  ·
    refine ⟨3334995047114408168834035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446660062819210891778713 3334995047114408168834035)
    ·
      refine ⟨5002492570671612253251053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334995047114408168834035 5002492570671612253251053)
      ·
        refine ⟨1875934714001854594969145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5002492570671612253251053 1875934714001854594969145)
        ·
          refine ⟨1406951035501390946226859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875934714001854594969145 1406951035501390946226859)
          ·
            refine ⟨2110426553252086419340289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406951035501390946226859 2110426553252086419340289)
            ·
              refine ⟨1582819914939064814505217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110426553252086419340289 1582819914939064814505217)
              ·
                refine ⟨1187114936204298610878913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582819914939064814505217 1187114936204298610878913)
                ·
                  refine ⟨890336202153223958159185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187114936204298610878913 890336202153223958159185)
                  ·
                    refine ⟨667752151614917968619389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890336202153223958159185 667752151614917968619389)
                    ·
                      refine ⟨250407056855594238232271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667752151614917968619389 250407056855594238232271)
                      ·
                        rfl

theorem cell23_487666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_487666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487666 prefixEnd_487666 := by exact prefixLift 487666
  have htrace : WordTrace (prefixWord ++ tailWord_487666) baseStart_487666 baseEnd_487666 := by
    simpa [prefixWord, tailWord_487666, baseEnd_487666] using wordTrace_append hprefix tailTrace_487666
  have hstable : (prefixWord ++ tailWord_487666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487666).length < 2 ^ (prefixWord ++ tailWord_487666).sum := by decide
  have hdescent : baseEnd_487666 < baseStart_487666 := by decide
  rcases family_descends (prefixWord ++ tailWord_487666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487692 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_487692 : Nat := 118140960795 + 487692 * 2 ^ 59
def prefixEnd_487692 : Nat := 4983230072969 + 3 ^ 40 * 487692 * 2
def baseEnd_487692 : Nat := 250420407352611136507151

theorem tailTrace_487692 : CollatzResearch.WordTrace tailWord_487692 prefixEnd_487692 250420407352611136507151 := by
  unfold tailWord_487692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893794274591325003780665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11858392366121766671707553 8893794274591325003780665)
  ·
    refine ⟨6670345705943493752835499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8893794274591325003780665 6670345705943493752835499)
    ·
      refine ⟨10005518558915240629253249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670345705943493752835499 10005518558915240629253249)
      ·
        refine ⟨7504138919186430471939937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10005518558915240629253249 7504138919186430471939937)
        ·
          refine ⟨5628104189389822853954953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504138919186430471939937 5628104189389822853954953)
          ·
            refine ⟨4221078142042367140466215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5628104189389822853954953 4221078142042367140466215)
            ·
              refine ⟨6331617213063550710699323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221078142042367140466215 6331617213063550710699323)
              ·
                refine ⟨9497425819595326066048985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331617213063550710699323 9497425819595326066048985)
                ·
                  refine ⟨7123069364696494549536739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497425819595326066048985 7123069364696494549536739)
                  ·
                    refine ⟨10684604047044741824305109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123069364696494549536739 10684604047044741824305109)
                    ·
                      refine ⟨250420407352611136507151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10684604047044741824305109 250420407352611136507151)
                      ·
                        rfl

theorem cell23_487692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_487692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487692 prefixEnd_487692 := by exact prefixLift 487692
  have htrace : WordTrace (prefixWord ++ tailWord_487692) baseStart_487692 baseEnd_487692 := by
    simpa [prefixWord, tailWord_487692, baseEnd_487692] using wordTrace_append hprefix tailTrace_487692
  have hstable : (prefixWord ++ tailWord_487692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487692).length < 2 ^ (prefixWord ++ tailWord_487692).sum := by decide
  have hdescent : baseEnd_487692 < baseStart_487692 := by decide
  rcases family_descends (prefixWord ++ tailWord_487692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487713 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_487713 : Nat := 118140960795 + 487713 * 2 ^ 59
def prefixEnd_487713 : Nat := 4983230072969 + 3 ^ 40 * 487713 * 2
def baseEnd_487713 : Nat := 250431190446355554344555

theorem tailTrace_487713 : CollatzResearch.WordTrace tailWord_487713 prefixEnd_487713 250431190446355554344555 := by
  unfold tailWord_487713
  simp only [CollatzResearch.WordTrace]
  refine ⟨17788354482106570594075793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11858902988071047062717195 17788354482106570594075793)
  ·
    refine ⟨13341265861579927945556845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17788354482106570594075793 13341265861579927945556845)
    ·
      refine ⟨5002974698092472979583817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13341265861579927945556845 5002974698092472979583817)
      ·
        refine ⟨3752231023569354734687863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5002974698092472979583817 3752231023569354734687863)
        ·
          refine ⟨5628346535354032102031795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752231023569354734687863 5628346535354032102031795)
          ·
            refine ⟨8442519803031048153047693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628346535354032102031795 8442519803031048153047693)
            ·
              refine ⟨3165944926136643057392885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8442519803031048153047693 3165944926136643057392885)
              ·
                refine ⟨296807336825310286630583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3165944926136643057392885 296807336825310286630583)
                ·
                  refine ⟨445211005237965429945875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296807336825310286630583 445211005237965429945875)
                  ·
                    refine ⟨667816507856948144918813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445211005237965429945875 667816507856948144918813)
                    ·
                      refine ⟨250431190446355554344555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667816507856948144918813 250431190446355554344555)
                      ·
                        rfl

theorem cell23_487713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_487713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487713 prefixEnd_487713 := by exact prefixLift 487713
  have htrace : WordTrace (prefixWord ++ tailWord_487713) baseStart_487713 baseEnd_487713 := by
    simpa [prefixWord, tailWord_487713, baseEnd_487713] using wordTrace_append hprefix tailTrace_487713
  have hstable : (prefixWord ++ tailWord_487713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487713).length < 2 ^ (prefixWord ++ tailWord_487713).sum := by decide
  have hdescent : baseEnd_487713 < baseStart_487713 := by decide
  rcases family_descends (prefixWord ++ tailWord_487713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487716 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_487716 : Nat := 118140960795 + 487716 * 2 ^ 59
def prefixEnd_487716 : Nat := 4983230072969 + 3 ^ 40 * 487716 * 2
def baseEnd_487716 : Nat := 83477576962773014202347

theorem tailTrace_487716 : CollatzResearch.WordTrace tailWord_487716 prefixEnd_487716 83477576962773014202347 := by
  unfold tailWord_487716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894231950547851053217501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11858975934063801404290001 8894231950547851053217501)
  ·
    refine ⟨3335336981455444144956563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8894231950547851053217501 3335336981455444144956563)
    ·
      refine ⟨5003005472183166217434845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335336981455444144956563 5003005472183166217434845)
      ·
        refine ⟨1876127052068687331538067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5003005472183166217434845 1876127052068687331538067)
        ·
          refine ⟨2814190578103030997307101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876127052068687331538067 2814190578103030997307101)
          ·
            refine ⟨1055321466788636623990163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2814190578103030997307101 1055321466788636623990163)
            ·
              refine ⟨1582982200182954935985245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055321466788636623990163 1582982200182954935985245)
              ·
                refine ⟨593618325068608100994467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582982200182954935985245 593618325068608100994467)
                ·
                  refine ⟨890427487602912151491701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593618325068608100994467 890427487602912151491701)
                  ·
                    refine ⟨83477576962773014202347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 890427487602912151491701 83477576962773014202347)
                    ·
                      rfl

theorem cell23_487716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_487716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487716 prefixEnd_487716 := by exact prefixLift 487716
  have htrace : WordTrace (prefixWord ++ tailWord_487716) baseStart_487716 baseEnd_487716 := by
    simpa [prefixWord, tailWord_487716, baseEnd_487716] using wordTrace_append hprefix tailTrace_487716
  have hstable : (prefixWord ++ tailWord_487716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487716).length < 2 ^ (prefixWord ++ tailWord_487716).sum := by decide
  have hdescent : baseEnd_487716 < baseStart_487716 := by decide
  rcases family_descends (prefixWord ++ tailWord_487716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487769 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_487769 : Nat := 118140960795 + 487769 * 2 ^ 59
def prefixEnd_487769 : Nat := 4983230072969 + 3 ^ 40 * 487769 * 2
def baseEnd_487769 : Nat := 250459945363007335244297

theorem tailTrace_487769 : CollatzResearch.WordTrace tailWord_487769 prefixEnd_487769 250459945363007335244297 := by
  unfold tailWord_487769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17790396969903692158114361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11860264646602461438742907 17790396969903692158114361)
  ·
    refine ⟨13342797727427769118585771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17790396969903692158114361 13342797727427769118585771)
    ·
      refine ⟨20014196591141653677878657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342797727427769118585771 20014196591141653677878657)
      ·
        refine ⟨15010647443356240258408993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20014196591141653677878657 15010647443356240258408993)
        ·
          refine ⟨11257985582517180193806745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15010647443356240258408993 11257985582517180193806745)
          ·
            refine ⟨8443489186887885145355059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11257985582517180193806745 8443489186887885145355059)
            ·
              refine ⟨12665233780331827718032589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443489186887885145355059 12665233780331827718032589)
              ·
                refine ⟨4749462667624435394262221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12665233780331827718032589 4749462667624435394262221)
                ·
                  refine ⟨1781048500359163272848333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4749462667624435394262221 1781048500359163272848333)
                  ·
                    refine ⟨667893187634686227318125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1781048500359163272848333 667893187634686227318125)
                    ·
                      refine ⟨250459945363007335244297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667893187634686227318125 250459945363007335244297)
                      ·
                        rfl

theorem cell23_487769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_487769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487769 prefixEnd_487769 := by exact prefixLift 487769
  have htrace : WordTrace (prefixWord ++ tailWord_487769) baseStart_487769 baseEnd_487769 := by
    simpa [prefixWord, tailWord_487769, baseEnd_487769] using wordTrace_append hprefix tailTrace_487769
  have hstable : (prefixWord ++ tailWord_487769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487769).length < 2 ^ (prefixWord ++ tailWord_487769).sum := by decide
  have hdescent : baseEnd_487769 < baseStart_487769 := by decide
  rcases family_descends (prefixWord ++ tailWord_487769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487776 : List Nat := [2, 1, 1, 3, 6, 1, 9]
def baseStart_487776 : Nat := 118140960795 + 487776 * 2 ^ 59
def prefixEnd_487776 : Nat := 4983230072969 + 3 ^ 40 * 487776 * 2
def baseEnd_487776 : Nat := 3092142465772701331565

theorem tailTrace_487776 : CollatzResearch.WordTrace tailWord_487776 prefixEnd_487776 3092142465772701331565 := by
  unfold tailWord_487776
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895326140439166176809591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11860434853918888235746121 8895326140439166176809591)
  ·
    refine ⟨13342989210658749265214387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8895326140439166176809591 13342989210658749265214387)
    ·
      refine ⟨20014483815988123897821581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342989210658749265214387 20014483815988123897821581)
      ·
        refine ⟨7505431430995546461683093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20014483815988123897821581 7505431430995546461683093)
        ·
          refine ⟨351817098327916240391395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7505431430995546461683093 351817098327916240391395)
          ·
            refine ⟨527725647491874360587093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351817098327916240391395 527725647491874360587093)
            ·
              refine ⟨3092142465772701331565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 527725647491874360587093 3092142465772701331565)
              ·
                rfl

theorem cell23_487776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 9].length) (baseStart_487776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487776 prefixEnd_487776 := by exact prefixLift 487776
  have htrace : WordTrace (prefixWord ++ tailWord_487776) baseStart_487776 baseEnd_487776 := by
    simpa [prefixWord, tailWord_487776, baseEnd_487776] using wordTrace_append hprefix tailTrace_487776
  have hstable : (prefixWord ++ tailWord_487776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487776).length < 2 ^ (prefixWord ++ tailWord_487776).sum := by decide
  have hdescent : baseEnd_487776 < baseStart_487776 := by decide
  rcases family_descends (prefixWord ++ tailWord_487776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487789 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_487789 : Nat := 118140960795 + 487789 * 2 ^ 59
def prefixEnd_487789 : Nat := 4983230072969 + 3 ^ 40 * 487789 * 2
def baseEnd_487789 : Nat := 83490071658699085664735

theorem tailTrace_487789 : CollatzResearch.WordTrace tailWord_487789 prefixEnd_487789 83490071658699085664735 := by
  unfold tailWord_487789
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791126429831235573842421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11860750953220823715894947 17791126429831235573842421)
  ·
    refine ⟨1667918102796678335047727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17791126429831235573842421 1667918102796678335047727)
    ·
      refine ⟨2501877154195017502571591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667918102796678335047727 2501877154195017502571591)
      ·
        refine ⟨3752815731292526253857387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501877154195017502571591 3752815731292526253857387)
        ·
          refine ⟨5629223596938789380786081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752815731292526253857387 5629223596938789380786081)
          ·
            refine ⟨4221917697704092035589561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5629223596938789380786081 4221917697704092035589561)
            ·
              refine ⟨3166438273278069026692171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4221917697704092035589561 3166438273278069026692171)
              ·
                refine ⟨4749657409917103540038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166438273278069026692171 4749657409917103540038257)
                ·
                  refine ⟨3562243057437827655028693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749657409917103540038257 3562243057437827655028693)
                  ·
                    refine ⟨83490071658699085664735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3562243057437827655028693 83490071658699085664735)
                    ·
                      rfl

theorem cell23_487789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_487789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487789 prefixEnd_487789 := by exact prefixLift 487789
  have htrace : WordTrace (prefixWord ++ tailWord_487789) baseStart_487789 baseEnd_487789 := by
    simpa [prefixWord, tailWord_487789, baseEnd_487789] using wordTrace_append hprefix tailTrace_487789
  have hstable : (prefixWord ++ tailWord_487789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487789).length < 2 ^ (prefixWord ++ tailWord_487789).sum := by decide
  have hdescent : baseEnd_487789 < baseStart_487789 := by decide
  rcases family_descends (prefixWord ++ tailWord_487789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487803 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 3]
def baseStart_487803 : Nat := 118140960795 + 487803 * 2 ^ 59
def prefixEnd_487803 : Nat := 4983230072969 + 3 ^ 40 * 487803 * 2
def baseEnd_487803 : Nat := 250477403705260202219141

theorem tailTrace_487803 : CollatzResearch.WordTrace tailWord_487803 prefixEnd_487803 250477403705260202219141 := by
  unfold tailWord_487803
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791637051780515964852063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11861091367853677309901375 17791637051780515964852063)
  ·
    refine ⟨26687455577670773947278095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17791637051780515964852063 26687455577670773947278095)
    ·
      refine ⟨40031183366506160920917143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26687455577670773947278095 40031183366506160920917143)
      ·
        refine ⟨60046775049759241381375715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40031183366506160920917143 60046775049759241381375715)
        ·
          refine ⟨90070162574638862072063573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60046775049759241381375715 90070162574638862072063573)
          ·
            refine ⟨1055509717671549164906995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 90070162574638862072063573 1055509717671549164906995)
            ·
              refine ⟨1583264576507323747360493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055509717671549164906995 1583264576507323747360493)
              ·
                refine ⟨593724216190246405260185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583264576507323747360493 593724216190246405260185)
                ·
                  refine ⟨445293162142684803945139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593724216190246405260185 445293162142684803945139)
                  ·
                    refine ⟨667939743214027205917709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445293162142684803945139 667939743214027205917709)
                    ·
                      refine ⟨250477403705260202219141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 667939743214027205917709 250477403705260202219141)
                      ·
                        rfl

theorem cell23_487803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 3].length) (baseStart_487803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487803 prefixEnd_487803 := by exact prefixLift 487803
  have htrace : WordTrace (prefixWord ++ tailWord_487803) baseStart_487803 baseEnd_487803 := by
    simpa [prefixWord, tailWord_487803, baseEnd_487803] using wordTrace_append hprefix tailTrace_487803
  have hstable : (prefixWord ++ tailWord_487803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487803).length < 2 ^ (prefixWord ++ tailWord_487803).sum := by decide
  have hdescent : baseEnd_487803 < baseStart_487803 := by decide
  rcases family_descends (prefixWord ++ tailWord_487803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487853 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_487853 : Nat := 118140960795 + 487853 * 2 ^ 59
def prefixEnd_487853 : Nat := 4983230072969 + 3 ^ 40 * 487853 * 2
def baseEnd_487853 : Nat := 83501025912661668864637

theorem tailTrace_487853 : CollatzResearch.WordTrace tailWord_487853 prefixEnd_487853 83501025912661668864637 := by
  unfold tailWord_487853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793460701599374504172213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11862307134399583002781475 17793460701599374504172213)
  ·
    refine ⟨1668136940774941359766145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17793460701599374504172213 1668136940774941359766145)
    ·
      refine ⟨1251102705581206019824609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668136940774941359766145 1251102705581206019824609)
      ·
        refine ⟨938327029185904514868457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251102705581206019824609 938327029185904514868457)
        ·
          refine ⟨703745271889428386151343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938327029185904514868457 703745271889428386151343)
          ·
            refine ⟨1055617907834142579227015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703745271889428386151343 1055617907834142579227015)
            ·
              refine ⟨1583426861751213868840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055617907834142579227015 1583426861751213868840523)
              ·
                refine ⟨2375140292626820803260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583426861751213868840523 2375140292626820803260785)
                ·
                  refine ⟨1781355219470115602445589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2375140292626820803260785 1781355219470115602445589)
                  ·
                    refine ⟨83501025912661668864637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1781355219470115602445589 83501025912661668864637)
                    ·
                      rfl

theorem cell23_487853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_487853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487853 prefixEnd_487853 := by exact prefixLift 487853
  have htrace : WordTrace (prefixWord ++ tailWord_487853) baseStart_487853 baseEnd_487853 := by
    simpa [prefixWord, tailWord_487853, baseEnd_487853] using wordTrace_append hprefix tailTrace_487853
  have hstable : (prefixWord ++ tailWord_487853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487853).length < 2 ^ (prefixWord ++ tailWord_487853).sum := by decide
  have hdescent : baseEnd_487853 < baseStart_487853 := by decide
  rcases family_descends (prefixWord ++ tailWord_487853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487889 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_487889 : Nat := 118140960795 + 487889 * 2 ^ 59
def prefixEnd_487889 : Nat := 4983230072969 + 3 ^ 40 * 487889 * 2
def baseEnd_487889 : Nat := 250521563041546865743745

theorem tailTrace_487889 : CollatzResearch.WordTrace tailWord_487889 prefixEnd_487889 250521563041546865743745 := by
  unfold tailWord_487889
  simp only [CollatzResearch.WordTrace]
  refine ⟨17794773729468952652482721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11863182486312635101655147 17794773729468952652482721)
  ·
    refine ⟨13346080297101714489362041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17794773729468952652482721 13346080297101714489362041)
    ·
      refine ⟨10009560222826285867021531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13346080297101714489362041 10009560222826285867021531)
      ·
        refine ⟨15014340334239428800532297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009560222826285867021531 15014340334239428800532297)
        ·
          refine ⟨11260755250679571600399223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15014340334239428800532297 11260755250679571600399223)
          ·
            refine ⟨16891132876019357400598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260755250679571600399223 16891132876019357400598835)
            ·
              refine ⟨25336699314029036100898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16891132876019357400598835 25336699314029036100898253)
              ·
                refine ⟨9501262242760888537836845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25336699314029036100898253 9501262242760888537836845)
                ·
                  refine ⟨3562973341035333201688817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9501262242760888537836845 3562973341035333201688817)
                  ·
                    refine ⟨2672230005776499901266613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562973341035333201688817 2672230005776499901266613)
                    ·
                      refine ⟨250521563041546865743745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2672230005776499901266613 250521563041546865743745)
                      ·
                        rfl

theorem cell23_487889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_487889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487889 prefixEnd_487889 := by exact prefixLift 487889
  have htrace : WordTrace (prefixWord ++ tailWord_487889) baseStart_487889 baseEnd_487889 := by
    simpa [prefixWord, tailWord_487889, baseEnd_487889] using wordTrace_append hprefix tailTrace_487889
  have hstable : (prefixWord ++ tailWord_487889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487889).length < 2 ^ (prefixWord ++ tailWord_487889).sum := by decide
  have hdescent : baseEnd_487889 < baseStart_487889 := by decide
  rcases family_descends (prefixWord ++ tailWord_487889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487926 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_487926 : Nat := 118140960795 + 487926 * 2 ^ 59
def prefixEnd_487926 : Nat := 4983230072969 + 3 ^ 40 * 487926 * 2
def baseEnd_487926 : Nat := 83513520608587740327025

theorem tailTrace_487926 : CollatzResearch.WordTrace tailWord_487926 prefixEnd_487926 83513520608587740327025 := by
  unfold tailWord_487926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112257701895931748223727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11864082153556605314386421 1112257701895931748223727)
  ·
    refine ⟨1668386552843897622335591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112257701895931748223727 1668386552843897622335591)
    ·
      refine ⟨2502579829265846433503387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1668386552843897622335591 2502579829265846433503387)
      ·
        refine ⟨3753869743898769650255081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502579829265846433503387 3753869743898769650255081)
        ·
          refine ⟨2815402307924077237691311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3753869743898769650255081 2815402307924077237691311)
          ·
            refine ⟨4223103461886115856536967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815402307924077237691311 4223103461886115856536967)
            ·
              refine ⟨6334655192829173784805451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223103461886115856536967 6334655192829173784805451)
              ·
                refine ⟨9501982789243760677208177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334655192829173784805451 9501982789243760677208177)
                ·
                  refine ⟨7126487091932820507906133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501982789243760677208177 7126487091932820507906133)
                  ·
                    refine ⟨83513520608587740327025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7126487091932820507906133 83513520608587740327025)
                    ·
                      rfl

theorem cell23_487926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_487926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487926 prefixEnd_487926 := by exact prefixLift 487926
  have htrace : WordTrace (prefixWord ++ tailWord_487926) baseStart_487926 baseEnd_487926 := by
    simpa [prefixWord, tailWord_487926, baseEnd_487926] using wordTrace_append hprefix tailTrace_487926
  have hstable : (prefixWord ++ tailWord_487926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487926).length < 2 ^ (prefixWord ++ tailWord_487926).sum := by decide
  have hdescent : baseEnd_487926 < baseStart_487926 := by decide
  rcases family_descends (prefixWord ++ tailWord_487926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487936 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_487936 : Nat := 118140960795 + 487936 * 2 ^ 59
def prefixEnd_487936 : Nat := 4983230072969 + 3 ^ 40 * 487936 * 2
def baseEnd_487936 : Nat := 250545696632308181856029

theorem tailTrace_487936 : CollatzResearch.WordTrace tailWord_487936 prefixEnd_487936 250545696632308181856029 := by
  unfold tailWord_487936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898243980149339839721831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11864325306865786452962441 8898243980149339839721831)
  ·
    refine ⟨13347365970224009759582747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898243980149339839721831 13347365970224009759582747)
    ·
      refine ⟨20021048955336014639374121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13347365970224009759582747 20021048955336014639374121)
      ·
        refine ⟨15015786716502010979530591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20021048955336014639374121 15015786716502010979530591)
        ·
          refine ⟨22523680074753016469295887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15015786716502010979530591 22523680074753016469295887)
          ·
            refine ⟨33785520112129524703943831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523680074753016469295887 33785520112129524703943831)
            ·
              refine ⟨50678280168194287055915747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33785520112129524703943831 50678280168194287055915747)
              ·
                refine ⟨76017420252291430583873621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50678280168194287055915747 76017420252291430583873621)
                ·
                  refine ⟨890829143581540202154769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 76017420252291430583873621 890829143581540202154769)
                  ·
                    refine ⟨668121857686155151616077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890829143581540202154769 668121857686155151616077)
                    ·
                      refine ⟨250545696632308181856029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668121857686155151616077 250545696632308181856029)
                      ·
                        rfl

theorem cell23_487936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_487936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487936 prefixEnd_487936 := by exact prefixLift 487936
  have htrace : WordTrace (prefixWord ++ tailWord_487936) baseStart_487936 baseEnd_487936 := by
    simpa [prefixWord, tailWord_487936, baseEnd_487936] using wordTrace_append hprefix tailTrace_487936
  have hstable : (prefixWord ++ tailWord_487936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487936).length < 2 ^ (prefixWord ++ tailWord_487936).sum := by decide
  have hdescent : baseEnd_487936 < baseStart_487936 := by decide
  rcases family_descends (prefixWord ++ tailWord_487936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487939 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 10]
def baseStart_487939 : Nat := 118140960795 + 487939 * 2 ^ 59
def prefixEnd_487939 : Nat := 4983230072969 + 3 ^ 40 * 487939 * 2
def baseEnd_487939 : Nat := 27838581897141296679835

theorem tailTrace_487939 : CollatzResearch.WordTrace tailWord_487939 prefixEnd_487939 27838581897141296679835 := by
  unfold tailWord_487939
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796597379287811191802871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11864398252858540794535247 17796597379287811191802871)
  ·
    refine ⟨26694896068931716787704307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17796597379287811191802871 26694896068931716787704307)
    ·
      refine ⟨40042344103397575181556461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26694896068931716787704307 40042344103397575181556461)
      ·
        refine ⟨15015879038774090693083673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40042344103397575181556461 15015879038774090693083673)
        ·
          refine ⟨11261909279080568019812755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15015879038774090693083673 11261909279080568019812755)
          ·
            refine ⟨16892863918620852029719133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261909279080568019812755 16892863918620852029719133)
            ·
              refine ⟨6334823969482819511144675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16892863918620852029719133 6334823969482819511144675)
              ·
                refine ⟨9502235954224229266717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334823969482819511144675 9502235954224229266717013)
                ·
                  refine ⟨27838581897141296679835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9502235954224229266717013 27838581897141296679835)
                  ·
                    rfl

theorem cell23_487939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 10].length) (baseStart_487939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487939 prefixEnd_487939 := by exact prefixLift 487939
  have htrace : WordTrace (prefixWord ++ tailWord_487939) baseStart_487939 baseEnd_487939 := by
    simpa [prefixWord, tailWord_487939, baseEnd_487939] using wordTrace_append hprefix tailTrace_487939
  have hstable : (prefixWord ++ tailWord_487939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487939).length < 2 ^ (prefixWord ++ tailWord_487939).sum := by decide
  have hdescent : baseEnd_487939 < baseStart_487939 := by decide
  rcases family_descends (prefixWord ++ tailWord_487939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487960 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_487960 : Nat := 118140960795 + 487960 * 2 ^ 59
def prefixEnd_487960 : Nat := 4983230072969 + 3 ^ 40 * 487960 * 2
def baseEnd_487960 : Nat := 83519340056005362651973

theorem tailTrace_487960 : CollatzResearch.WordTrace tailWord_487960 prefixEnd_487960 83519340056005362651973 := by
  unfold tailWord_487960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898681656105865889158667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11864908874807821185544889 8898681656105865889158667)
  ·
    refine ⟨13348022484158798833738001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898681656105865889158667 13348022484158798833738001)
    ·
      refine ⟨10011016863119099125303501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348022484158798833738001 10011016863119099125303501)
      ·
        refine ⟨3754131323669662171988813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10011016863119099125303501 3754131323669662171988813)
        ·
          refine ⟨1407799246376123314495805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3754131323669662171988813 1407799246376123314495805)
          ·
            refine ⟨527924717391046242935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1407799246376123314495805 527924717391046242935927)
            ·
              refine ⟨791887076086569364403891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527924717391046242935927 791887076086569364403891)
              ·
                refine ⟨1187830614129854046605837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791887076086569364403891 1187830614129854046605837)
                ·
                  refine ⟨445436480298695267477189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187830614129854046605837 445436480298695267477189)
                  ·
                    refine ⟨83519340056005362651973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445436480298695267477189 83519340056005362651973)
                    ·
                      rfl

theorem cell23_487960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_487960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487960 prefixEnd_487960 := by exact prefixLift 487960
  have htrace : WordTrace (prefixWord ++ tailWord_487960) baseStart_487960 baseEnd_487960 := by
    simpa [prefixWord, tailWord_487960, baseEnd_487960] using wordTrace_append hprefix tailTrace_487960
  have hstable : (prefixWord ++ tailWord_487960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487960).length < 2 ^ (prefixWord ++ tailWord_487960).sum := by decide
  have hdescent : baseEnd_487960 < baseStart_487960 := by decide
  rcases family_descends (prefixWord ++ tailWord_487960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487973 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 6]
def baseStart_487973 : Nat := 118140960795 + 487973 * 2 ^ 59
def prefixEnd_487973 : Nat := 4983230072969 + 3 ^ 40 * 487973 * 2
def baseEnd_487973 : Nat := 27840521712947170788151

theorem tailTrace_487973 : CollatzResearch.WordTrace tailWord_487973 prefixEnd_487973 27840521712947170788151 := by
  unfold tailWord_487973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797837461164634998540573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865224974109756665693715 17797837461164634998540573)
  ·
    refine ⟨6674189047936738124452715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17797837461164634998540573 6674189047936738124452715)
    ·
      refine ⟨10011283571905107186679073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674189047936738124452715 10011283571905107186679073)
      ·
        refine ⟨7508462678928830390009305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10011283571905107186679073 7508462678928830390009305)
        ·
          refine ⟨5631347009196622792506979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7508462678928830390009305 5631347009196622792506979)
          ·
            refine ⟨8447020513794934188760469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631347009196622792506979 8447020513794934188760469)
            ·
              refine ⟨395954086584137540098147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8447020513794934188760469 395954086584137540098147)
              ·
                refine ⟨593931129876206310147221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395954086584137540098147 593931129876206310147221)
                ·
                  refine ⟨27840521712947170788151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593931129876206310147221 27840521712947170788151)
                  ·
                    rfl

theorem cell23_487973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_487973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_487973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_487973 prefixEnd_487973 := by exact prefixLift 487973
  have htrace : WordTrace (prefixWord ++ tailWord_487973) baseStart_487973 baseEnd_487973 := by
    simpa [prefixWord, tailWord_487973, baseEnd_487973] using wordTrace_append hprefix tailTrace_487973
  have hstable : (prefixWord ++ tailWord_487973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487973).length < 2 ^ (prefixWord ++ tailWord_487973).sum := by decide
  have hdescent : baseEnd_487973 < baseStart_487973 := by decide
  rcases family_descends (prefixWord ++ tailWord_487973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488010 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_488010 : Nat := 118140960795 + 488010 * 2 ^ 59
def prefixEnd_488010 : Nat := 4983230072969 + 3 ^ 40 * 488010 * 2
def baseEnd_488010 : Nat := 250583694200740892330689

theorem tailTrace_488010 : CollatzResearch.WordTrace tailWord_488010 prefixEnd_488010 250583694200740892330689 := by
  unfold tailWord_488010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449796740507647579409371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11866124641353726878424989 4449796740507647579409371)
  ·
    refine ⟨6674695110761471369114057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4449796740507647579409371 6674695110761471369114057)
    ·
      refine ⟨5006021333071103526835543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6674695110761471369114057 5006021333071103526835543)
      ·
        refine ⟨7509031999606655290253315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006021333071103526835543 7509031999606655290253315)
        ·
          refine ⟨11263547999409982935379973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509031999606655290253315 11263547999409982935379973)
          ·
            refine ⟨2111915249889371800383745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11263547999409982935379973 2111915249889371800383745)
            ·
              refine ⟨1583936437417028850287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111915249889371800383745 1583936437417028850287809)
              ·
                refine ⟨1187952328062771637715857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583936437417028850287809 1187952328062771637715857)
                ·
                  refine ⟨890964246047078728286893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187952328062771637715857 890964246047078728286893)
                  ·
                    refine ⟨334111592267654523107585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890964246047078728286893 334111592267654523107585)
                    ·
                      refine ⟨250583694200740892330689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334111592267654523107585 250583694200740892330689)
                      ·
                        rfl

theorem cell23_488010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_488010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488010 prefixEnd_488010 := by exact prefixLift 488010
  have htrace : WordTrace (prefixWord ++ tailWord_488010) baseStart_488010 baseEnd_488010 := by
    simpa [prefixWord, tailWord_488010, baseEnd_488010] using wordTrace_append hprefix tailTrace_488010
  have hstable : (prefixWord ++ tailWord_488010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488010).length < 2 ^ (prefixWord ++ tailWord_488010).sum := by decide
  have hdescent : baseEnd_488010 < baseStart_488010 := by decide
  rcases family_descends (prefixWord ++ tailWord_488010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488017 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_488017 : Nat := 118140960795 + 488017 * 2 ^ 59
def prefixEnd_488017 : Nat := 4983230072969 + 3 ^ 40 * 488017 * 2
def baseEnd_488017 : Nat := 250587288565322364943157

theorem tailTrace_488017 : CollatzResearch.WordTrace tailWord_488017 prefixEnd_488017 250587288565322364943157 := by
  unfold tailWord_488017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799442273005230513142305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11866294848670153675428203 17799442273005230513142305)
  ·
    refine ⟨13349581704753922884856729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17799442273005230513142305 13349581704753922884856729)
    ·
      refine ⟨10012186278565442163642547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13349581704753922884856729 10012186278565442163642547)
      ·
        refine ⟨15018279417848163245463821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012186278565442163642547 15018279417848163245463821)
        ·
          refine ⟨5631854781693061217048933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15018279417848163245463821 5631854781693061217048933)
          ·
            refine ⟨1055972771567448978196675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5631854781693061217048933 1055972771567448978196675)
            ·
              refine ⟨1583959157351173467295013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055972771567448978196675 1583959157351173467295013)
              ·
                refine ⟨296992342003345025117815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1583959157351173467295013 296992342003345025117815)
                ·
                  refine ⟨445488513005017537676723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296992342003345025117815 445488513005017537676723)
                  ·
                    refine ⟨668232769507526306515085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445488513005017537676723 668232769507526306515085)
                    ·
                      refine ⟨250587288565322364943157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668232769507526306515085 250587288565322364943157)
                      ·
                        rfl

theorem cell23_488017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_488017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488017 prefixEnd_488017 := by exact prefixLift 488017
  have htrace : WordTrace (prefixWord ++ tailWord_488017) baseStart_488017 baseEnd_488017 := by
    simpa [prefixWord, tailWord_488017, baseEnd_488017] using wordTrace_append hprefix tailTrace_488017
  have hstable : (prefixWord ++ tailWord_488017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488017).length < 2 ^ (prefixWord ++ tailWord_488017).sum := by decide
  have hdescent : baseEnd_488017 < baseStart_488017 := by decide
  rcases family_descends (prefixWord ++ tailWord_488017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488033 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_488033 : Nat := 118140960795 + 488033 * 2 ^ 59
def prefixEnd_488033 : Nat := 4983230072969 + 3 ^ 40 * 488033 * 2
def baseEnd_488033 : Nat := 83531834751931434114361

theorem tailTrace_488033 : CollatzResearch.WordTrace tailWord_488033 prefixEnd_488033 83531834751931434114361 := by
  unfold tailWord_488033
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800025840947265245724753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11866683893964843497149835 17800025840947265245724753)
  ·
    refine ⟨13350019380710448934293565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17800025840947265245724753 13350019380710448934293565)
    ·
      refine ⟨5006257267766418350360087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13350019380710448934293565 5006257267766418350360087)
      ·
        refine ⟨7509385901649627525540131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006257267766418350360087 7509385901649627525540131)
        ·
          refine ⟨11264078852474441288310197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509385901649627525540131 11264078852474441288310197)
          ·
            refine ⟨1056007392419478870779081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11264078852474441288310197 1056007392419478870779081)
            ·
              refine ⟨792005544314609153084311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056007392419478870779081 792005544314609153084311)
              ·
                refine ⟨1188008316471913729626467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792005544314609153084311 1188008316471913729626467)
                ·
                  refine ⟨1782012474707870594439701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188008316471913729626467 1782012474707870594439701)
                  ·
                    refine ⟨83531834751931434114361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1782012474707870594439701 83531834751931434114361)
                    ·
                      rfl

theorem cell23_488033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_488033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488033 prefixEnd_488033 := by exact prefixLift 488033
  have htrace : WordTrace (prefixWord ++ tailWord_488033) baseStart_488033 baseEnd_488033 := by
    simpa [prefixWord, tailWord_488033, baseEnd_488033] using wordTrace_append hprefix tailTrace_488033
  have hstable : (prefixWord ++ tailWord_488033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488033).length < 2 ^ (prefixWord ++ tailWord_488033).sum := by decide
  have hdescent : baseEnd_488033 < baseStart_488033 := by decide
  rcases family_descends (prefixWord ++ tailWord_488033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488034 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_488034 : Nat := 118140960795 + 488034 * 2 ^ 59
def prefixEnd_488034 : Nat := 4983230072969 + 3 ^ 40 * 488034 * 2
def baseEnd_488034 : Nat := 250596017736448798430579

theorem tailTrace_488034 : CollatzResearch.WordTrace tailWord_488034 prefixEnd_488034 250596017736448798430579 := by
  unfold tailWord_488034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450015578485910604127789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11866708209295761611007437 4450015578485910604127789)
  ·
    refine ⟨1668755841932216476547921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4450015578485910604127789 1668755841932216476547921)
    ·
      refine ⟨1251566881449162357410941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668755841932216476547921 1251566881449162357410941)
      ·
        refine ⟨469337580543435884029103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1251566881449162357410941 469337580543435884029103)
        ·
          refine ⟨704006370815153826043655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469337580543435884029103 704006370815153826043655)
          ·
            refine ⟨1056009556222730739065483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704006370815153826043655 1056009556222730739065483)
            ·
              refine ⟨1584014334334096108598225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056009556222730739065483 1584014334334096108598225)
              ·
                refine ⟨1188010750750572081448669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584014334334096108598225 1188010750750572081448669)
                ·
                  refine ⟨445504031531464530543251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188010750750572081448669 445504031531464530543251)
                  ·
                    refine ⟨668256047297196795814877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445504031531464530543251 668256047297196795814877)
                    ·
                      refine ⟨250596017736448798430579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668256047297196795814877 250596017736448798430579)
                      ·
                        rfl

theorem cell23_488034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_488034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488034 prefixEnd_488034 := by exact prefixLift 488034
  have htrace : WordTrace (prefixWord ++ tailWord_488034) baseStart_488034 baseEnd_488034 := by
    simpa [prefixWord, tailWord_488034, baseEnd_488034] using wordTrace_append hprefix tailTrace_488034
  have hstable : (prefixWord ++ tailWord_488034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488034).length < 2 ^ (prefixWord ++ tailWord_488034).sum := by decide
  have hdescent : baseEnd_488034 < baseStart_488034 := by decide
  rcases family_descends (prefixWord ++ tailWord_488034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488054 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_488054 : Nat := 118140960795 + 488054 * 2 ^ 59
def prefixEnd_488054 : Nat := 4983230072969 + 3 ^ 40 * 488054 * 2
def baseEnd_488054 : Nat := 83535429116512906726829

theorem tailTrace_488054 : CollatzResearch.WordTrace tailWord_488054 prefixEnd_488054 83535429116512906726829 := by
  unfold tailWord_488054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112549485866949114514951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11867194515914123888159477 1112549485866949114514951)
  ·
    refine ⟨1668824228800423671772427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112549485866949114514951 1668824228800423671772427)
    ·
      refine ⟨2503236343200635507658641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1668824228800423671772427 2503236343200635507658641)
      ·
        refine ⟨1877427257400476630743981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503236343200635507658641 1877427257400476630743981)
        ·
          refine ⟨704035221525178736528993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1877427257400476630743981 704035221525178736528993)
          ·
            refine ⟨528026416143884052396745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704035221525178736528993 528026416143884052396745)
            ·
              refine ⟨396019812107913039297559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528026416143884052396745 396019812107913039297559)
              ·
                refine ⟨594029718161869558946339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396019812107913039297559 594029718161869558946339)
                ·
                  refine ⟨891044577242804338419509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594029718161869558946339 891044577242804338419509)
                  ·
                    refine ⟨83535429116512906726829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 891044577242804338419509 83535429116512906726829)
                    ·
                      rfl

theorem cell23_488054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_488054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488054 prefixEnd_488054 := by exact prefixLift 488054
  have htrace : WordTrace (prefixWord ++ tailWord_488054) baseStart_488054 baseEnd_488054 := by
    simpa [prefixWord, tailWord_488054, baseEnd_488054] using wordTrace_append hprefix tailTrace_488054
  have hstable : (prefixWord ++ tailWord_488054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488054).length < 2 ^ (prefixWord ++ tailWord_488054).sum := by decide
  have hdescent : baseEnd_488054 < baseStart_488054 := by decide
  rcases family_descends (prefixWord ++ tailWord_488054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488057 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 1, 1, 4]
def baseStart_488057 : Nat := 118140960795 + 488057 * 2 ^ 59
def prefixEnd_488057 : Nat := 4983230072969 + 3 ^ 40 * 488057 * 2
def baseEnd_488057 : Nat := 250607827791502208442973

theorem tailTrace_488057 : CollatzResearch.WordTrace tailWord_488057 prefixEnd_488057 250607827791502208442973 := by
  unfold tailWord_488057
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800901192860317344598425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11867267461906878229732283 17800901192860317344598425)
  ·
    refine ⟨13350675894645238008448819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17800901192860317344598425 13350675894645238008448819)
    ·
      refine ⟨20026013841967857012673229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350675894645238008448819 20026013841967857012673229)
      ·
        refine ⟨7509755190737946379752461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20026013841967857012673229 7509755190737946379752461)
        ·
          refine ⟨2816158196526729892407173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7509755190737946379752461 2816158196526729892407173)
          ·
            refine ⟨528029661848761854826345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2816158196526729892407173 528029661848761854826345)
            ·
              refine ⟨396022246386571391119759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528029661848761854826345 396022246386571391119759)
              ·
                refine ⟨594033369579857086679639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396022246386571391119759 594033369579857086679639)
                ·
                  refine ⟨891050054369785630019459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594033369579857086679639 891050054369785630019459)
                  ·
                    refine ⟨1336575081554678445029189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891050054369785630019459 1336575081554678445029189)
                    ·
                      refine ⟨250607827791502208442973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1336575081554678445029189 250607827791502208442973)
                      ·
                        rfl

theorem cell23_488057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_488057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488057 prefixEnd_488057 := by exact prefixLift 488057
  have htrace : WordTrace (prefixWord ++ tailWord_488057) baseStart_488057 baseEnd_488057 := by
    simpa [prefixWord, tailWord_488057, baseEnd_488057] using wordTrace_append hprefix tailTrace_488057
  have hstable : (prefixWord ++ tailWord_488057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488057).length < 2 ^ (prefixWord ++ tailWord_488057).sum := by decide
  have hdescent : baseEnd_488057 < baseStart_488057 := by decide
  rcases family_descends (prefixWord ++ tailWord_488057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488074 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_488074 : Nat := 118140960795 + 488074 * 2 ^ 59
def prefixEnd_488074 : Nat := 4983230072969 + 3 ^ 40 * 488074 * 2
def baseEnd_488074 : Nat := 250616556962628641930395

theorem tailTrace_488074 : CollatzResearch.WordTrace tailWord_488074 prefixEnd_488074 250616556962628641930395 := by
  unfold tailWord_488074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450380308449682311991819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11867680822532486165311517 4450380308449682311991819)
  ·
    refine ⟨6675570462674523467987729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4450380308449682311991819 6675570462674523467987729)
    ·
      refine ⟨5006677847005892600990797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6675570462674523467987729 5006677847005892600990797)
      ·
        refine ⟨1877504192627209725371549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5006677847005892600990797 1877504192627209725371549)
        ·
          refine ⟨704064072235203647014331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1877504192627209725371549 704064072235203647014331)
          ·
            refine ⟨1056096108352805470521497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704064072235203647014331 1056096108352805470521497)
            ·
              refine ⟨792072081264604102891123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056096108352805470521497 792072081264604102891123)
              ·
                refine ⟨1188108121896906154336685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792072081264604102891123 1188108121896906154336685)
                ·
                  refine ⟨445540545711339807876257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188108121896906154336685 445540545711339807876257)
                  ·
                    refine ⟨334155409283504855907193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445540545711339807876257 334155409283504855907193)
                    ·
                      refine ⟨250616556962628641930395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334155409283504855907193 250616556962628641930395)
                      ·
                        rfl

theorem cell23_488074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_488074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488074 prefixEnd_488074 := by exact prefixLift 488074
  have htrace : WordTrace (prefixWord ++ tailWord_488074) baseStart_488074 baseEnd_488074 := by
    simpa [prefixWord, tailWord_488074, baseEnd_488074] using wordTrace_append hprefix tailTrace_488074
  have hstable : (prefixWord ++ tailWord_488074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488074).length < 2 ^ (prefixWord ++ tailWord_488074).sum := by decide
  have hdescent : baseEnd_488074 < baseStart_488074 := by decide
  rcases family_descends (prefixWord ++ tailWord_488074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488076 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_488076 : Nat := 118140960795 + 488076 * 2 ^ 59
def prefixEnd_488076 : Nat := 4983230072969 + 3 ^ 40 * 488076 * 2
def baseEnd_488076 : Nat := 83539194641312544701795

theorem tailTrace_488076 : CollatzResearch.WordTrace tailWord_488076 prefixEnd_488076 83539194641312544701795 := by
  unfold tailWord_488076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900797089895741794770041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11867729453194322393026721 8900797089895741794770041)
  ·
    refine ⟨6675597817421806346077531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8900797089895741794770041 6675597817421806346077531)
    ·
      refine ⟨10013396726132709519116297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675597817421806346077531 10013396726132709519116297)
      ·
        refine ⟨7510047544599532139337223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013396726132709519116297 7510047544599532139337223)
        ·
          refine ⟨11265071316899298209005835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510047544599532139337223 11265071316899298209005835)
          ·
            refine ⟨16897606975348947313508753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265071316899298209005835 16897606975348947313508753)
            ·
              refine ⟨12673205231511710485131565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16897606975348947313508753 12673205231511710485131565)
              ·
                refine ⟨4752451961816891431924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12673205231511710485131565 4752451961816891431924337)
                ·
                  refine ⟨3564338971362668573943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752451961816891431924337 3564338971362668573943253)
                  ·
                    refine ⟨83539194641312544701795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3564338971362668573943253 83539194641312544701795)
                    ·
                      rfl

theorem cell23_488076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_488076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488076 prefixEnd_488076 := by exact prefixLift 488076
  have htrace : WordTrace (prefixWord ++ tailWord_488076) baseStart_488076 baseEnd_488076 := by
    simpa [prefixWord, tailWord_488076, baseEnd_488076] using wordTrace_append hprefix tailTrace_488076
  have hstable : (prefixWord ++ tailWord_488076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488076).length < 2 ^ (prefixWord ++ tailWord_488076).sum := by decide
  have hdescent : baseEnd_488076 < baseStart_488076 := by decide
  rcases family_descends (prefixWord ++ tailWord_488076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488084 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_488084 : Nat := 118140960795 + 488084 * 2 ^ 59
def prefixEnd_488084 : Nat := 4983230072969 + 3 ^ 40 * 488084 * 2
def baseEnd_488084 : Nat := 83540563923057867601783

theorem tailTrace_488084 : CollatzResearch.WordTrace tailWord_488084 prefixEnd_488084 83540563923057867601783 := by
  unfold tailWord_488084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900942981881250477915653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11867923975841667303887537 8900942981881250477915653)
  ·
    refine ⟨1668926809102734464609185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8900942981881250477915653 1668926809102734464609185)
    ·
      refine ⟨1251695106827050848456889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668926809102734464609185 1251695106827050848456889)
      ·
        refine ⟨938771330120288136342667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251695106827050848456889 938771330120288136342667)
        ·
          refine ⟨1408156995180432204514001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938771330120288136342667 1408156995180432204514001)
          ·
            refine ⟨1056117746385324153385501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408156995180432204514001 1056117746385324153385501)
            ·
              refine ⟨396044154894496557519563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056117746385324153385501 396044154894496557519563)
              ·
                refine ⟨594066232341744836279345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396044154894496557519563 594066232341744836279345)
                ·
                  refine ⟨445549674256308627209509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594066232341744836279345 445549674256308627209509)
                  ·
                    refine ⟨83540563923057867601783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445549674256308627209509 83540563923057867601783)
                    ·
                      rfl

theorem cell23_488084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_488084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488084 prefixEnd_488084 := by exact prefixLift 488084
  have htrace : WordTrace (prefixWord ++ tailWord_488084) baseStart_488084 baseEnd_488084 := by
    simpa [prefixWord, tailWord_488084, baseEnd_488084] using wordTrace_append hprefix tailTrace_488084
  have hstable : (prefixWord ++ tailWord_488084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488084).length < 2 ^ (prefixWord ++ tailWord_488084).sum := by decide
  have hdescent : baseEnd_488084 < baseStart_488084 := by decide
  rcases family_descends (prefixWord ++ tailWord_488084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488097 : List Nat := [1, 2, 3, 3, 4, 1, 2, 7]
def baseStart_488097 : Nat := 118140960795 + 488097 * 2 ^ 59
def prefixEnd_488097 : Nat := 4983230072969 + 3 ^ 40 * 488097 * 2
def baseEnd_488097 : Nat := 9282532111766001923807

theorem tailTrace_488097 : CollatzResearch.WordTrace tailWord_488097 prefixEnd_488097 9282532111766001923807 := by
  unfold tailWord_488097
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802360112715404176054545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11868240075143602784036363 17802360112715404176054545)
  ·
    refine ⟨13351770084536553132040909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17802360112715404176054545 13351770084536553132040909)
    ·
      refine ⟨5006913781701207424515341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13351770084536553132040909 5006913781701207424515341)
      ·
        refine ⟨1877592668137952784193253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5006913781701207424515341 1877592668137952784193253)
        ·
          refine ⟨352048625275866147036235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1877592668137952784193253 352048625275866147036235)
          ·
            refine ⟨528072937913799220554353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352048625275866147036235 528072937913799220554353)
            ·
              refine ⟨396054703435349415415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528072937913799220554353 396054703435349415415765)
              ·
                refine ⟨9282532111766001923807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396054703435349415415765 9282532111766001923807)
                ·
                  rfl

theorem cell23_488097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 7].length) (baseStart_488097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488097 prefixEnd_488097 := by exact prefixLift 488097
  have htrace : WordTrace (prefixWord ++ tailWord_488097) baseStart_488097 baseEnd_488097 := by
    simpa [prefixWord, tailWord_488097, baseEnd_488097] using wordTrace_append hprefix tailTrace_488097
  have hstable : (prefixWord ++ tailWord_488097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488097).length < 2 ^ (prefixWord ++ tailWord_488097).sum := by decide
  have hdescent : baseEnd_488097 < baseStart_488097 := by decide
  rcases family_descends (prefixWord ++ tailWord_488097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488141 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_488141 : Nat := 118140960795 + 488141 * 2 ^ 59
def prefixEnd_488141 : Nat := 4983230072969 + 3 ^ 40 * 488141 * 2
def baseEnd_488141 : Nat := 250650960166479879792587

theorem tailTrace_488141 : CollatzResearch.WordTrace tailWord_488141 prefixEnd_488141 250650960166479879792587 := by
  unfold tailWord_488141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803964924555999690656277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11869309949703999793770851 17803964924555999690656277)
  ·
    refine ⟨834560855838562485499513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17803964924555999690656277 834560855838562485499513)
    ·
      refine ⟨625920641878921864124635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834560855838562485499513 625920641878921864124635)
      ·
        refine ⟨938880962818382796186953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625920641878921864124635 938880962818382796186953)
        ·
          refine ⟨704160722113787097140215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938880962818382796186953 704160722113787097140215)
          ·
            refine ⟨1056241083170680645710323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704160722113787097140215 1056241083170680645710323)
            ·
              refine ⟨1584361624756020968565485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056241083170680645710323 1584361624756020968565485)
              ·
                refine ⟨594135609283507863212057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1584361624756020968565485 594135609283507863212057)
                ·
                  refine ⟨445601706962630897409043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594135609283507863212057 445601706962630897409043)
                  ·
                    refine ⟨668402560443946346113565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445601706962630897409043 668402560443946346113565)
                    ·
                      refine ⟨250650960166479879792587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668402560443946346113565 250650960166479879792587)
                      ·
                        rfl

theorem cell23_488141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_488141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488141 prefixEnd_488141 := by exact prefixLift 488141
  have htrace : WordTrace (prefixWord ++ tailWord_488141) baseStart_488141 baseEnd_488141 := by
    simpa [prefixWord, tailWord_488141, baseEnd_488141] using wordTrace_append hprefix tailTrace_488141
  have hstable : (prefixWord ++ tailWord_488141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488141).length < 2 ^ (prefixWord ++ tailWord_488141).sum := by decide
  have hdescent : baseEnd_488141 < baseStart_488141 := by decide
  rcases family_descends (prefixWord ++ tailWord_488141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488170 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_488170 : Nat := 118140960795 + 488170 * 2 ^ 59
def prefixEnd_488170 : Nat := 4983230072969 + 3 ^ 40 * 488170 * 2
def baseEnd_488170 : Nat := 27851761233940029592217

theorem tailTrace_488170 : CollatzResearch.WordTrace tailWord_488170 prefixEnd_488170 27851761233940029592217 := by
  unfold tailWord_488170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451255660362734410865491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11870015094300625095641309 4451255660362734410865491)
  ·
    refine ⟨6676883490544101616298237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451255660362734410865491 6676883490544101616298237)
    ·
      refine ⟨2503831308954038106111839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6676883490544101616298237 2503831308954038106111839)
      ·
        refine ⟨3755746963431057159167759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503831308954038106111839 3755746963431057159167759)
        ·
          refine ⟨5633620445146585738751639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755746963431057159167759 5633620445146585738751639)
          ·
            refine ⟨8450430667719878608127459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633620445146585738751639 8450430667719878608127459)
            ·
              refine ⟨12675646001579817912191189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450430667719878608127459 12675646001579817912191189)
              ·
                refine ⟨297085453162026982316981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12675646001579817912191189 297085453162026982316981)
                ·
                  refine ⟨27851761233940029592217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297085453162026982316981 27851761233940029592217)
                  ·
                    rfl

theorem cell23_488170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_488170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488170 prefixEnd_488170 := by exact prefixLift 488170
  have htrace : WordTrace (prefixWord ++ tailWord_488170) baseStart_488170 baseEnd_488170 := by
    simpa [prefixWord, tailWord_488170, baseEnd_488170] using wordTrace_append hprefix tailTrace_488170
  have hstable : (prefixWord ++ tailWord_488170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488170).length < 2 ^ (prefixWord ++ tailWord_488170).sum := by decide
  have hdescent : baseEnd_488170 < baseStart_488170 := by decide
  rcases family_descends (prefixWord ++ tailWord_488170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488203 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_488203 : Nat := 118140960795 + 488203 * 2 ^ 59
def prefixEnd_488203 : Nat := 4983230072969 + 3 ^ 40 * 488203 * 2
def baseEnd_488203 : Nat := 250682795967058637217301

theorem tailTrace_488203 : CollatzResearch.WordTrace tailWord_488203 prefixEnd_488203 250682795967058637217301 := by
  unfold tailWord_488203
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806226250331384279413263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11870817500220922852942175 17806226250331384279413263)
  ·
    refine ⟨26709339375497076419119895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17806226250331384279413263 26709339375497076419119895)
    ·
      refine ⟨40064009063245614628679843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26709339375497076419119895 40064009063245614628679843)
      ·
        refine ⟨60096013594868421943019765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40064009063245614628679843 60096013594868421943019765)
        ·
          refine ⟨5634001274518914557158103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60096013594868421943019765 5634001274518914557158103)
          ·
            refine ⟨8451001911778371835737155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634001274518914557158103 8451001911778371835737155)
            ·
              refine ⟨12676502867667557753605733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451001911778371835737155 12676502867667557753605733)
              ·
                refine ⟨2376844287687667078801075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12676502867667557753605733 2376844287687667078801075)
                ·
                  refine ⟨3565266431531500618201613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376844287687667078801075 3565266431531500618201613)
                  ·
                    refine ⟨1336974911824312731825605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565266431531500618201613 1336974911824312731825605)
                    ·
                      refine ⟨250682795967058637217301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1336974911824312731825605 250682795967058637217301)
                      ·
                        rfl

theorem cell23_488203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_488203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488203 prefixEnd_488203 := by exact prefixLift 488203
  have htrace : WordTrace (prefixWord ++ tailWord_488203) baseStart_488203 baseEnd_488203 := by
    simpa [prefixWord, tailWord_488203, baseEnd_488203] using wordTrace_append hprefix tailTrace_488203
  have hstable : (prefixWord ++ tailWord_488203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488203).length < 2 ^ (prefixWord ++ tailWord_488203).sum := by decide
  have hdescent : baseEnd_488203 < baseStart_488203 := by decide
  rcases family_descends (prefixWord ++ tailWord_488203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488220 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_488220 : Nat := 118140960795 + 488220 * 2 ^ 59
def prefixEnd_488220 : Nat := 4983230072969 + 3 ^ 40 * 488220 * 2
def baseEnd_488220 : Nat := 250691525138185070704723

theorem tailTrace_488220 : CollatzResearch.WordTrace tailWord_488220 prefixEnd_488220 250691525138185070704723 := by
  unfold tailWord_488220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903423145634898091391057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11871230860846530788521409 8903423145634898091391057)
  ·
    refine ⟨6677567359226173568543293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8903423145634898091391057 6677567359226173568543293)
    ·
      refine ⟨2504087759709815088203735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6677567359226173568543293 2504087759709815088203735)
      ·
        refine ⟨3756131639564722632305603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504087759709815088203735 3756131639564722632305603)
        ·
          refine ⟨5634197459347083948458405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756131639564722632305603 5634197459347083948458405)
          ·
            refine ⟨1056412023627578240335951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5634197459347083948458405 1056412023627578240335951)
            ·
              refine ⟨1584618035441367360503927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056412023627578240335951 1584618035441367360503927)
              ·
                refine ⟨2376927053162051040755891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584618035441367360503927 2376927053162051040755891)
                ·
                  refine ⟨3565390579743076561133837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376927053162051040755891 3565390579743076561133837)
                  ·
                    refine ⟨1337021467403653710425189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565390579743076561133837 1337021467403653710425189)
                    ·
                      refine ⟨250691525138185070704723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1337021467403653710425189 250691525138185070704723)
                      ·
                        rfl

theorem cell23_488220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_488220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488220 prefixEnd_488220 := by exact prefixLift 488220
  have htrace : WordTrace (prefixWord ++ tailWord_488220) baseStart_488220 baseEnd_488220 := by
    simpa [prefixWord, tailWord_488220, baseEnd_488220] using wordTrace_append hprefix tailTrace_488220
  have hstable : (prefixWord ++ tailWord_488220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488220).length < 2 ^ (prefixWord ++ tailWord_488220).sum := by decide
  have hdescent : baseEnd_488220 < baseStart_488220 := by decide
  rcases family_descends (prefixWord ++ tailWord_488220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488240 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_488240 : Nat := 118140960795 + 488240 * 2 ^ 59
def prefixEnd_488240 : Nat := 4983230072969 + 3 ^ 40 * 488240 * 2
def baseEnd_488240 : Nat := 250701794751274992454631

theorem tailTrace_488240 : CollatzResearch.WordTrace tailWord_488240 prefixEnd_488240 250701794751274992454631 := by
  unfold tailWord_488240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903787875598669799255087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11871717167464893065673449 8903787875598669799255087)
  ·
    refine ⟨13355681813398004698882631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903787875598669799255087 13355681813398004698882631)
    ·
      refine ⟨20033522720097007048323947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13355681813398004698882631 20033522720097007048323947)
      ·
        refine ⟨30050284080145510572485921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033522720097007048323947 30050284080145510572485921)
        ·
          refine ⟨22537713060109132929364441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30050284080145510572485921 22537713060109132929364441)
          ·
            refine ⟨16903284795081849697023331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22537713060109132929364441 16903284795081849697023331)
            ·
              refine ⟨25354927192622774545534997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903284795081849697023331 25354927192622774545534997)
              ·
                refine ⟨1188512212154192556821953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25354927192622774545534997 1188512212154192556821953)
                ·
                  refine ⟨891384159115644417616465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188512212154192556821953 891384159115644417616465)
                  ·
                    refine ⟨668538119336733313212349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891384159115644417616465 668538119336733313212349)
                    ·
                      refine ⟨250701794751274992454631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668538119336733313212349 250701794751274992454631)
                      ·
                        rfl

theorem cell23_488240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_488240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488240 prefixEnd_488240 := by exact prefixLift 488240
  have htrace : WordTrace (prefixWord ++ tailWord_488240) baseStart_488240 baseEnd_488240 := by
    simpa [prefixWord, tailWord_488240, baseEnd_488240] using wordTrace_append hprefix tailTrace_488240
  have hstable : (prefixWord ++ tailWord_488240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488240).length < 2 ^ (prefixWord ++ tailWord_488240).sum := by decide
  have hdescent : baseEnd_488240 < baseStart_488240 := by decide
  rcases family_descends (prefixWord ++ tailWord_488240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488247 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 1, 4]
def baseStart_488247 : Nat := 118140960795 + 488247 * 2 ^ 59
def prefixEnd_488247 : Nat := 4983230072969 + 3 ^ 40 * 488247 * 2
def baseEnd_488247 : Nat := 83568463038618821689033

theorem tailTrace_488247 : CollatzResearch.WordTrace tailWord_488247 prefixEnd_488247 83568463038618821689033 := by
  unfold tailWord_488247
  simp only [CollatzResearch.WordTrace]
  refine ⟨17807831062171979794014995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11871887374781319862676663 17807831062171979794014995)
  ·
    refine ⟨26711746593257969691022493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17807831062171979794014995 26711746593257969691022493)
    ·
      refine ⟨10016904972471738634133435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26711746593257969691022493 10016904972471738634133435)
      ·
        refine ⟨15025357458707607951200153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10016904972471738634133435 15025357458707607951200153)
        ·
          refine ⟨11269018094030705963400115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15025357458707607951200153 11269018094030705963400115)
          ·
            refine ⟨16903527141046058945100173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11269018094030705963400115 16903527141046058945100173)
            ·
              refine ⟨6338822677892272104412565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16903527141046058945100173 6338822677892272104412565)
              ·
                refine ⟨297132313026200254894339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6338822677892272104412565 297132313026200254894339)
                ·
                  refine ⟨445698469539300382341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297132313026200254894339 445698469539300382341509)
                  ·
                    refine ⟨83568463038618821689033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445698469539300382341509 83568463038618821689033)
                    ·
                      rfl

theorem cell23_488247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_488247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488247 prefixEnd_488247 := by exact prefixLift 488247
  have htrace : WordTrace (prefixWord ++ tailWord_488247) baseStart_488247 baseEnd_488247 := by
    simpa [prefixWord, tailWord_488247, baseEnd_488247] using wordTrace_append hprefix tailTrace_488247
  have hstable : (prefixWord ++ tailWord_488247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488247).length < 2 ^ (prefixWord ++ tailWord_488247).sum := by decide
  have hdescent : baseEnd_488247 < baseStart_488247 := by decide
  rcases family_descends (prefixWord ++ tailWord_488247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_488263 : Nat := 118140960795 + 488263 * 2 ^ 59
def prefixEnd_488263 : Nat := 4983230072969 + 3 ^ 40 * 488263 * 2
def baseEnd_488263 : Nat := 250713604806328402467025

theorem tailTrace_488263 : CollatzResearch.WordTrace tailWord_488263 prefixEnd_488263 250713604806328402467025 := by
  unfold tailWord_488263
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808414630114014526597443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11872276420076009684398295 17808414630114014526597443)
  ·
    refine ⟨26712621945171021789896165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808414630114014526597443 26712621945171021789896165)
    ·
      refine ⟨5008616614719566585605531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26712621945171021789896165 5008616614719566585605531)
      ·
        refine ⟨7512924922079349878408297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008616614719566585605531 7512924922079349878408297)
        ·
          refine ⟨5634693691559512408806223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512924922079349878408297 5634693691559512408806223)
          ·
            refine ⟨8452040537339268613209335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634693691559512408806223 8452040537339268613209335)
            ·
              refine ⟨12678060806008902919814003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452040537339268613209335 12678060806008902919814003)
              ·
                refine ⟨19017091209013354379721005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678060806008902919814003 19017091209013354379721005)
                ·
                  refine ⟨7131409203380007892395377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19017091209013354379721005 7131409203380007892395377)
                  ·
                    refine ⟨5348556902535005919296533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7131409203380007892395377 5348556902535005919296533)
                    ·
                      refine ⟨250713604806328402467025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5348556902535005919296533 250713604806328402467025)
                      ·
                        rfl

theorem cell23_488263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_488263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488263 prefixEnd_488263 := by exact prefixLift 488263
  have htrace : WordTrace (prefixWord ++ tailWord_488263) baseStart_488263 baseEnd_488263 := by
    simpa [prefixWord, tailWord_488263, baseEnd_488263] using wordTrace_append hprefix tailTrace_488263
  have hstable : (prefixWord ++ tailWord_488263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488263).length < 2 ^ (prefixWord ++ tailWord_488263).sum := by decide
  have hdescent : baseEnd_488263 < baseStart_488263 := by decide
  rcases family_descends (prefixWord ++ tailWord_488263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488304 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 1, 1, 3]
def baseStart_488304 : Nat := 118140960795 + 488304 * 2 ^ 59
def prefixEnd_488304 : Nat := 4983230072969 + 3 ^ 40 * 488304 * 2
def baseEnd_488304 : Nat := 250734657513162742054337

theorem tailTrace_488304 : CollatzResearch.WordTrace tailWord_488304 prefixEnd_488304 250734657513162742054337 := by
  unfold tailWord_488304
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904955011482739264419983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11873273348643652352559977 8904955011482739264419983)
  ·
    refine ⟨13357432517224108896629975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8904955011482739264419983 13357432517224108896629975)
    ·
      refine ⟨20036148775836163344944963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13357432517224108896629975 20036148775836163344944963)
      ·
        refine ⟨30054223163754245017417445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036148775836163344944963 30054223163754245017417445)
        ·
          refine ⟨5635166843203920940765771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30054223163754245017417445 5635166843203920940765771)
          ·
            refine ⟨8452750264805881411148657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635166843203920940765771 8452750264805881411148657)
            ·
              refine ⟨6339562698604411058361493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452750264805881411148657 6339562698604411058361493)
              ·
                refine ⟨297167001497081768360695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6339562698604411058361493 297167001497081768360695)
                ·
                  refine ⟨445750502245622652541043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297167001497081768360695 445750502245622652541043)
                  ·
                    refine ⟨668625753368433978811565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445750502245622652541043 668625753368433978811565)
                    ·
                      refine ⟨250734657513162742054337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668625753368433978811565 250734657513162742054337)
                      ·
                        rfl

theorem cell23_488304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 1, 3].length) (baseStart_488304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488304 prefixEnd_488304 := by exact prefixLift 488304
  have htrace : WordTrace (prefixWord ++ tailWord_488304) baseStart_488304 baseEnd_488304 := by
    simpa [prefixWord, tailWord_488304, baseEnd_488304] using wordTrace_append hprefix tailTrace_488304
  have hstable : (prefixWord ++ tailWord_488304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488304).length < 2 ^ (prefixWord ++ tailWord_488304).sum := by decide
  have hdescent : baseEnd_488304 < baseStart_488304 := by decide
  rcases family_descends (prefixWord ++ tailWord_488304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488320 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_488320 : Nat := 118140960795 + 488320 * 2 ^ 59
def prefixEnd_488320 : Nat := 4983230072969 + 3 ^ 40 * 488320 * 2
def baseEnd_488320 : Nat := 83580957734544893151421

theorem tailTrace_488320 : CollatzResearch.WordTrace tailWord_488320 prefixEnd_488320 83580957734544893151421 := by
  unfold tailWord_488320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905246795453756630711207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11873662393938342174281609 8905246795453756630711207)
  ·
    refine ⟨13357870193180634946066811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8905246795453756630711207 13357870193180634946066811)
    ·
      refine ⟨20036805289770952419100217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13357870193180634946066811 20036805289770952419100217)
      ·
        refine ⟨15027603967328214314325163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20036805289770952419100217 15027603967328214314325163)
        ·
          refine ⟨22541405950992321471487745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15027603967328214314325163 22541405950992321471487745)
          ·
            refine ⟨16906054463244241103615809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22541405950992321471487745 16906054463244241103615809)
            ·
              refine ⟨12679540847433180827711857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16906054463244241103615809 12679540847433180827711857)
              ·
                refine ⟨9509655635574885620783893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12679540847433180827711857 9509655635574885620783893)
                ·
                  refine ⟨445765107917572763474245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9509655635574885620783893 445765107917572763474245)
                  ·
                    refine ⟨83580957734544893151421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445765107917572763474245 83580957734544893151421)
                    ·
                      rfl

theorem cell23_488320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_488320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488320 prefixEnd_488320 := by exact prefixLift 488320
  have htrace : WordTrace (prefixWord ++ tailWord_488320) baseStart_488320 baseEnd_488320 := by
    simpa [prefixWord, tailWord_488320, baseEnd_488320] using wordTrace_append hprefix tailTrace_488320
  have hstable : (prefixWord ++ tailWord_488320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488320).length < 2 ^ (prefixWord ++ tailWord_488320).sum := by decide
  have hdescent : baseEnd_488320 < baseStart_488320 := by decide
  rcases family_descends (prefixWord ++ tailWord_488320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488327 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_488327 : Nat := 118140960795 + 488327 * 2 ^ 59
def prefixEnd_488327 : Nat := 4983230072969 + 3 ^ 40 * 488327 * 2
def baseEnd_488327 : Nat := 250746467568216152066731

theorem tailTrace_488327 : CollatzResearch.WordTrace tailWord_488327 prefixEnd_488327 250746467568216152066731 := by
  unfold tailWord_488327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810748901882153456927235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11873832601254768971284823 17810748901882153456927235)
  ·
    refine ⟨26716123352823230185390853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17810748901882153456927235 26716123352823230185390853)
    ·
      refine ⟨5009273128654355659760785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26716123352823230185390853 5009273128654355659760785)
      ·
        refine ⟨3756954846490766744820589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5009273128654355659760785 3756954846490766744820589)
        ·
          refine ⟨1408858067434037529307721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3756954846490766744820589 1408858067434037529307721)
          ·
            refine ⟨1056643550575528146980791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408858067434037529307721 1056643550575528146980791)
            ·
              refine ⟨1584965325863292220471187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056643550575528146980791 1584965325863292220471187)
              ·
                refine ⟨2377447988794938330706781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584965325863292220471187 2377447988794938330706781)
                ·
                  refine ⟨891542995798101874015043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2377447988794938330706781 891542995798101874015043)
                  ·
                    refine ⟨1337314493697152811022565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891542995798101874015043 1337314493697152811022565)
                    ·
                      refine ⟨250746467568216152066731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1337314493697152811022565 250746467568216152066731)
                      ·
                        rfl

theorem cell23_488327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_488327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488327 prefixEnd_488327 := by exact prefixLift 488327
  have htrace : WordTrace (prefixWord ++ tailWord_488327) baseStart_488327 baseEnd_488327 := by
    simpa [prefixWord, tailWord_488327, baseEnd_488327] using wordTrace_append hprefix tailTrace_488327
  have hstable : (prefixWord ++ tailWord_488327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488327).length < 2 ^ (prefixWord ++ tailWord_488327).sum := by decide
  have hdescent : baseEnd_488327 < baseStart_488327 := by decide
  rcases family_descends (prefixWord ++ tailWord_488327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488350 : List Nat := [4, 3, 1, 15]
def baseStart_488350 : Nat := 118140960795 + 488350 * 2 ^ 59
def prefixEnd_488350 : Nat := 4983230072969 + 3 ^ 40 * 488350 * 2
def baseEnd_488350 : Nat := 114658563156501857375

theorem tailTrace_488350 : CollatzResearch.WordTrace tailWord_488350 prefixEnd_488350 114658563156501857375 := by
  unfold tailWord_488350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226448472599853548126813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11874391853865885590009669 2226448472599853548126813)
  ·
    refine ⟨834918177224945080547555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2226448472599853548126813 834918177224945080547555)
    ·
      refine ⟨1252377265837417620821333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834918177224945080547555 1252377265837417620821333)
      ·
        refine ⟨114658563156501857375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 1252377265837417620821333 114658563156501857375)
        ·
          rfl

theorem cell23_488350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 15].length) (baseStart_488350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488350 prefixEnd_488350 := by exact prefixLift 488350
  have htrace : WordTrace (prefixWord ++ tailWord_488350) baseStart_488350 baseEnd_488350 := by
    simpa [prefixWord, tailWord_488350, baseEnd_488350] using wordTrace_append hprefix tailTrace_488350
  have hstable : (prefixWord ++ tailWord_488350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488350).length < 2 ^ (prefixWord ++ tailWord_488350).sum := by decide
  have hdescent : baseEnd_488350 < baseStart_488350 := by decide
  rcases family_descends (prefixWord ++ tailWord_488350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488354 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_488354 : Nat := 118140960795 + 488354 * 2 ^ 59
def prefixEnd_488354 : Nat := 4983230072969 + 3 ^ 40 * 488354 * 2
def baseEnd_488354 : Nat := 83586777181962515476369

theorem tailTrace_488354 : CollatzResearch.WordTrace tailWord_488354 prefixEnd_488354 83586777181962515476369 := by
  unfold tailWord_488354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452933418196084267040029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11874489115189558045440077 4452933418196084267040029)
  ·
    refine ⟨1669850031823531600140011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4452933418196084267040029 1669850031823531600140011)
    ·
      refine ⟨2504775047735297400210017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669850031823531600140011 2504775047735297400210017)
      ·
        refine ⟨1878581285801473050157513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504775047735297400210017 1878581285801473050157513)
        ·
          refine ⟨1408935964351104787618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878581285801473050157513 1408935964351104787618135)
          ·
            refine ⟨2113403946526657181427203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408935964351104787618135 2113403946526657181427203)
            ·
              refine ⟨3170105919789985772140805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113403946526657181427203 3170105919789985772140805)
              ·
                refine ⟨594394859960622332276401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3170105919789985772140805 594394859960622332276401)
                ·
                  refine ⟨445796144970466749207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594394859960622332276401 445796144970466749207301)
                  ·
                    refine ⟨83586777181962515476369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445796144970466749207301 83586777181962515476369)
                    ·
                      rfl

theorem cell23_488354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_488354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488354 prefixEnd_488354 := by exact prefixLift 488354
  have htrace : WordTrace (prefixWord ++ tailWord_488354) baseStart_488354 baseEnd_488354 := by
    simpa [prefixWord, tailWord_488354, baseEnd_488354] using wordTrace_append hprefix tailTrace_488354
  have hstable : (prefixWord ++ tailWord_488354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488354).length < 2 ^ (prefixWord ++ tailWord_488354).sum := by decide
  have hdescent : baseEnd_488354 < baseStart_488354 := by decide
  rcases family_descends (prefixWord ++ tailWord_488354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488361 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 1, 2, 2]
def baseStart_488361 : Nat := 118140960795 + 488361 * 2 ^ 59
def prefixEnd_488361 : Nat := 4983230072969 + 3 ^ 40 * 488361 * 2
def baseEnd_488361 : Nat := 250763925910469019041575

theorem tailTrace_488361 : CollatzResearch.WordTrace tailWord_488361 prefixEnd_488361 250763925910469019041575 := by
  unfold tailWord_488361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811988983758977263664937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11874659322505984842443291 17811988983758977263664937)
  ·
    refine ⟨13358991737819232947748703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17811988983758977263664937 13358991737819232947748703)
    ·
      refine ⟨20038487606728849421623055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13358991737819232947748703 20038487606728849421623055)
      ·
        refine ⟨30057731410093274132434583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038487606728849421623055 30057731410093274132434583)
        ·
          refine ⟨45086597115139911198651875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30057731410093274132434583 45086597115139911198651875)
          ·
            refine ⟨67629895672709866797977813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45086597115139911198651875 67629895672709866797977813)
            ·
              refine ⟨1585075679829137503077605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67629895672709866797977813 1585075679829137503077605)
              ·
                refine ⟨297201689967963281827051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1585075679829137503077605 297201689967963281827051)
                ·
                  refine ⟨445802534951944922740577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297201689967963281827051 445802534951944922740577)
                  ·
                    refine ⟨334351901213958692055433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445802534951944922740577 334351901213958692055433)
                    ·
                      refine ⟨250763925910469019041575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334351901213958692055433 250763925910469019041575)
                      ·
                        rfl

theorem cell23_488361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 2, 2].length) (baseStart_488361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488361 prefixEnd_488361 := by exact prefixLift 488361
  have htrace : WordTrace (prefixWord ++ tailWord_488361) baseStart_488361 baseEnd_488361 := by
    simpa [prefixWord, tailWord_488361, baseEnd_488361] using wordTrace_append hprefix tailTrace_488361
  have hstable : (prefixWord ++ tailWord_488361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488361).length < 2 ^ (prefixWord ++ tailWord_488361).sum := by decide
  have hdescent : baseEnd_488361 < baseStart_488361 := by decide
  rcases family_descends (prefixWord ++ tailWord_488361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488377 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_488377 : Nat := 118140960795 + 488377 * 2 ^ 59
def prefixEnd_488377 : Nat := 4983230072969 + 3 ^ 40 * 488377 * 2
def baseEnd_488377 : Nat := 250772141600940956441501

theorem tailTrace_488377 : CollatzResearch.WordTrace tailWord_488377 prefixEnd_488377 250772141600940956441501 := by
  unfold tailWord_488377
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812572551701011996247385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11875048367800674664164923 17812572551701011996247385)
  ·
    refine ⟨13359429413775758997185539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17812572551701011996247385 13359429413775758997185539)
    ·
      refine ⟨20039144120663638495778309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359429413775758997185539 20039144120663638495778309)
      ·
        refine ⟨3757339522624432217958433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20039144120663638495778309 3757339522624432217958433)
        ·
          refine ⟨2818004641968324163468825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3757339522624432217958433 2818004641968324163468825)
          ·
            refine ⟨2113503481476243122601619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2818004641968324163468825 2113503481476243122601619)
            ·
              refine ⟨3170255222214364683902429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113503481476243122601619 3170255222214364683902429)
              ·
                refine ⟨1188845708330386756463411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170255222214364683902429 1188845708330386756463411)
                ·
                  refine ⟨1783268562495580134695117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188845708330386756463411 1783268562495580134695117)
                  ·
                    refine ⟨668725710935842550510669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783268562495580134695117 668725710935842550510669)
                    ·
                      refine ⟨250772141600940956441501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 668725710935842550510669 250772141600940956441501)
                      ·
                        rfl

theorem cell23_488377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_488377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488377 prefixEnd_488377 := by exact prefixLift 488377
  have htrace : WordTrace (prefixWord ++ tailWord_488377) baseStart_488377 baseEnd_488377 := by
    simpa [prefixWord, tailWord_488377, baseEnd_488377] using wordTrace_append hprefix tailTrace_488377
  have hstable : (prefixWord ++ tailWord_488377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488377).length < 2 ^ (prefixWord ++ tailWord_488377).sum := by decide
  have hdescent : baseEnd_488377 < baseStart_488377 := by decide
  rcases family_descends (prefixWord ++ tailWord_488377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488420 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_488420 : Nat := 118140960795 + 488420 * 2 ^ 59
def prefixEnd_488420 : Nat := 4983230072969 + 3 ^ 40 * 488420 * 2
def baseEnd_488420 : Nat := 250794221269084288203803

theorem tailTrace_488420 : CollatzResearch.WordTrace tailWord_488420 prefixEnd_488420 250794221269084288203803 := by
  unfold tailWord_488420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907070445272615170031357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11876093927030153560041809 8907070445272615170031357)
  ·
    refine ⟨3340151416977230688761759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8907070445272615170031357 3340151416977230688761759)
    ·
      refine ⟨5010227125465846033142639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340151416977230688761759 5010227125465846033142639)
      ·
        refine ⟨7515340688198769049713959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010227125465846033142639 7515340688198769049713959)
        ·
          refine ⟨11273011032298153574570939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7515340688198769049713959 11273011032298153574570939)
          ·
            refine ⟨16909516548447230361856409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273011032298153574570939 16909516548447230361856409)
            ·
              refine ⟨12682137411335422771392307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16909516548447230361856409 12682137411335422771392307)
              ·
                refine ⟨19023206117003134157088461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682137411335422771392307 19023206117003134157088461)
                ·
                  refine ⟨7133702293876175308908173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19023206117003134157088461 7133702293876175308908173)
                  ·
                    refine ⟨2675138360203565740840565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7133702293876175308908173 2675138360203565740840565)
                    ·
                      refine ⟨250794221269084288203803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2675138360203565740840565 250794221269084288203803)
                      ·
                        rfl

theorem cell23_488420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_488420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488420 prefixEnd_488420 := by exact prefixLift 488420
  have htrace : WordTrace (prefixWord ++ tailWord_488420) baseStart_488420 baseEnd_488420 := by
    simpa [prefixWord, tailWord_488420, baseEnd_488420] using wordTrace_append hprefix tailTrace_488420
  have hstable : (prefixWord ++ tailWord_488420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488420).length < 2 ^ (prefixWord ++ tailWord_488420).sum := by decide
  have hdescent : baseEnd_488420 < baseStart_488420 := by decide
  rcases family_descends (prefixWord ++ tailWord_488420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488438 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_488438 : Nat := 118140960795 + 488438 * 2 ^ 59
def prefixEnd_488438 : Nat := 4983230072969 + 3 ^ 40 * 488438 * 2
def baseEnd_488438 : Nat := 250803463920865217778721

theorem tailTrace_488438 : CollatzResearch.WordTrace tailWord_488438 prefixEnd_488438 250803463920865217778721 := by
  unfold tailWord_488438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113424837780001213388623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11876531602986679609478645 1113424837780001213388623)
  ·
    refine ⟨1670137256670001820082935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113424837780001213388623 1670137256670001820082935)
    ·
      refine ⟨2505205885005002730124403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670137256670001820082935 2505205885005002730124403)
      ·
        refine ⟨3757808827507504095186605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505205885005002730124403 3757808827507504095186605)
        ·
          refine ⟨1409178310315314035694977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3757808827507504095186605 1409178310315314035694977)
          ·
            refine ⟨1056883732736485526771233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409178310315314035694977 1056883732736485526771233)
            ·
              refine ⟨792662799552364145078425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056883732736485526771233 792662799552364145078425)
              ·
                refine ⟨594497099664273108808819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792662799552364145078425 594497099664273108808819)
                ·
                  refine ⟨891745649496409663213229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594497099664273108808819 891745649496409663213229)
                  ·
                    refine ⟨334404618561153623704961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891745649496409663213229 334404618561153623704961)
                    ·
                      refine ⟨250803463920865217778721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334404618561153623704961 250803463920865217778721)
                      ·
                        rfl

theorem cell23_488438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_488438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488438 prefixEnd_488438 := by exact prefixLift 488438
  have htrace : WordTrace (prefixWord ++ tailWord_488438) baseStart_488438 baseEnd_488438 := by
    simpa [prefixWord, tailWord_488438, baseEnd_488438] using wordTrace_append hprefix tailTrace_488438
  have hstable : (prefixWord ++ tailWord_488438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488438).length < 2 ^ (prefixWord ++ tailWord_488438).sum := by decide
  have hdescent : baseEnd_488438 < baseStart_488438 := by decide
  rcases family_descends (prefixWord ++ tailWord_488438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488504 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_488504 : Nat := 118140960795 + 488504 * 2 ^ 59
def prefixEnd_488504 : Nat := 4983230072969 + 3 ^ 40 * 488504 * 2
def baseEnd_488504 : Nat := 83612451214687319851139

theorem tailTrace_488504 : CollatzResearch.WordTrace tailWord_488504 prefixEnd_488504 83612451214687319851139 := by
  unfold tailWord_488504
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908602311120456343060283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11878136414827275124080377 8908602311120456343060283)
  ·
    refine ⟨13362903466680684514590425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8908602311120456343060283 13362903466680684514590425)
    ·
      refine ⟨10022177600010513385942819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13362903466680684514590425 10022177600010513385942819)
      ·
        refine ⟨15033266400015770078914229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022177600010513385942819 15033266400015770078914229)
        ·
          refine ⟨1409368725001478444898209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15033266400015770078914229 1409368725001478444898209)
          ·
            refine ⟨1057026543751108833673657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409368725001478444898209 1057026543751108833673657)
            ·
              refine ⟨792769907813331625255243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057026543751108833673657 792769907813331625255243)
              ·
                refine ⟨1189154861719997437882865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792769907813331625255243 1189154861719997437882865)
                ·
                  refine ⟨891866146289998078412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1189154861719997437882865 891866146289998078412149)
                  ·
                    refine ⟨83612451214687319851139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 891866146289998078412149 83612451214687319851139)
                    ·
                      rfl

theorem cell23_488504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_488504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488504 prefixEnd_488504 := by exact prefixLift 488504
  have htrace : WordTrace (prefixWord ++ tailWord_488504) baseStart_488504 baseEnd_488504 := by
    simpa [prefixWord, tailWord_488504, baseEnd_488504] using wordTrace_append hprefix tailTrace_488504
  have hstable : (prefixWord ++ tailWord_488504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488504).length < 2 ^ (prefixWord ++ tailWord_488504).sum := by decide
  have hdescent : baseEnd_488504 < baseStart_488504 := by decide
  rcases family_descends (prefixWord ++ tailWord_488504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488524 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_488524 : Nat := 118140960795 + 488524 * 2 ^ 59
def prefixEnd_488524 : Nat := 4983230072969 + 3 ^ 40 * 488524 * 2
def baseEnd_488524 : Nat := 250847623257151881303325

theorem tailTrace_488524 : CollatzResearch.WordTrace tailWord_488524 prefixEnd_488524 250847623257151881303325 := by
  unfold tailWord_488524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908967041084228050924313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11878622721445637401232417 8908967041084228050924313)
  ·
    refine ⟨6681725280813171038193235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8908967041084228050924313 6681725280813171038193235)
    ·
      refine ⟨10022587921219756557289853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681725280813171038193235 10022587921219756557289853)
      ·
        refine ⟨3758470470457408708983695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10022587921219756557289853 3758470470457408708983695)
        ·
          refine ⟨5637705705686113063475543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758470470457408708983695 5637705705686113063475543)
          ·
            refine ⟨8456558558529169595213315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637705705686113063475543 8456558558529169595213315)
            ·
              refine ⟨12684837837793754392819973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456558558529169595213315 12684837837793754392819973)
              ·
                refine ⟨2378407094586328948653745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12684837837793754392819973 2378407094586328948653745)
                ·
                  refine ⟨1783805320939746711490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378407094586328948653745 1783805320939746711490309)
                  ·
                    refine ⟨334463497676202508404433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783805320939746711490309 334463497676202508404433)
                    ·
                      refine ⟨250847623257151881303325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334463497676202508404433 250847623257151881303325)
                      ·
                        rfl

theorem cell23_488524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_488524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488524 prefixEnd_488524 := by exact prefixLift 488524
  have htrace : WordTrace (prefixWord ++ tailWord_488524) baseStart_488524 baseEnd_488524 := by
    simpa [prefixWord, tailWord_488524, baseEnd_488524] using wordTrace_append hprefix tailTrace_488524
  have hstable : (prefixWord ++ tailWord_488524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488524).length < 2 ^ (prefixWord ++ tailWord_488524).sum := by decide
  have hdescent : baseEnd_488524 < baseStart_488524 := by decide
  rcases family_descends (prefixWord ++ tailWord_488524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488581 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 6]
def baseStart_488581 : Nat := 118140960795 + 488581 * 2 ^ 59
def prefixEnd_488581 : Nat := 4983230072969 + 3 ^ 40 * 488581 * 2
def baseEnd_488581 : Nat := 27875210183828684254507

theorem tailTrace_488581 : CollatzResearch.WordTrace tailWord_488581 prefixEnd_488581 27875210183828684254507 := by
  unfold tailWord_488581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820013042961954836673597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11880008695307969891115731 17820013042961954836673597)
  ·
    refine ⟨6682504891110733063752599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17820013042961954836673597 6682504891110733063752599)
    ·
      refine ⟨10023757336666099595628899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6682504891110733063752599 10023757336666099595628899)
      ·
        refine ⟨15035636004999149393443349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023757336666099595628899 15035636004999149393443349)
        ·
          refine ⟨704795437734335127817657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15035636004999149393443349 704795437734335127817657)
          ·
            refine ⟨528596578300751345863243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704795437734335127817657 528596578300751345863243)
            ·
              refine ⟨792894867451127018794865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528596578300751345863243 792894867451127018794865)
              ·
                refine ⟨594671150588345264096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792894867451127018794865 594671150588345264096149)
                ·
                  refine ⟨27875210183828684254507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594671150588345264096149 27875210183828684254507)
                  ·
                    rfl

theorem cell23_488581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_488581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488581 prefixEnd_488581 := by exact prefixLift 488581
  have htrace : WordTrace (prefixWord ++ tailWord_488581) baseStart_488581 baseEnd_488581 := by
    simpa [prefixWord, tailWord_488581, baseEnd_488581] using wordTrace_append hprefix tailTrace_488581
  have hstable : (prefixWord ++ tailWord_488581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488581).length < 2 ^ (prefixWord ++ tailWord_488581).sum := by decide
  have hdescent : baseEnd_488581 < baseStart_488581 := by decide
  rcases family_descends (prefixWord ++ tailWord_488581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488597 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_488597 : Nat := 118140960795 + 488597 * 2 ^ 59
def prefixEnd_488597 : Nat := 4983230072969 + 3 ^ 40 * 488597 * 2
def baseEnd_488597 : Nat := 250885107344930095690489

theorem tailTrace_488597 : CollatzResearch.WordTrace tailWord_488597 prefixEnd_488597 250885107344930095690489 := by
  unfold tailWord_488597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820596610903989569256045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11880397740602659712837363 17820596610903989569256045)
  ·
    refine ⟨6682723729088996088471017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17820596610903989569256045 6682723729088996088471017)
    ·
      refine ⟨5012042796816747066353263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6682723729088996088471017 5012042796816747066353263)
      ·
        refine ⟨7518064195225120599529895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012042796816747066353263 7518064195225120599529895)
        ·
          refine ⟨11277096292837680899294843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518064195225120599529895 11277096292837680899294843)
          ·
            refine ⟨16915644439256521348942265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277096292837680899294843 16915644439256521348942265)
            ·
              refine ⟨12686733329442391011706699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16915644439256521348942265 12686733329442391011706699)
              ·
                refine ⟨19030099994163586517560049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686733329442391011706699 19030099994163586517560049)
                ·
                  refine ⟨14272574995622689888170037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19030099994163586517560049 14272574995622689888170037)
                  ·
                    refine ⟨1338053905839627177015941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14272574995622689888170037 1338053905839627177015941)
                    ·
                      refine ⟨250885107344930095690489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1338053905839627177015941 250885107344930095690489)
                      ·
                        rfl

theorem cell23_488597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_488597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488597 prefixEnd_488597 := by exact prefixLift 488597
  have htrace : WordTrace (prefixWord ++ tailWord_488597) baseStart_488597 baseEnd_488597 := by
    simpa [prefixWord, tailWord_488597, baseEnd_488597] using wordTrace_append hprefix tailTrace_488597
  have hstable : (prefixWord ++ tailWord_488597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488597).length < 2 ^ (prefixWord ++ tailWord_488597).sum := by decide
  have hdescent : baseEnd_488597 < baseStart_488597 := by decide
  rcases family_descends (prefixWord ++ tailWord_488597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488618 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_488618 : Nat := 118140960795 + 488618 * 2 ^ 59
def prefixEnd_488618 : Nat := 4983230072969 + 3 ^ 40 * 488618 * 2
def baseEnd_488618 : Nat := 250895890438674513527893

theorem tailTrace_488618 : CollatzResearch.WordTrace tailWord_488618 prefixEnd_488618 250895890438674513527893 := by
  unfold tailWord_488618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455340635956977538942627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11880908362551940103847005 4455340635956977538942627)
  ·
    refine ⟨6683010953935466308413941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455340635956977538942627 6683010953935466308413941)
    ·
      refine ⟨626532276931449966413807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6683010953935466308413941 626532276931449966413807)
      ·
        refine ⟨939798415397174949620711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626532276931449966413807 939798415397174949620711)
        ·
          refine ⟨1409697623095762424431067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939798415397174949620711 1409697623095762424431067)
          ·
            refine ⟨2114546434643643636646601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409697623095762424431067 2114546434643643636646601)
            ·
              refine ⟨1585909825982732727484951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114546434643643636646601 1585909825982732727484951)
              ·
                refine ⟨2378864738974099091227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585909825982732727484951 2378864738974099091227427)
                ·
                  refine ⟨3568297108461148636841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378864738974099091227427 3568297108461148636841141)
                  ·
                    refine ⟨334527853918232684703857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3568297108461148636841141 334527853918232684703857)
                    ·
                      refine ⟨250895890438674513527893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334527853918232684703857 250895890438674513527893)
                      ·
                        rfl

theorem cell23_488618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_488618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488618 prefixEnd_488618 := by exact prefixLift 488618
  have htrace : WordTrace (prefixWord ++ tailWord_488618) baseStart_488618 baseEnd_488618 := by
    simpa [prefixWord, tailWord_488618, baseEnd_488618] using wordTrace_append hprefix tailTrace_488618
  have hstable : (prefixWord ++ tailWord_488618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488618).length < 2 ^ (prefixWord ++ tailWord_488618).sum := by decide
  have hdescent : baseEnd_488618 < baseStart_488618 := by decide
  rcases family_descends (prefixWord ++ tailWord_488618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488625 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_488625 : Nat := 118140960795 + 488625 * 2 ^ 59
def prefixEnd_488625 : Nat := 4983230072969 + 3 ^ 40 * 488625 * 2
def baseEnd_488625 : Nat := 250899484803255986140361

theorem tailTrace_488625 : CollatzResearch.WordTrace tailWord_488625 prefixEnd_488625 250899484803255986140361 := by
  unfold tailWord_488625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821617854802550351275329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881078569868366900850219 17821617854802550351275329)
  ·
    refine ⟨13366213391101912763456497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17821617854802550351275329 13366213391101912763456497)
    ·
      refine ⟨10024660043326434572592373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13366213391101912763456497 10024660043326434572592373)
      ·
        refine ⟨939811879061853241180535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10024660043326434572592373 939811879061853241180535)
        ·
          refine ⟨1409717818592779861770803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939811879061853241180535 1409717818592779861770803)
          ·
            refine ⟨2114576727889169792656205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409717818592779861770803 2114576727889169792656205)
            ·
              refine ⟨792966272958438672246077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2114576727889169792656205 792966272958438672246077)
              ·
                refine ⟨297362352359414502092279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792966272958438672246077 297362352359414502092279)
                ·
                  refine ⟨446043528539121753138419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297362352359414502092279 446043528539121753138419)
                  ·
                    refine ⟨669065292808682629707629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446043528539121753138419 669065292808682629707629)
                    ·
                      refine ⟨250899484803255986140361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669065292808682629707629 250899484803255986140361)
                      ·
                        rfl

theorem cell23_488625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_488625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488625 prefixEnd_488625 := by exact prefixLift 488625
  have htrace : WordTrace (prefixWord ++ tailWord_488625) baseStart_488625 baseEnd_488625 := by
    simpa [prefixWord, tailWord_488625, baseEnd_488625] using wordTrace_append hprefix tailTrace_488625
  have hstable : (prefixWord ++ tailWord_488625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488625).length < 2 ^ (prefixWord ++ tailWord_488625).sum := by decide
  have hdescent : baseEnd_488625 < baseStart_488625 := by decide
  rcases family_descends (prefixWord ++ tailWord_488625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488634 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_488634 : Nat := 118140960795 + 488634 * 2 ^ 59
def prefixEnd_488634 : Nat := 4983230072969 + 3 ^ 40 * 488634 * 2
def baseEnd_488634 : Nat := 250904106129146450927819

theorem tailTrace_488634 : CollatzResearch.WordTrace tailWord_488634 prefixEnd_488634 250904106129146450927819 := by
  unfold tailWord_488634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455486527942486222088239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11881297407846629925568637 4455486527942486222088239)
  ·
    refine ⟨6683229791913729333132359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455486527942486222088239 6683229791913729333132359)
    ·
      refine ⟨10024844687870593999698539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6683229791913729333132359 10024844687870593999698539)
      ·
        refine ⟨15037267031805890999547809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10024844687870593999698539 15037267031805890999547809)
        ·
          refine ⟨11277950273854418249660857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037267031805890999547809 11277950273854418249660857)
          ·
            refine ⟨8458462705390813687245643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277950273854418249660857 8458462705390813687245643)
            ·
              refine ⟨12687694058086220530868465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458462705390813687245643 12687694058086220530868465)
              ·
                refine ⟨9515770543564665398151349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687694058086220530868465 9515770543564665398151349)
                ·
                  refine ⟨892103488459187381076689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9515770543564665398151349 892103488459187381076689)
                  ·
                    refine ⟨669077616344390535807517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892103488459187381076689 669077616344390535807517)
                    ·
                      refine ⟨250904106129146450927819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669077616344390535807517 250904106129146450927819)
                      ·
                        rfl

theorem cell23_488634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_488634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488634 prefixEnd_488634 := by exact prefixLift 488634
  have htrace : WordTrace (prefixWord ++ tailWord_488634) baseStart_488634 baseEnd_488634 := by
    simpa [prefixWord, tailWord_488634, baseEnd_488634] using wordTrace_append hprefix tailTrace_488634
  have hstable : (prefixWord ++ tailWord_488634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488634).length < 2 ^ (prefixWord ++ tailWord_488634).sum := by decide
  have hdescent : baseEnd_488634 < baseStart_488634 := by decide
  rcases family_descends (prefixWord ++ tailWord_488634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488637 : List Nat := [1, 4, 1, 2, 1, 1, 13]
def baseStart_488637 : Nat := 118140960795 + 488637 * 2 ^ 59
def prefixEnd_488637 : Nat := 4983230072969 + 3 ^ 40 * 488637 * 2
def baseEnd_488637 : Nat := 3097600574951974557905

theorem tailTrace_488637 : CollatzResearch.WordTrace tailWord_488637 prefixEnd_488637 3097600574951974557905 := by
  unfold tailWord_488637
  simp only [CollatzResearch.WordTrace]
  refine ⟨17822055530759076400712165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881370353839384267141443 17822055530759076400712165)
  ·
    refine ⟨3341635412017326825133531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17822055530759076400712165 3341635412017326825133531)
    ·
      refine ⟨5012453118025990237700297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341635412017326825133531 5012453118025990237700297)
      ·
        refine ⟨3759339838519492678275223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5012453118025990237700297 3759339838519492678275223)
        ·
          refine ⟨5639009757779239017412835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759339838519492678275223 5639009757779239017412835)
          ·
            refine ⟨8458514636668858526119253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639009757779239017412835 8458514636668858526119253)
            ·
              refine ⟨3097600574951974557905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 8458514636668858526119253 3097600574951974557905)
              ·
                rfl

theorem cell23_488637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 13].length) (baseStart_488637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488637 prefixEnd_488637 := by exact prefixLift 488637
  have htrace : WordTrace (prefixWord ++ tailWord_488637) baseStart_488637 baseEnd_488637 := by
    simpa [prefixWord, tailWord_488637, baseEnd_488637] using wordTrace_append hprefix tailTrace_488637
  have hstable : (prefixWord ++ tailWord_488637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488637).length < 2 ^ (prefixWord ++ tailWord_488637).sum := by decide
  have hdescent : baseEnd_488637 < baseStart_488637 := by decide
  rcases family_descends (prefixWord ++ tailWord_488637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488648 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_488648 : Nat := 118140960795 + 488648 * 2 ^ 59
def prefixEnd_488648 : Nat := 4983230072969 + 3 ^ 40 * 488648 * 2
def baseEnd_488648 : Nat := 250911294858309396152755

theorem tailTrace_488648 : CollatzResearch.WordTrace tailWord_488648 prefixEnd_488648 250911294858309396152755 := by
  unfold tailWord_488648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911228366859612639681299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11881637822479483519575065 8911228366859612639681299)
  ·
    refine ⟨13366842550289418959521949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911228366859612639681299 13366842550289418959521949)
    ·
      refine ⟨5012565956358532109820731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13366842550289418959521949 5012565956358532109820731)
      ·
        refine ⟨7518848934537798164731097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012565956358532109820731 7518848934537798164731097)
        ·
          refine ⟨5639136700903348623548323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518848934537798164731097 5639136700903348623548323)
          ·
            refine ⟨8458705051355022935322485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639136700903348623548323 8458705051355022935322485)
            ·
              refine ⟨793003598564533400186483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8458705051355022935322485 793003598564533400186483)
              ·
                refine ⟨1189505397846800100279725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793003598564533400186483 1189505397846800100279725)
                ·
                  refine ⟨446064524192550037604897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189505397846800100279725 446064524192550037604897)
                  ·
                    refine ⟨334548393144412528203673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446064524192550037604897 334548393144412528203673)
                    ·
                      refine ⟨250911294858309396152755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334548393144412528203673 250911294858309396152755)
                      ·
                        rfl

theorem cell23_488648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_488648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488648 prefixEnd_488648 := by exact prefixLift 488648
  have htrace : WordTrace (prefixWord ++ tailWord_488648) baseStart_488648 baseEnd_488648 := by
    simpa [prefixWord, tailWord_488648, baseEnd_488648] using wordTrace_append hprefix tailTrace_488648
  have hstable : (prefixWord ++ tailWord_488648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488648).length < 2 ^ (prefixWord ++ tailWord_488648).sum := by decide
  have hdescent : baseEnd_488648 < baseStart_488648 := by decide
  rcases family_descends (prefixWord ++ tailWord_488648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488657 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_488657 : Nat := 118140960795 + 488657 * 2 ^ 59
def prefixEnd_488657 : Nat := 4983230072969 + 3 ^ 40 * 488657 * 2
def baseEnd_488657 : Nat := 250915916184199860940213

theorem tailTrace_488657 : CollatzResearch.WordTrace tailWord_488657 prefixEnd_488657 250915916184199860940213 := by
  unfold tailWord_488657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17822784990686619816440225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881856660457746544293483 17822784990686619816440225)
  ·
    refine ⟨13367088743014964862330169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17822784990686619816440225 13367088743014964862330169)
    ·
      refine ⟨10025316557261223646747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13367088743014964862330169 10025316557261223646747627)
      ·
        refine ⟨15037974835891835470121441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10025316557261223646747627 15037974835891835470121441)
        ·
          refine ⟨11278481126918876602591081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037974835891835470121441 11278481126918876602591081)
          ·
            refine ⟨8458860845189157451943311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278481126918876602591081 8458860845189157451943311)
            ·
              refine ⟨12688291267783736177914967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458860845189157451943311 12688291267783736177914967)
              ·
                refine ⟨19032436901675604266872451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688291267783736177914967 19032436901675604266872451)
                ·
                  refine ⟨28548655352513406400308677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032436901675604266872451 28548655352513406400308677)
                  ·
                    refine ⟨5352872878596263700057877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28548655352513406400308677 5352872878596263700057877)
                    ·
                      refine ⟨250915916184199860940213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5352872878596263700057877 250915916184199860940213)
                      ·
                        rfl

theorem cell23_488657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_488657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488657 prefixEnd_488657 := by exact prefixLift 488657
  have htrace : WordTrace (prefixWord ++ tailWord_488657) baseStart_488657 baseEnd_488657 := by
    simpa [prefixWord, tailWord_488657, baseEnd_488657] using wordTrace_append hprefix tailTrace_488657
  have hstable : (prefixWord ++ tailWord_488657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488657).length < 2 ^ (prefixWord ++ tailWord_488657).sum := by decide
  have hdescent : baseEnd_488657 < baseStart_488657 := by decide
  rcases family_descends (prefixWord ++ tailWord_488657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488662 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_488662 : Nat := 118140960795 + 488662 * 2 ^ 59
def prefixEnd_488662 : Nat := 4983230072969 + 3 ^ 40 * 488662 * 2
def baseEnd_488662 : Nat := 83639494529157447125897

theorem tailTrace_488662 : CollatzResearch.WordTrace tailWord_488662 prefixEnd_488662 83639494529157447125897 := by
  unfold tailWord_488662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113935459729281604398265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11881978237112337113581493 1113935459729281604398265)
  ·
    refine ⟨835451594796961203298699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1113935459729281604398265 835451594796961203298699)
    ·
      refine ⟨1253177392195441804948049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835451594796961203298699 1253177392195441804948049)
      ·
        refine ⟨939883044146581353711037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253177392195441804948049 939883044146581353711037)
        ·
          refine ⟨352456141554968007641639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939883044146581353711037 352456141554968007641639)
          ·
            refine ⟨528684212332452011462459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352456141554968007641639 528684212332452011462459)
            ·
              refine ⟨793026318498678017193689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528684212332452011462459 793026318498678017193689)
              ·
                refine ⟨594769738874008512895267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793026318498678017193689 594769738874008512895267)
                ·
                  refine ⟨892154608311012769342901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594769738874008512895267 892154608311012769342901)
                  ·
                    refine ⟨83639494529157447125897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 892154608311012769342901 83639494529157447125897)
                    ·
                      rfl

theorem cell23_488662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_488662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488662 prefixEnd_488662 := by exact prefixLift 488662
  have htrace : WordTrace (prefixWord ++ tailWord_488662) baseStart_488662 baseEnd_488662 := by
    simpa [prefixWord, tailWord_488662, baseEnd_488662] using wordTrace_append hprefix tailTrace_488662
  have hstable : (prefixWord ++ tailWord_488662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488662).length < 2 ^ (prefixWord ++ tailWord_488662).sum := by decide
  have hdescent : baseEnd_488662 < baseStart_488662 := by decide
  rcases family_descends (prefixWord ++ tailWord_488662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488685 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_488685 : Nat := 118140960795 + 488685 * 2 ^ 59
def prefixEnd_488685 : Nat := 4983230072969 + 3 ^ 40 * 488685 * 2
def baseEnd_488685 : Nat := 250930293642525751390085

theorem tailTrace_488685 : CollatzResearch.WordTrace tailWord_488685 prefixEnd_488685 250930293642525751390085 := by
  unfold tailWord_488685
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823806234585180598459509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11882537489723453732306339 17823806234585180598459509)
  ·
    refine ⟨1670981834492360681105579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17823806234585180598459509 1670981834492360681105579)
    ·
      refine ⟨2506472751738541021658369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670981834492360681105579 2506472751738541021658369)
      ·
        refine ⟨1879854563803905766243777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2506472751738541021658369 1879854563803905766243777)
        ·
          refine ⟨1409890922852929324682833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879854563803905766243777 1409890922852929324682833)
          ·
            refine ⟨1057418192139696993512125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409890922852929324682833 1057418192139696993512125)
            ·
              refine ⟨396531822052386372567047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057418192139696993512125 396531822052386372567047)
              ·
                refine ⟨594797733078579558850571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396531822052386372567047 594797733078579558850571)
                ·
                  refine ⟨892196599617869338275857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594797733078579558850571 892196599617869338275857)
                  ·
                    refine ⟨669147449713402003706893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892196599617869338275857 669147449713402003706893)
                    ·
                      refine ⟨250930293642525751390085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669147449713402003706893 250930293642525751390085)
                      ·
                        rfl

theorem cell23_488685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_488685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488685 prefixEnd_488685 := by exact prefixLift 488685
  have htrace : WordTrace (prefixWord ++ tailWord_488685) baseStart_488685 baseEnd_488685 := by
    simpa [prefixWord, tailWord_488685, baseEnd_488685] using wordTrace_append hprefix tailTrace_488685
  have hstable : (prefixWord ++ tailWord_488685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488685).length < 2 ^ (prefixWord ++ tailWord_488685).sum := by decide
  have hdescent : baseEnd_488685 < baseStart_488685 := by decide
  rcases family_descends (prefixWord ++ tailWord_488685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488698 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_488698 : Nat := 118140960795 + 488698 * 2 ^ 59
def prefixEnd_488698 : Nat := 4983230072969 + 3 ^ 40 * 488698 * 2
def baseEnd_488698 : Nat := 250936968891034200527525

theorem tailTrace_488698 : CollatzResearch.WordTrace tailWord_488698 prefixEnd_488698 250936968891034200527525 := by
  unfold tailWord_488698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456070095884520954670687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11882853589025389212455165 4456070095884520954670687)
  ·
    refine ⟨6684105143826781432006031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456070095884520954670687 6684105143826781432006031)
    ·
      refine ⟨10026157715740172148009047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684105143826781432006031 10026157715740172148009047)
      ·
        refine ⟨15039236573610258222013571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10026157715740172148009047 15039236573610258222013571)
        ·
          refine ⟨22558854860415387333020357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15039236573610258222013571 22558854860415387333020357)
          ·
            refine ⟨4229785286327885124941317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22558854860415387333020357 4229785286327885124941317)
            ·
              refine ⟨793084741186478460926497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4229785286327885124941317 793084741186478460926497)
              ·
                refine ⟨594813555889858845694873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793084741186478460926497 594813555889858845694873)
                ·
                  refine ⟨446110166917394134271155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594813555889858845694873 446110166917394134271155)
                  ·
                    refine ⟨669165250376091201406733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446110166917394134271155 669165250376091201406733)
                    ·
                      refine ⟨250936968891034200527525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669165250376091201406733 250936968891034200527525)
                      ·
                        rfl

theorem cell23_488698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_488698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488698 prefixEnd_488698 := by exact prefixLift 488698
  have htrace : WordTrace (prefixWord ++ tailWord_488698) baseStart_488698 baseEnd_488698 := by
    simpa [prefixWord, tailWord_488698, baseEnd_488698] using wordTrace_append hprefix tailTrace_488698
  have hstable : (prefixWord ++ tailWord_488698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488698).length < 2 ^ (prefixWord ++ tailWord_488698).sum := by decide
  have hdescent : baseEnd_488698 < baseStart_488698 := by decide
  rcases family_descends (prefixWord ++ tailWord_488698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488708 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_488708 : Nat := 118140960795 + 488708 * 2 ^ 59
def prefixEnd_488708 : Nat := 4983230072969 + 3 ^ 40 * 488708 * 2
def baseEnd_488708 : Nat := 250942103697579161402479

theorem tailTrace_488708 : CollatzResearch.WordTrace tailWord_488708 prefixEnd_488708 250942103697579161402479 := by
  unfold tailWord_488708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912322556750927763273389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11883096742334570351031185 8912322556750927763273389)
  ·
    refine ⟨3342120958781597911227521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8912322556750927763273389 3342120958781597911227521)
    ·
      refine ⟨2506590719086198433420641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3342120958781597911227521 2506590719086198433420641)
      ·
        refine ⟨1879943039314648825065481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2506590719086198433420641 1879943039314648825065481)
        ·
          refine ⟨1409957279485986618799111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879943039314648825065481 1409957279485986618799111)
          ·
            refine ⟨2114935919228979928198667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409957279485986618799111 2114935919228979928198667)
            ·
              refine ⟨3172403878843469892298001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114935919228979928198667 3172403878843469892298001)
              ·
                refine ⟨2379302909132602419223501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172403878843469892298001 2379302909132602419223501)
                ·
                  refine ⟨892238590924725907208813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2379302909132602419223501 892238590924725907208813)
                  ·
                    refine ⟨334589471596772215203305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892238590924725907208813 334589471596772215203305)
                    ·
                      refine ⟨250942103697579161402479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334589471596772215203305 250942103697579161402479)
                      ·
                        rfl

theorem cell23_488708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_488708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488708 prefixEnd_488708 := by exact prefixLift 488708
  have htrace : WordTrace (prefixWord ++ tailWord_488708) baseStart_488708 baseEnd_488708 := by
    simpa [prefixWord, tailWord_488708, baseEnd_488708] using wordTrace_append hprefix tailTrace_488708
  have hstable : (prefixWord ++ tailWord_488708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488708).length < 2 ^ (prefixWord ++ tailWord_488708).sum := by decide
  have hdescent : baseEnd_488708 < baseStart_488708 := by decide
  rcases family_descends (prefixWord ++ tailWord_488708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488755 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 2, 2, 2]
def baseStart_488755 : Nat := 118140960795 + 488755 * 2 ^ 59
def prefixEnd_488755 : Nat := 4983230072969 + 3 ^ 40 * 488755 * 2
def baseEnd_488755 : Nat := 250966237288340477514763

theorem tailTrace_488755 : CollatzResearch.WordTrace tailWord_488755 prefixEnd_488755 250966237288340477514763 := by
  unfold tailWord_488755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17826359344331582553507719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11884239562887721702338479 17826359344331582553507719)
  ·
    refine ⟨26739539016497373830261579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17826359344331582553507719 26739539016497373830261579)
    ·
      refine ⟨40109308524746060745392369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26739539016497373830261579 40109308524746060745392369)
      ·
        refine ⟨30081981393559545559044277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40109308524746060745392369 30081981393559545559044277)
        ·
          refine ⟨2820185755646207396160401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30081981393559545559044277 2820185755646207396160401)
          ·
            refine ⟨2115139316734655547120301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2820185755646207396160401 2115139316734655547120301)
            ·
              refine ⟨793177243775495830170113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115139316734655547120301 793177243775495830170113)
              ·
                refine ⟨594882932831621872627585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793177243775495830170113 594882932831621872627585)
                ·
                  refine ⟨446162199623716404470689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594882932831621872627585 446162199623716404470689)
                  ·
                    refine ⟨334621649717787303353017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446162199623716404470689 334621649717787303353017)
                    ·
                      refine ⟨250966237288340477514763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334621649717787303353017 250966237288340477514763)
                      ·
                        rfl

theorem cell23_488755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2, 2].length) (baseStart_488755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488755 prefixEnd_488755 := by exact prefixLift 488755
  have htrace : WordTrace (prefixWord ++ tailWord_488755) baseStart_488755 baseEnd_488755 := by
    simpa [prefixWord, tailWord_488755, baseEnd_488755] using wordTrace_append hprefix tailTrace_488755
  have hstable : (prefixWord ++ tailWord_488755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488755).length < 2 ^ (prefixWord ++ tailWord_488755).sum := by decide
  have hdescent : baseEnd_488755 < baseStart_488755 := by decide
  rcases family_descends (prefixWord ++ tailWord_488755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488772 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_488772 : Nat := 118140960795 + 488772 * 2 ^ 59
def prefixEnd_488772 : Nat := 4983230072969 + 3 ^ 40 * 488772 * 2
def baseEnd_488772 : Nat := 250974966459466911002185

theorem tailTrace_488772 : CollatzResearch.WordTrace tailWord_488772 prefixEnd_488772 250974966459466911002185 := by
  unfold tailWord_488772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913489692634997228438285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11884652923513329637917713 8913489692634997228438285)
  ·
    refine ⟨3342558634738123960664357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8913489692634997228438285 3342558634738123960664357)
    ·
      refine ⟨626729744013398242624567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3342558634738123960664357 626729744013398242624567)
      ·
        refine ⟨940094616020097363936851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626729744013398242624567 940094616020097363936851)
        ·
          refine ⟨1410141924030146045905277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940094616020097363936851 1410141924030146045905277)
          ·
            refine ⟨528803221511304767214479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410141924030146045905277 528803221511304767214479)
            ·
              refine ⟨793204832266957150821719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528803221511304767214479 793204832266957150821719)
              ·
                refine ⟨1189807248400435726232579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793204832266957150821719 1189807248400435726232579)
                ·
                  refine ⟨1784710872600653589348869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189807248400435726232579 1784710872600653589348869)
                  ·
                    refine ⟨334633288612622548002913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784710872600653589348869 334633288612622548002913)
                    ·
                      refine ⟨250974966459466911002185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334633288612622548002913 250974966459466911002185)
                      ·
                        rfl

theorem cell23_488772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_488772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488772 prefixEnd_488772 := by exact prefixLift 488772
  have htrace : WordTrace (prefixWord ++ tailWord_488772) baseStart_488772 baseEnd_488772 := by
    simpa [prefixWord, tailWord_488772, baseEnd_488772] using wordTrace_append hprefix tailTrace_488772
  have hstable : (prefixWord ++ tailWord_488772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488772).length < 2 ^ (prefixWord ++ tailWord_488772).sum := by decide
  have hdescent : baseEnd_488772 < baseStart_488772 := by decide
  rcases family_descends (prefixWord ++ tailWord_488772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488808 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_488808 : Nat := 118140960795 + 488808 * 2 ^ 59
def prefixEnd_488808 : Nat := 4983230072969 + 3 ^ 40 * 488808 * 2
def baseEnd_488808 : Nat := 83664483921009590050673

theorem tailTrace_488808 : CollatzResearch.WordTrace tailWord_488808 prefixEnd_488808 83664483921009590050673 := by
  unfold tailWord_488808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914146206569786302593539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11885528275426381736791385 8914146206569786302593539)
  ·
    refine ⟨13371219309854679453890309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8914146206569786302593539 13371219309854679453890309)
    ·
      refine ⟨2507103620597752397604433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13371219309854679453890309 2507103620597752397604433)
      ·
        refine ⟨1880327715448314298203325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2507103620597752397604433 1880327715448314298203325)
        ·
          refine ⟨705122893293117861826247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1880327715448314298203325 705122893293117861826247)
          ·
            refine ⟨1057684339939676792739371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705122893293117861826247 1057684339939676792739371)
            ·
              refine ⟨1586526509909515189109057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057684339939676792739371 1586526509909515189109057)
              ·
                refine ⟨1189894882432136391831793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586526509909515189109057 1189894882432136391831793)
                ·
                  refine ⟨892421161824102293873845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1189894882432136391831793 892421161824102293873845)
                  ·
                    refine ⟨83664483921009590050673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 892421161824102293873845 83664483921009590050673)
                    ·
                      rfl

theorem cell23_488808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_488808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488808 prefixEnd_488808 := by exact prefixLift 488808
  have htrace : WordTrace (prefixWord ++ tailWord_488808) baseStart_488808 baseEnd_488808 := by
    simpa [prefixWord, tailWord_488808, baseEnd_488808] using wordTrace_append hprefix tailTrace_488808
  have hstable : (prefixWord ++ tailWord_488808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488808).length < 2 ^ (prefixWord ++ tailWord_488808).sum := by decide
  have hdescent : baseEnd_488808 < baseStart_488808 := by decide
  rcases family_descends (prefixWord ++ tailWord_488808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488871 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_488871 : Nat := 118140960795 + 488871 * 2 ^ 59
def prefixEnd_488871 : Nat := 4983230072969 + 3 ^ 40 * 488871 * 2
def baseEnd_488871 : Nat := 251025801044262023664229

theorem tailTrace_488871 : CollatzResearch.WordTrace tailWord_488871 prefixEnd_488871 251025801044262023664229 := by
  unfold tailWord_488871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830590211911334364730467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11887060141274222909820311 17830590211911334364730467)
  ·
    refine ⟨26745885317867001547095701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17830590211911334364730467 26745885317867001547095701)
    ·
      refine ⟨1253713374275015697520111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26745885317867001547095701 1253713374275015697520111)
      ·
        refine ⟨1880570061412523546280167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253713374275015697520111 1880570061412523546280167)
        ·
          refine ⟨2820855092118785319420251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880570061412523546280167 2820855092118785319420251)
          ·
            refine ⟨4231282638178177979130377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820855092118785319420251 4231282638178177979130377)
            ·
              refine ⟨3173461978633633484347783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231282638178177979130377 3173461978633633484347783)
              ·
                refine ⟨4760192967950450226521675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173461978633633484347783 4760192967950450226521675)
                ·
                  refine ⟨7140289451925675339782513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760192967950450226521675 7140289451925675339782513)
                  ·
                    refine ⟨5355217088944256504836885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7140289451925675339782513 5355217088944256504836885)
                    ·
                      refine ⟨251025801044262023664229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5355217088944256504836885 251025801044262023664229)
                      ·
                        rfl

theorem cell23_488871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_488871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488871 prefixEnd_488871 := by exact prefixLift 488871
  have htrace : WordTrace (prefixWord ++ tailWord_488871) baseStart_488871 baseEnd_488871 := by
    simpa [prefixWord, tailWord_488871, baseEnd_488871] using wordTrace_append hprefix tailTrace_488871
  have hstable : (prefixWord ++ tailWord_488871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488871).length < 2 ^ (prefixWord ++ tailWord_488871).sum := by decide
  have hdescent : baseEnd_488871 < baseStart_488871 := by decide
  rcases family_descends (prefixWord ++ tailWord_488871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488881 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_488881 : Nat := 118140960795 + 488881 * 2 ^ 59
def prefixEnd_488881 : Nat := 4983230072969 + 3 ^ 40 * 488881 * 2
def baseEnd_488881 : Nat := 83676978616935661513061

theorem tailTrace_488881 : CollatzResearch.WordTrace tailWord_488881 prefixEnd_488881 83676978616935661513061 := by
  unfold tailWord_488881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830954941875106072594497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11887303294583404048396331 17830954941875106072594497)
  ·
    refine ⟨13373216206406329554445873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17830954941875106072594497 13373216206406329554445873)
    ·
      refine ⟨10029912154804747165834405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13373216206406329554445873 10029912154804747165834405)
      ·
        refine ⟨1880608529025890093593951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10029912154804747165834405 1880608529025890093593951)
        ·
          refine ⟨2820912793538835140390927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880608529025890093593951 2820912793538835140390927)
          ·
            refine ⟨4231369190308252710586391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820912793538835140390927 4231369190308252710586391)
            ·
              refine ⟨6347053785462379065879587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231369190308252710586391 6347053785462379065879587)
              ·
                refine ⟨9520580678193568598819381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347053785462379065879587 9520580678193568598819381)
                ·
                  refine ⟨892554438580647056139317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9520580678193568598819381 892554438580647056139317)
                  ·
                    refine ⟨83676978616935661513061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 892554438580647056139317 83676978616935661513061)
                    ·
                      rfl

theorem cell23_488881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_488881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488881 prefixEnd_488881 := by exact prefixLift 488881
  have htrace : WordTrace (prefixWord ++ tailWord_488881) baseStart_488881 baseEnd_488881 := by
    simpa [prefixWord, tailWord_488881, baseEnd_488881] using wordTrace_append hprefix tailTrace_488881
  have hstable : (prefixWord ++ tailWord_488881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488881).length < 2 ^ (prefixWord ++ tailWord_488881).sum := by decide
  have hdescent : baseEnd_488881 < baseStart_488881 := by decide
  rcases family_descends (prefixWord ++ tailWord_488881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488888 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_488888 : Nat := 118140960795 + 488888 * 2 ^ 59
def prefixEnd_488888 : Nat := 4983230072969 + 3 ^ 40 * 488888 * 2
def baseEnd_488888 : Nat := 251034530215388457151651

theorem tailTrace_488888 : CollatzResearch.WordTrace tailWord_488888 prefixEnd_488888 251034530215388457151651 := by
  unfold tailWord_488888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915605126424873134049659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11887473501899830845399545 8915605126424873134049659)
  ·
    refine ⟨13373407689637309701074489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8915605126424873134049659 13373407689637309701074489)
    ·
      refine ⟨10030055767227982275805867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13373407689637309701074489 10030055767227982275805867)
      ·
        refine ⟨15045083650841973413708801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030055767227982275805867 15045083650841973413708801)
        ·
          refine ⟨11283812738131480060281601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15045083650841973413708801 11283812738131480060281601)
          ·
            refine ⟨8462859553598610045211201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283812738131480060281601 8462859553598610045211201)
            ·
              refine ⟨6347144665198957533908401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462859553598610045211201 6347144665198957533908401)
              ·
                refine ⟨4760358498899218150431301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347144665198957533908401 4760358498899218150431301)
                ·
                  refine ⟨892567218543603403205869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4760358498899218150431301 892567218543603403205869)
                  ·
                    refine ⟨334712706953851276202201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892567218543603403205869 334712706953851276202201)
                    ·
                      refine ⟨251034530215388457151651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334712706953851276202201 251034530215388457151651)
                      ·
                        rfl

theorem cell23_488888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_488888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488888 prefixEnd_488888 := by exact prefixLift 488888
  have htrace : WordTrace (prefixWord ++ tailWord_488888) baseStart_488888 baseEnd_488888 := by
    simpa [prefixWord, tailWord_488888, baseEnd_488888] using wordTrace_append hprefix tailTrace_488888
  have hstable : (prefixWord ++ tailWord_488888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488888).length < 2 ^ (prefixWord ++ tailWord_488888).sum := by decide
  have hdescent : baseEnd_488888 < baseStart_488888 := by decide
  rcases family_descends (prefixWord ++ tailWord_488888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488911 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 6]
def baseStart_488911 : Nat := 118140960795 + 488911 * 2 ^ 59
def prefixEnd_488911 : Nat := 4983230072969 + 3 ^ 40 * 488911 * 2
def baseEnd_488911 : Nat := 83682113423480622388015

theorem tailTrace_488911 : CollatzResearch.WordTrace tailWord_488911 prefixEnd_488911 83682113423480622388015 := by
  unfold tailWord_488911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832049131766421196186587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11888032754510947464124391 17832049131766421196186587)
  ·
    refine ⟨26748073697649631794279881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832049131766421196186587 26748073697649631794279881)
    ·
      refine ⟨20061055273237223845709911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26748073697649631794279881 20061055273237223845709911)
      ·
        refine ⟨30091582909855835768564867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20061055273237223845709911 30091582909855835768564867)
        ·
          refine ⟨45137374364783753652847301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30091582909855835768564867 45137374364783753652847301)
          ·
            refine ⟨8463257693396953809908869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45137374364783753652847301 8463257693396953809908869)
            ·
              refine ⟨1586860817511928839357913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8463257693396953809908869 1586860817511928839357913)
              ·
                refine ⟨1190145613133946629518435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586860817511928839357913 1190145613133946629518435)
                ·
                  refine ⟨1785218419700919944277653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190145613133946629518435 1785218419700919944277653)
                  ·
                    refine ⟨83682113423480622388015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1785218419700919944277653 83682113423480622388015)
                    ·
                      rfl

theorem cell23_488911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_488911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488911 prefixEnd_488911 := by exact prefixLift 488911
  have htrace : WordTrace (prefixWord ++ tailWord_488911) baseStart_488911 baseEnd_488911 := by
    simpa [prefixWord, tailWord_488911, baseEnd_488911] using wordTrace_append hprefix tailTrace_488911
  have hstable : (prefixWord ++ tailWord_488911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488911).length < 2 ^ (prefixWord ++ tailWord_488911).sum := by decide
  have hdescent : baseEnd_488911 < baseStart_488911 := by decide
  rcases family_descends (prefixWord ++ tailWord_488911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488928 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_488928 : Nat := 118140960795 + 488928 * 2 ^ 59
def prefixEnd_488928 : Nat := 4983230072969 + 3 ^ 40 * 488928 * 2
def baseEnd_488928 : Nat := 83685023147189433550489

theorem tailTrace_488928 : CollatzResearch.WordTrace tailWord_488928 prefixEnd_488928 83685023147189433550489 := by
  unfold tailWord_488928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916334586352416549777719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11888446115136555399703625 8916334586352416549777719)
  ·
    refine ⟨13374501879528624824666579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8916334586352416549777719 13374501879528624824666579)
    ·
      refine ⟨20061752819292937236999869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13374501879528624824666579 20061752819292937236999869)
      ·
        refine ⟨7523157307234851463874951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20061752819292937236999869 7523157307234851463874951)
        ·
          refine ⟨11284735960852277195812427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523157307234851463874951 11284735960852277195812427)
          ·
            refine ⟨16927103941278415793718641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11284735960852277195812427 16927103941278415793718641)
            ·
              refine ⟨12695327955958811845288981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16927103941278415793718641 12695327955958811845288981)
              ·
                refine ⟨595093497935569305247921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12695327955958811845288981 595093497935569305247921)
                ·
                  refine ⟨446320123451676978935941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595093497935569305247921 446320123451676978935941)
                  ·
                    refine ⟨83685023147189433550489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446320123451676978935941 83685023147189433550489)
                    ·
                      rfl

theorem cell23_488928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_488928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488928 prefixEnd_488928 := by exact prefixLift 488928
  have htrace : WordTrace (prefixWord ++ tailWord_488928) baseStart_488928 baseEnd_488928 := by
    simpa [prefixWord, tailWord_488928, baseEnd_488928] using wordTrace_append hprefix tailTrace_488928
  have hstable : (prefixWord ++ tailWord_488928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488928).length < 2 ^ (prefixWord ++ tailWord_488928).sum := by decide
  have hdescent : baseEnd_488928 < baseStart_488928 := by decide
  rcases family_descends (prefixWord ++ tailWord_488928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488968 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_488968 : Nat := 118140960795 + 488968 * 2 ^ 59
def prefixEnd_488968 : Nat := 4983230072969 + 3 ^ 40 * 488968 * 2
def baseEnd_488968 : Nat := 251075608667748144151283

theorem tailTrace_488968 : CollatzResearch.WordTrace tailWord_488968 prefixEnd_488968 251075608667748144151283 := by
  unfold tailWord_488968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917064046279959965505779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11889418728373279954007705 8917064046279959965505779)
  ·
    refine ⟨13375596069419939948258669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8917064046279959965505779 13375596069419939948258669)
    ·
      refine ⟨5015848526032477480597001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13375596069419939948258669 5015848526032477480597001)
      ·
        refine ⟨3761886394524358110447751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015848526032477480597001 3761886394524358110447751)
        ·
          refine ⟨5642829591786537165671627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761886394524358110447751 5642829591786537165671627)
          ·
            refine ⟨8464244387679805748507441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642829591786537165671627 8464244387679805748507441)
            ·
              refine ⟨6348183290759854311380581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464244387679805748507441 6348183290759854311380581)
              ·
                refine ⟨1190284367017472683383859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6348183290759854311380581 1190284367017472683383859)
                ·
                  refine ⟨1785426550526209025075789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190284367017472683383859 1785426550526209025075789)
                  ·
                    refine ⟨669534956447328384403421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785426550526209025075789 669534956447328384403421)
                    ·
                      refine ⟨251075608667748144151283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669534956447328384403421 251075608667748144151283)
                      ·
                        rfl

theorem cell23_488968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_488968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_488968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_488968 prefixEnd_488968 := by exact prefixLift 488968
  have htrace : WordTrace (prefixWord ++ tailWord_488968) baseStart_488968 baseEnd_488968 := by
    simpa [prefixWord, tailWord_488968, baseEnd_488968] using wordTrace_append hprefix tailTrace_488968
  have hstable : (prefixWord ++ tailWord_488968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488968).length < 2 ^ (prefixWord ++ tailWord_488968).sum := by decide
  have hdescent : baseEnd_488968 < baseStart_488968 := by decide
  rcases family_descends (prefixWord ++ tailWord_488968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489002 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_489002 : Nat := 118140960795 + 489002 * 2 ^ 59
def prefixEnd_489002 : Nat := 4983230072969 + 3 ^ 40 * 489002 * 2
def baseEnd_489002 : Nat := 251093067010001011126127

theorem tailTrace_489002 : CollatzResearch.WordTrace tailWord_489002 prefixEnd_489002 251093067010001011126127 := by
  unfold tailWord_489002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458842043609185934437315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11890245449624495825166173 4458842043609185934437315)
  ·
    refine ⟨6688263065413778901655973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4458842043609185934437315 6688263065413778901655973)
    ·
      refine ⟨1254049324765083544060495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6688263065413778901655973 1254049324765083544060495)
      ·
        refine ⟨1881073987147625316090743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254049324765083544060495 1881073987147625316090743)
        ·
          refine ⟨2821610980721437974136115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881073987147625316090743 2821610980721437974136115)
          ·
            refine ⟨4232416471082156961204173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821610980721437974136115 4232416471082156961204173)
            ·
              refine ⟨1587156176655808860451565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4232416471082156961204173 1587156176655808860451565)
              ·
                refine ⟨595183566245928322669337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587156176655808860451565 595183566245928322669337)
                ·
                  refine ⟨446387674684446242002003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595183566245928322669337 446387674684446242002003)
                  ·
                    refine ⟨669581512026669363003005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446387674684446242002003 669581512026669363003005)
                    ·
                      refine ⟨251093067010001011126127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669581512026669363003005 251093067010001011126127)
                      ·
                        rfl

theorem cell23_489002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_489002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489002 prefixEnd_489002 := by exact prefixLift 489002
  have htrace : WordTrace (prefixWord ++ tailWord_489002) baseStart_489002 baseEnd_489002 := by
    simpa [prefixWord, tailWord_489002, baseEnd_489002] using wordTrace_append hprefix tailTrace_489002
  have hstable : (prefixWord ++ tailWord_489002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489002).length < 2 ^ (prefixWord ++ tailWord_489002).sum := by decide
  have hdescent : baseEnd_489002 < baseStart_489002 := by decide
  rcases family_descends (prefixWord ++ tailWord_489002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489038 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_489038 : Nat := 118140960795 + 489038 * 2 ^ 59
def prefixEnd_489038 : Nat := 4983230072969 + 3 ^ 40 * 489038 * 2
def baseEnd_489038 : Nat := 251111552313562870275961

theorem tailTrace_489038 : CollatzResearch.WordTrace tailWord_489038 prefixEnd_489038 251111552313562870275961 := by
  unfold tailWord_489038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229585150288290235757471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11891120801537547924039845 2229585150288290235757471)
  ·
    refine ⟨3344377725432435353636207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229585150288290235757471 3344377725432435353636207)
    ·
      refine ⟨5016566588148653030454311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344377725432435353636207 5016566588148653030454311)
      ·
        refine ⟨7524849882222979545681467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016566588148653030454311 7524849882222979545681467)
        ·
          refine ⟨11287274823334469318522201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524849882222979545681467 11287274823334469318522201)
          ·
            refine ⟨8465456117500851988891651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11287274823334469318522201 8465456117500851988891651)
            ·
              refine ⟨12698184176251277983337477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465456117500851988891651 12698184176251277983337477)
              ·
                refine ⟨2380909533047114621875777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12698184176251277983337477 2380909533047114621875777)
                ·
                  refine ⟨1785682149785335966406833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380909533047114621875777 1785682149785335966406833)
                  ·
                    refine ⟨1339261612339001974805125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785682149785335966406833 1339261612339001974805125)
                    ·
                      refine ⟨251111552313562870275961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1339261612339001974805125 251111552313562870275961)
                      ·
                        rfl

theorem cell23_489038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_489038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489038 prefixEnd_489038 := by exact prefixLift 489038
  have htrace : WordTrace (prefixWord ++ tailWord_489038) baseStart_489038 baseEnd_489038 := by
    simpa [prefixWord, tailWord_489038, baseEnd_489038] using wordTrace_append hprefix tailTrace_489038
  have hstable : (prefixWord ++ tailWord_489038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489038).length < 2 ^ (prefixWord ++ tailWord_489038).sum := by decide
  have hdescent : baseEnd_489038 < baseStart_489038 := by decide
  rcases family_descends (prefixWord ++ tailWord_489038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489125 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_489125 : Nat := 118140960795 + 489125 * 2 ^ 59
def prefixEnd_489125 : Nat := 4983230072969 + 3 ^ 40 * 489125 * 2
def baseEnd_489125 : Nat := 83718741710168009962687

theorem tailTrace_489125 : CollatzResearch.WordTrace tailWord_489125 prefixEnd_489125 83718741710168009962687 := by
  unfold tailWord_489125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17839854352991135744476829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11893236235327423829651219 17839854352991135744476829)
  ·
    refine ⟨6689945382371675904178811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17839854352991135744476829 6689945382371675904178811)
    ·
      refine ⟨10034918073557513856268217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689945382371675904178811 10034918073557513856268217)
      ·
        refine ⟨7526188555168135392201163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10034918073557513856268217 7526188555168135392201163)
        ·
          refine ⟨11289282832752203088301745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526188555168135392201163 11289282832752203088301745)
          ·
            refine ⟨8466962124564152316226309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11289282832752203088301745 8466962124564152316226309)
            ·
              refine ⟨1587555398355778559292433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8466962124564152316226309 1587555398355778559292433)
              ·
                refine ⟨1190666548766833919469325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587555398355778559292433 1190666548766833919469325)
                ·
                  refine ⟨446499955787562719800997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190666548766833919469325 446499955787562719800997)
                  ·
                    refine ⟨83718741710168009962687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446499955787562719800997 83718741710168009962687)
                    ·
                      rfl

theorem cell23_489125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_489125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489125 prefixEnd_489125 := by exact prefixLift 489125
  have htrace : WordTrace (prefixWord ++ tailWord_489125) baseStart_489125 baseEnd_489125 := by
    simpa [prefixWord, tailWord_489125, baseEnd_489125] using wordTrace_append hprefix tailTrace_489125
  have hstable : (prefixWord ++ tailWord_489125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489125).length < 2 ^ (prefixWord ++ tailWord_489125).sum := by decide
  have hdescent : baseEnd_489125 < baseStart_489125 := by decide
  rcases family_descends (prefixWord ++ tailWord_489125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489135 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_489135 : Nat := 118140960795 + 489135 * 2 ^ 59
def prefixEnd_489135 : Nat := 4983230072969 + 3 ^ 40 * 489135 * 2
def baseEnd_489135 : Nat := 251161359937048990763015

theorem tailTrace_489135 : CollatzResearch.WordTrace tailWord_489135 prefixEnd_489135 251161359937048990763015 := by
  unfold tailWord_489135
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840219082954907452340859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11893479388636604968227239 17840219082954907452340859)
  ·
    refine ⟨26760328624432361178511289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17840219082954907452340859 26760328624432361178511289)
    ·
      refine ⟨20070246468324270883883467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26760328624432361178511289 20070246468324270883883467)
      ·
        refine ⟨30105369702486406325825201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20070246468324270883883467 30105369702486406325825201)
        ·
          refine ⟨22579027276864804744368901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30105369702486406325825201 22579027276864804744368901)
          ·
            refine ⟨4233567614412150889569169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22579027276864804744368901 4233567614412150889569169)
            ·
              refine ⟨3175175710809113167176877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233567614412150889569169 3175175710809113167176877)
              ·
                refine ⟨1190690891553417437691329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175175710809113167176877 1190690891553417437691329)
                ·
                  refine ⟨893018168665063078268497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1190690891553417437691329 893018168665063078268497)
                  ·
                    refine ⟨669763626498797308701373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893018168665063078268497 669763626498797308701373)
                    ·
                      refine ⟨251161359937048990763015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669763626498797308701373 251161359937048990763015)
                      ·
                        rfl

theorem cell23_489135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_489135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489135 prefixEnd_489135 := by exact prefixLift 489135
  have htrace : WordTrace (prefixWord ++ tailWord_489135) baseStart_489135 baseEnd_489135 := by
    simpa [prefixWord, tailWord_489135, baseEnd_489135] using wordTrace_append hprefix tailTrace_489135
  have hstable : (prefixWord ++ tailWord_489135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489135).length < 2 ^ (prefixWord ++ tailWord_489135).sum := by decide
  have hdescent : baseEnd_489135 < baseStart_489135 := by decide
  rcases family_descends (prefixWord ++ tailWord_489135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489138 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_489138 : Nat := 118140960795 + 489138 * 2 ^ 59
def prefixEnd_489138 : Nat := 4983230072969 + 3 ^ 40 * 489138 * 2
def baseEnd_489138 : Nat := 27906988931001386558389

theorem tailTrace_489138 : CollatzResearch.WordTrace tailWord_489138 prefixEnd_489138 27906988931001386558389 := by
  unfold tailWord_489138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460082125486009741175017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11893552334629359309800045 4460082125486009741175017)
  ·
    refine ⟨3345061594114507305881263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4460082125486009741175017 3345061594114507305881263)
    ·
      refine ⟨5017592391171760958821895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345061594114507305881263 5017592391171760958821895)
      ·
        refine ⟨7526388586757641438232843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017592391171760958821895 7526388586757641438232843)
        ·
          refine ⟨11289582880136462157349265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526388586757641438232843 11289582880136462157349265)
          ·
            refine ⟨8467187160102346618011949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11289582880136462157349265 8467187160102346618011949)
            ·
              refine ⟨3175195185038379981754481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8467187160102346618011949 3175195185038379981754481)
              ·
                refine ⟨2381396388778784986315861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175195185038379981754481 2381396388778784986315861)
                ·
                  refine ⟨27906988931001386558389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2381396388778784986315861 27906988931001386558389)
                  ·
                    rfl

theorem cell23_489138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_489138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489138 prefixEnd_489138 := by exact prefixLift 489138
  have htrace : WordTrace (prefixWord ++ tailWord_489138) baseStart_489138 baseEnd_489138 := by
    simpa [prefixWord, tailWord_489138, baseEnd_489138] using wordTrace_append hprefix tailTrace_489138
  have hstable : (prefixWord ++ tailWord_489138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489138).length < 2 ^ (prefixWord ++ tailWord_489138).sum := by decide
  have hdescent : baseEnd_489138 < baseStart_489138 := by decide
  rcases family_descends (prefixWord ++ tailWord_489138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489159 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 1, 4]
def baseStart_489159 : Nat := 118140960795 + 489159 * 2 ^ 59
def prefixEnd_489159 : Nat := 4983230072969 + 3 ^ 40 * 489159 * 2
def baseEnd_489159 : Nat := 83724561157585632287635

theorem tailTrace_489159 : CollatzResearch.WordTrace tailWord_489159 prefixEnd_489159 83724561157585632287635 := by
  unfold tailWord_489159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17841094434867959551214531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11894062956578639700809687 17841094434867959551214531)
  ·
    refine ⟨26761641652301939326821797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17841094434867959551214531 26761641652301939326821797)
    ·
      refine ⟨5017807809806613623779087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26761641652301939326821797 5017807809806613623779087)
      ·
        refine ⟨7526711714709920435668631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017807809806613623779087 7526711714709920435668631)
        ·
          refine ⟨11290067572064880653502947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526711714709920435668631 11290067572064880653502947)
          ·
            refine ⟨16935101358097320980254421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290067572064880653502947 16935101358097320980254421)
            ·
              refine ⟨396916438080405960474713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16935101358097320980254421 396916438080405960474713)
              ·
                refine ⟨297687328560304470356035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396916438080405960474713 297687328560304470356035)
                ·
                  refine ⟨446530992840456705534053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297687328560304470356035 446530992840456705534053)
                  ·
                    refine ⟨83724561157585632287635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446530992840456705534053 83724561157585632287635)
                    ·
                      rfl

theorem cell23_489159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_489159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489159 prefixEnd_489159 := by exact prefixLift 489159
  have htrace : WordTrace (prefixWord ++ tailWord_489159) baseStart_489159 baseEnd_489159 := by
    simpa [prefixWord, tailWord_489159, baseEnd_489159] using wordTrace_append hprefix tailTrace_489159
  have hstable : (prefixWord ++ tailWord_489159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489159).length < 2 ^ (prefixWord ++ tailWord_489159).sum := by decide
  have hdescent : baseEnd_489159 < baseStart_489159 := by decide
  rcases family_descends (prefixWord ++ tailWord_489159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489172 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 6]
def baseStart_489172 : Nat := 118140960795 + 489172 * 2 ^ 59
def prefixEnd_489172 : Nat := 4983230072969 + 3 ^ 40 * 489172 * 2
def baseEnd_489172 : Nat := 27908928746807260666705

theorem tailTrace_489172 : CollatzResearch.WordTrace tailWord_489172 prefixEnd_489172 27908928746807260666705 := by
  unfold tailWord_489172
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920784291910431385718885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11894379055880575180958513 8920784291910431385718885)
  ·
    refine ⟨1672647054733205884822291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8920784291910431385718885 1672647054733205884822291)
    ·
      refine ⟨2508970582099808827233437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1672647054733205884822291 2508970582099808827233437)
      ·
        refine ⟨940863968287428310212539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2508970582099808827233437 940863968287428310212539)
        ·
          refine ⟨1411295952431142465318809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940863968287428310212539 1411295952431142465318809)
          ·
            refine ⟨1058471964323356848989107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411295952431142465318809 1058471964323356848989107)
            ·
              refine ⟨1587707946485035273483661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058471964323356848989107 1587707946485035273483661)
              ·
                refine ⟨595390479931888227556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587707946485035273483661 595390479931888227556373)
                ·
                  refine ⟨27908928746807260666705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 595390479931888227556373 27908928746807260666705)
                  ·
                    rfl

theorem cell23_489172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_489172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489172 prefixEnd_489172 := by exact prefixLift 489172
  have htrace : WordTrace (prefixWord ++ tailWord_489172) baseStart_489172 baseEnd_489172 := by
    simpa [prefixWord, tailWord_489172, baseEnd_489172] using wordTrace_append hprefix tailTrace_489172
  have hstable : (prefixWord ++ tailWord_489172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489172).length < 2 ^ (prefixWord ++ tailWord_489172).sum := by decide
  have hdescent : baseEnd_489172 < baseStart_489172 := by decide
  rcases family_descends (prefixWord ++ tailWord_489172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489199 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 1, 1, 3]
def baseStart_489199 : Nat := 118140960795 + 489199 * 2 ^ 59
def prefixEnd_489199 : Nat := 4983230072969 + 3 ^ 40 * 489199 * 2
def baseEnd_489199 : Nat := 251194222698936740362721

theorem tailTrace_489199 : CollatzResearch.WordTrace tailWord_489199 prefixEnd_489199 251194222698936740362721 := by
  unfold tailWord_489199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842553354723046382670651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11895035569815364255113767 17842553354723046382670651)
  ·
    refine ⟨26763830032084569574005977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842553354723046382670651 26763830032084569574005977)
    ·
      refine ⟨20072872524063427180504483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26763830032084569574005977 20072872524063427180504483)
      ·
        refine ⟨30109308786095140770756725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20072872524063427180504483 30109308786095140770756725)
        ·
          refine ⟨2822747698696419447258443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30109308786095140770756725 2822747698696419447258443)
          ·
            refine ⟨4234121548044629170887665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822747698696419447258443 4234121548044629170887665)
            ·
              refine ⟨3175591161033471878165749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234121548044629170887665 3175591161033471878165749)
              ·
                refine ⟨297711671346887988578039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3175591161033471878165749 297711671346887988578039)
                ·
                  refine ⟨446567507020331982867059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297711671346887988578039 446567507020331982867059)
                  ·
                    refine ⟨669851260530497974300589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446567507020331982867059 669851260530497974300589)
                    ·
                      refine ⟨251194222698936740362721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669851260530497974300589 251194222698936740362721)
                      ·
                        rfl

theorem cell23_489199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 1, 3].length) (baseStart_489199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489199 prefixEnd_489199 := by exact prefixLift 489199
  have htrace : WordTrace (prefixWord ++ tailWord_489199) baseStart_489199 baseEnd_489199 := by
    simpa [prefixWord, tailWord_489199, baseEnd_489199] using wordTrace_append hprefix tailTrace_489199
  have hstable : (prefixWord ++ tailWord_489199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489199).length < 2 ^ (prefixWord ++ tailWord_489199).sum := by decide
  have hdescent : baseEnd_489199 < baseStart_489199 := by decide
  rcases family_descends (prefixWord ++ tailWord_489199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489215 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 4, 4]
def baseStart_489215 : Nat := 118140960795 + 489215 * 2 ^ 59
def prefixEnd_489215 : Nat := 4983230072969 + 3 ^ 40 * 489215 * 2
def baseEnd_489215 : Nat := 83734146129802892587549

theorem tailTrace_489215 : CollatzResearch.WordTrace tailWord_489215 prefixEnd_489215 83734146129802892587549 := by
  unfold tailWord_489215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17843136922665081115253099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11895424615110054076835399 17843136922665081115253099)
  ·
    refine ⟨26764705383997621672879649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17843136922665081115253099 26764705383997621672879649)
    ·
      refine ⟨20073529037998216254659737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26764705383997621672879649 20073529037998216254659737)
      ·
        refine ⟨15055146778498662190994803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20073529037998216254659737 15055146778498662190994803)
        ·
          refine ⟨22582720167747993286492205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055146778498662190994803 22582720167747993286492205)
          ·
            refine ⟨8468520062905497482434577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22582720167747993286492205 8468520062905497482434577)
            ·
              refine ⟨6351390047179123111825933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8468520062905497482434577 6351390047179123111825933)
              ·
                refine ⟨2381771267692171166934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6351390047179123111825933 2381771267692171166934725)
                ·
                  refine ⟨446582112692282093800261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381771267692171166934725 446582112692282093800261)
                  ·
                    refine ⟨83734146129802892587549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446582112692282093800261 83734146129802892587549)
                    ·
                      rfl

theorem cell23_489215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_489215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489215 prefixEnd_489215 := by exact prefixLift 489215
  have htrace : WordTrace (prefixWord ++ tailWord_489215) baseStart_489215 baseEnd_489215 := by
    simpa [prefixWord, tailWord_489215, baseEnd_489215] using wordTrace_append hprefix tailTrace_489215
  have hstable : (prefixWord ++ tailWord_489215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489215).length < 2 ^ (prefixWord ++ tailWord_489215).sum := by decide
  have hdescent : baseEnd_489215 < baseStart_489215 := by decide
  rcases family_descends (prefixWord ++ tailWord_489215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489239 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_489239 : Nat := 118140960795 + 489239 * 2 ^ 59
def prefixEnd_489239 : Nat := 4983230072969 + 3 ^ 40 * 489239 * 2
def baseEnd_489239 : Nat := 251214761925116583862537

theorem tailTrace_489239 : CollatzResearch.WordTrace tailWord_489239 prefixEnd_489239 251214761925116583862537 := by
  unfold tailWord_489239
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844012274578133214126771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896008183052088809417847 17844012274578133214126771)
  ·
    refine ⟨26766018411867199821190157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17844012274578133214126771 26766018411867199821190157)
    ·
      refine ⟨10037256904450199932946309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26766018411867199821190157 10037256904450199932946309)
      ·
        refine ⟨1881985669584412487427433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10037256904450199932946309 1881985669584412487427433)
        ·
          refine ⟨1411489252188309365570575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881985669584412487427433 1411489252188309365570575)
          ·
            refine ⟨2117233878282464048355863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411489252188309365570575 2117233878282464048355863)
            ·
              refine ⟨3175850817423696072533795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117233878282464048355863 3175850817423696072533795)
              ·
                refine ⟨4763776226135544108800693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175850817423696072533795 4763776226135544108800693)
                ·
                  refine ⟨446604021200207260200065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763776226135544108800693 446604021200207260200065)
                  ·
                    refine ⟨334953015900155445150049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446604021200207260200065 334953015900155445150049)
                    ·
                      refine ⟨251214761925116583862537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334953015900155445150049 251214761925116583862537)
                      ·
                        rfl

theorem cell23_489239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_489239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489239 prefixEnd_489239 := by exact prefixLift 489239
  have htrace : WordTrace (prefixWord ++ tailWord_489239) baseStart_489239 baseEnd_489239 := by
    simpa [prefixWord, tailWord_489239, baseEnd_489239] using wordTrace_append hprefix tailTrace_489239
  have hstable : (prefixWord ++ tailWord_489239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489239).length < 2 ^ (prefixWord ++ tailWord_489239).sum := by decide
  have hdescent : baseEnd_489239 < baseStart_489239 := by decide
  rcases family_descends (prefixWord ++ tailWord_489239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489242 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_489242 : Nat := 118140960795 + 489242 * 2 ^ 59
def prefixEnd_489242 : Nat := 4983230072969 + 3 ^ 40 * 489242 * 2
def baseEnd_489242 : Nat := 251216302367080072125023

theorem tailTrace_489242 : CollatzResearch.WordTrace tailWord_489242 prefixEnd_489242 251216302367080072125023 := by
  unfold tailWord_489242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461030423391816181621495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11896081129044843150990653 4461030423391816181621495)
  ·
    refine ⟨6691545635087724272432243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461030423391816181621495 6691545635087724272432243)
    ·
      refine ⟨10037318452631586408648365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691545635087724272432243 10037318452631586408648365)
      ·
        refine ⟨3763994419736844903243137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10037318452631586408648365 3763994419736844903243137)
        ·
          refine ⟨2822995814802633677432353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763994419736844903243137 2822995814802633677432353)
          ·
            refine ⟨2117246861101975258074265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822995814802633677432353 2117246861101975258074265)
            ·
              refine ⟨1587935145826481443555699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117246861101975258074265 1587935145826481443555699)
              ·
                refine ⟨2381902718739722165333549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587935145826481443555699 2381902718739722165333549)
                ·
                  refine ⟨893213519527395812000081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2381902718739722165333549 893213519527395812000081)
                  ·
                    refine ⟨669910139645546859000061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893213519527395812000081 669910139645546859000061)
                    ·
                      refine ⟨251216302367080072125023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 669910139645546859000061 251216302367080072125023)
                      ·
                        rfl

theorem cell23_489242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_489242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489242 prefixEnd_489242 := by exact prefixLift 489242
  have htrace : WordTrace (prefixWord ++ tailWord_489242) baseStart_489242 baseEnd_489242 := by
    simpa [prefixWord, tailWord_489242, baseEnd_489242] using wordTrace_append hprefix tailTrace_489242
  have hstable : (prefixWord ++ tailWord_489242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489242).length < 2 ^ (prefixWord ++ tailWord_489242).sum := by decide
  have hdescent : baseEnd_489242 < baseStart_489242 := by decide
  rcases family_descends (prefixWord ++ tailWord_489242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489252 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_489252 : Nat := 118140960795 + 489252 * 2 ^ 59
def prefixEnd_489252 : Nat := 4983230072969 + 3 ^ 40 * 489252 * 2
def baseEnd_489252 : Nat := 251221437173625032999977

theorem tailTrace_489252 : CollatzResearch.WordTrace tailWord_489252 prefixEnd_489252 251221437173625032999977 := by
  unfold tailWord_489252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922243211765518217175005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11896324282354024289566673 8922243211765518217175005)
  ·
    refine ⟨3345841204412069331440627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8922243211765518217175005 3345841204412069331440627)
    ·
      refine ⟨5018761806618103997160941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345841204412069331440627 5018761806618103997160941)
      ·
        refine ⟨1882035677481788998935353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5018761806618103997160941 1882035677481788998935353)
        ·
          refine ⟨1411526758111341749201515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882035677481788998935353 1411526758111341749201515)
          ·
            refine ⟨2117290137167012623802273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411526758111341749201515 2117290137167012623802273)
            ·
              refine ⟨1587967602875259467851705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117290137167012623802273 1587967602875259467851705)
              ·
                refine ⟨1190975702156444600888779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587967602875259467851705 1190975702156444600888779)
                ·
                  refine ⟨1786463553234666901333169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190975702156444600888779 1786463553234666901333169)
                  ·
                    refine ⟨1339847664926000175999877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786463553234666901333169 1339847664926000175999877)
                    ·
                      refine ⟨251221437173625032999977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1339847664926000175999877 251221437173625032999977)
                      ·
                        rfl

theorem cell23_489252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_489252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489252 prefixEnd_489252 := by exact prefixLift 489252
  have htrace : WordTrace (prefixWord ++ tailWord_489252) baseStart_489252 baseEnd_489252 := by
    simpa [prefixWord, tailWord_489252, baseEnd_489252] using wordTrace_append hprefix tailTrace_489252
  have hstable : (prefixWord ++ tailWord_489252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489252).length < 2 ^ (prefixWord ++ tailWord_489252).sum := by decide
  have hdescent : baseEnd_489252 < baseStart_489252 := by decide
  rcases family_descends (prefixWord ++ tailWord_489252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489256 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_489256 : Nat := 118140960795 + 489256 * 2 ^ 59
def prefixEnd_489256 : Nat := 4983230072969 + 3 ^ 40 * 489256 * 2
def baseEnd_489256 : Nat := 251223491096243017349959

theorem tailTrace_489256 : CollatzResearch.WordTrace tailWord_489256 prefixEnd_489256 251223491096243017349959 := by
  unfold tailWord_489256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922316157758272558747811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11896421543677696744997081 8922316157758272558747811)
  ·
    refine ⟨13383474236637408838121717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922316157758272558747811 13383474236637408838121717)
    ·
      refine ⟨1254700709684757078573911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13383474236637408838121717 1254700709684757078573911)
      ·
        refine ⟨1882051064527135617860867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254700709684757078573911 1882051064527135617860867)
        ·
          refine ⟨2823076596790703426791301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882051064527135617860867 2823076596790703426791301)
          ·
            refine ⟨529326861898256892523369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2823076596790703426791301 529326861898256892523369)
            ·
              refine ⟨396995146423692669392527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529326861898256892523369 396995146423692669392527)
              ·
                refine ⟨595492719635539004088791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396995146423692669392527 595492719635539004088791)
                ·
                  refine ⟨893239079453308506133187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595492719635539004088791 893239079453308506133187)
                  ·
                    refine ⟨1339858619179962759199781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 893239079453308506133187 1339858619179962759199781)
                    ·
                      refine ⟨251223491096243017349959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1339858619179962759199781 251223491096243017349959)
                      ·
                        rfl

theorem cell23_489256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_489256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489256 prefixEnd_489256 := by exact prefixLift 489256
  have htrace : WordTrace (prefixWord ++ tailWord_489256) baseStart_489256 baseEnd_489256 := by
    simpa [prefixWord, tailWord_489256, baseEnd_489256] using wordTrace_append hprefix tailTrace_489256
  have hstable : (prefixWord ++ tailWord_489256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489256).length < 2 ^ (prefixWord ++ tailWord_489256).sum := by decide
  have hdescent : baseEnd_489256 < baseStart_489256 := by decide
  rcases family_descends (prefixWord ++ tailWord_489256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489262 : List Nat := [4, 1, 3, 2, 2, 1, 10]
def baseStart_489262 : Nat := 118140960795 + 489262 * 2 ^ 59
def prefixEnd_489262 : Nat := 4983230072969 + 3 ^ 40 * 489262 * 2
def baseEnd_489262 : Nat := 3101562617039135726851

theorem tailTrace_489262 : CollatzResearch.WordTrace tailWord_489262 prefixEnd_489262 3101562617039135726851 := by
  unfold tailWord_489262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230606394186851017776755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11896567435663205428142693 2230606394186851017776755)
  ·
    refine ⟨3345909591280276526665133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230606394186851017776755 3345909591280276526665133)
    ·
      refine ⟨1254716096730103697499425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3345909591280276526665133 1254716096730103697499425)
      ·
        refine ⟨941037072547577773124569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254716096730103697499425 941037072547577773124569)
        ·
          refine ⟨705777804410683329843427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941037072547577773124569 705777804410683329843427)
          ·
            refine ⟨1058666706616024994765141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705777804410683329843427 1058666706616024994765141)
            ·
              refine ⟨3101562617039135726851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1058666706616024994765141 3101562617039135726851)
              ·
                rfl

theorem cell23_489262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 10].length) (baseStart_489262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489262 prefixEnd_489262 := by exact prefixLift 489262
  have htrace : WordTrace (prefixWord ++ tailWord_489262) baseStart_489262 baseEnd_489262 := by
    simpa [prefixWord, tailWord_489262, baseEnd_489262] using wordTrace_append hprefix tailTrace_489262
  have hstable : (prefixWord ++ tailWord_489262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489262).length < 2 ^ (prefixWord ++ tailWord_489262).sum := by decide
  have hdescent : baseEnd_489262 < baseStart_489262 := by decide
  rcases family_descends (prefixWord ++ tailWord_489262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489273 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 3, 2, 2]
def baseStart_489273 : Nat := 118140960795 + 489273 * 2 ^ 59
def prefixEnd_489273 : Nat := 4983230072969 + 3 ^ 40 * 489273 * 2
def baseEnd_489273 : Nat := 251232220267369450837381

theorem tailTrace_489273 : CollatzResearch.WordTrace tailWord_489273 prefixEnd_489273 251232220267369450837381 := by
  unfold tailWord_489273
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845252356454957020864473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896834904303304680576315 17845252356454957020864473)
  ·
    refine ⟨13383939267341217765648355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17845252356454957020864473 13383939267341217765648355)
    ·
      refine ⟨20075908901011826648472533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383939267341217765648355 20075908901011826648472533)
      ·
        refine ⟨470529114867464687073575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20075908901011826648472533 470529114867464687073575)
        ·
          refine ⟨705793672301197030610363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470529114867464687073575 705793672301197030610363)
          ·
            refine ⟨1058690508451795545915545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705793672301197030610363 1058690508451795545915545)
            ·
              refine ⟨794017881338846659436659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058690508451795545915545 794017881338846659436659)
              ·
                refine ⟨1191026822008269989154989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794017881338846659436659 1191026822008269989154989)
                ·
                  refine ⟨446635058253101245933121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191026822008269989154989 446635058253101245933121)
                  ·
                    refine ⟨334976293689825934449841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446635058253101245933121 334976293689825934449841)
                    ·
                      refine ⟨251232220267369450837381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334976293689825934449841 251232220267369450837381)
                      ·
                        rfl

theorem cell23_489273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_489273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489273 prefixEnd_489273 := by exact prefixLift 489273
  have htrace : WordTrace (prefixWord ++ tailWord_489273) baseStart_489273 baseEnd_489273 := by
    simpa [prefixWord, tailWord_489273, baseEnd_489273] using wordTrace_append hprefix tailTrace_489273
  have hstable : (prefixWord ++ tailWord_489273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489273).length < 2 ^ (prefixWord ++ tailWord_489273).sum := by decide
  have hdescent : baseEnd_489273 < baseStart_489273 := by decide
  rcases family_descends (prefixWord ++ tailWord_489273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489286 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_489286 : Nat := 118140960795 + 489286 * 2 ^ 59
def prefixEnd_489286 : Nat := 4983230072969 + 3 ^ 40 * 489286 * 2
def baseEnd_489286 : Nat := 251238895515877899974821

theorem tailTrace_489286 : CollatzResearch.WordTrace tailWord_489286 prefixEnd_489286 251238895515877899974821 := by
  unfold tailWord_489286
  simp only [CollatzResearch.WordTrace]
  refine ⟨557678953293995632533991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11897151003605240160725141 557678953293995632533991)
  ·
    refine ⟨836518429940993448800987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557678953293995632533991 836518429940993448800987)
    ·
      refine ⟨1254777644911490173201481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836518429940993448800987 1254777644911490173201481)
      ·
        refine ⟨941083233683617629901111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254777644911490173201481 941083233683617629901111)
        ·
          refine ⟨1411624850525426444851667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941083233683617629901111 1411624850525426444851667)
          ·
            refine ⟨2117437275788139667277501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411624850525426444851667 2117437275788139667277501)
            ·
              refine ⟨794038978420552375229063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2117437275788139667277501 794038978420552375229063)
              ·
                refine ⟨1191058467630828562843595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794038978420552375229063 1191058467630828562843595)
                ·
                  refine ⟨1786587701446242844265393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191058467630828562843595 1786587701446242844265393)
                  ·
                    refine ⟨1339940776084682133199045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786587701446242844265393 1339940776084682133199045)
                    ·
                      refine ⟨251238895515877899974821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1339940776084682133199045 251238895515877899974821)
                      ·
                        rfl

theorem cell23_489286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_489286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489286 prefixEnd_489286 := by exact prefixLift 489286
  have htrace : WordTrace (prefixWord ++ tailWord_489286) baseStart_489286 baseEnd_489286 := by
    simpa [prefixWord, tailWord_489286, baseEnd_489286] using wordTrace_append hprefix tailTrace_489286
  have hstable : (prefixWord ++ tailWord_489286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489286).length < 2 ^ (prefixWord ++ tailWord_489286).sum := by decide
  have hdescent : baseEnd_489286 < baseStart_489286 := by decide
  rcases family_descends (prefixWord ++ tailWord_489286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489329 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_489329 : Nat := 118140960795 + 489329 * 2 ^ 59
def prefixEnd_489329 : Nat := 4983230072969 + 3 ^ 40 * 489329 * 2
def baseEnd_489329 : Nat := 251260975184021231737123

theorem tailTrace_489329 : CollatzResearch.WordTrace tailWord_489329 prefixEnd_489329 251260975184021231737123 := by
  unfold tailWord_489329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847294844252078584903041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11898196562834719056602027 17847294844252078584903041)
  ·
    refine ⟨13385471133189058938677281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17847294844252078584903041 13385471133189058938677281)
    ·
      refine ⟨10039103349891794204007961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13385471133189058938677281 10039103349891794204007961)
      ·
        refine ⟨7529327512418845653005971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10039103349891794204007961 7529327512418845653005971)
        ·
          refine ⟨11293991268628268479508957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529327512418845653005971 11293991268628268479508957)
          ·
            refine ⟨4235246725735600679815859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11293991268628268479508957 4235246725735600679815859)
            ·
              refine ⟨6352870088603401019723789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235246725735600679815859 6352870088603401019723789)
              ·
                refine ⟨2382326283226275382396421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6352870088603401019723789 2382326283226275382396421)
                ·
                  refine ⟨446686178104926634199329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382326283226275382396421 446686178104926634199329)
                  ·
                    refine ⟨335014633578694975649497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446686178104926634199329 335014633578694975649497)
                    ·
                      refine ⟨251260975184021231737123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335014633578694975649497 251260975184021231737123)
                      ·
                        rfl

theorem cell23_489329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_489329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489329 prefixEnd_489329 := by exact prefixLift 489329
  have htrace : WordTrace (prefixWord ++ tailWord_489329) baseStart_489329 baseEnd_489329 := by
    simpa [prefixWord, tailWord_489329, baseEnd_489329] using wordTrace_append hprefix tailTrace_489329
  have hstable : (prefixWord ++ tailWord_489329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489329).length < 2 ^ (prefixWord ++ tailWord_489329).sum := by decide
  have hdescent : baseEnd_489329 < baseStart_489329 := by decide
  rcases family_descends (prefixWord ++ tailWord_489329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489496 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_489496 : Nat := 118140960795 + 489496 * 2 ^ 59
def prefixEnd_489496 : Nat := 4983230072969 + 3 ^ 40 * 489496 * 2
def baseEnd_489496 : Nat := 251346726453322078348855

theorem tailTrace_489496 : CollatzResearch.WordTrace tailWord_489496 prefixEnd_489496 251346726453322078348855 := by
  unfold tailWord_489496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926692917323533053116171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11902257223098044070821561 8926692917323533053116171)
  ·
    refine ⟨13390039375985299579674257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8926692917323533053116171 13390039375985299579674257)
    ·
      refine ⟨10042529531988974684755693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13390039375985299579674257 10042529531988974684755693)
      ·
        refine ⟨3765948574495865506783385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10042529531988974684755693 3765948574495865506783385)
        ·
          refine ⟨2824461430871899130087539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3765948574495865506783385 2824461430871899130087539)
          ·
            refine ⟨4236692146307848695131309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824461430871899130087539 4236692146307848695131309)
            ·
              refine ⟨1588759554865443260674241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236692146307848695131309 1588759554865443260674241)
              ·
                refine ⟨1191569666149082445505681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588759554865443260674241 1191569666149082445505681)
                ·
                  refine ⟨893677249611811834129261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1191569666149082445505681 893677249611811834129261)
                  ·
                    refine ⟨335128968604429437798473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893677249611811834129261 335128968604429437798473)
                    ·
                      refine ⟨251346726453322078348855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335128968604429437798473 251346726453322078348855)
                      ·
                        rfl

theorem cell23_489496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_489496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489496 prefixEnd_489496 := by exact prefixLift 489496
  have htrace : WordTrace (prefixWord ++ tailWord_489496) baseStart_489496 baseEnd_489496 := by
    simpa [prefixWord, tailWord_489496, baseEnd_489496] using wordTrace_append hprefix tailTrace_489496
  have hstable : (prefixWord ++ tailWord_489496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489496).length < 2 ^ (prefixWord ++ tailWord_489496).sum := by decide
  have hdescent : baseEnd_489496 < baseStart_489496 := by decide
  rcases family_descends (prefixWord ++ tailWord_489496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489526 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_489526 : Nat := 118140960795 + 489526 * 2 ^ 59
def prefixEnd_489526 : Nat := 4983230072969 + 3 ^ 40 * 489526 * 2
def baseEnd_489526 : Nat := 251362130872956960973717

theorem tailTrace_489526 : CollatzResearch.WordTrace tailWord_489526 prefixEnd_489526 251362130872956960973717 := by
  unfold tailWord_489526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115905001533648826864027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11902986683025587486549621 1115905001533648826864027)
  ·
    refine ⟨1673857502300473240296041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1115905001533648826864027 1673857502300473240296041)
    ·
      refine ⟨1255393126725354930222031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1673857502300473240296041 1255393126725354930222031)
      ·
        refine ⟨1883089690088032395333047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255393126725354930222031 1883089690088032395333047)
        ·
          refine ⟨2824634535132048592999571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883089690088032395333047 2824634535132048592999571)
          ·
            refine ⟨4236951802698072889499357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824634535132048592999571 4236951802698072889499357)
            ·
              refine ⟨1588856926011777333562259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236951802698072889499357 1588856926011777333562259)
              ·
                refine ⟨2383285389017666000343389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588856926011777333562259 2383285389017666000343389)
                ·
                  refine ⟨893732020881624750128771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383285389017666000343389 893732020881624750128771)
                  ·
                    refine ⟨1340598031322437125193157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 893732020881624750128771 1340598031322437125193157)
                    ·
                      refine ⟨251362130872956960973717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1340598031322437125193157 251362130872956960973717)
                      ·
                        rfl

theorem cell23_489526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_489526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489526 prefixEnd_489526 := by exact prefixLift 489526
  have htrace : WordTrace (prefixWord ++ tailWord_489526) baseStart_489526 baseEnd_489526 := by
    simpa [prefixWord, tailWord_489526, baseEnd_489526] using wordTrace_append hprefix tailTrace_489526
  have hstable : (prefixWord ++ tailWord_489526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489526).length < 2 ^ (prefixWord ++ tailWord_489526).sum := by decide
  have hdescent : baseEnd_489526 < baseStart_489526 := by decide
  rcases family_descends (prefixWord ++ tailWord_489526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489532 : List Nat := [2, 2, 2, 2, 2, 1, 1, 11]
def baseStart_489532 : Nat := 118140960795 + 489532 * 2 ^ 59
def prefixEnd_489532 : Nat := 4983230072969 + 3 ^ 40 * 489532 * 2
def baseEnd_489532 : Nat := 9309822657662368055507

theorem tailTrace_489532 : CollatzResearch.WordTrace tailWord_489532 prefixEnd_489532 9309822657662368055507 := by
  unfold tailWord_489532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927349431258322127271425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11903132575011096169695233 8927349431258322127271425)
  ·
    refine ⟨6695512073443741595453569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8927349431258322127271425 6695512073443741595453569)
    ·
      refine ⟨5021634055082806196590177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6695512073443741595453569 5021634055082806196590177)
      ·
        refine ⟨3766225541312104647442633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5021634055082806196590177 3766225541312104647442633)
        ·
          refine ⟨2824669155984078485581975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766225541312104647442633 2824669155984078485581975)
          ·
            refine ⟨4237003733976117728372963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824669155984078485581975 4237003733976117728372963)
            ·
              refine ⟨6355505600964176592559445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237003733976117728372963 6355505600964176592559445)
              ·
                refine ⟨9309822657662368055507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6355505600964176592559445 9309822657662368055507)
                ·
                  rfl

theorem cell23_489532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 11].length) (baseStart_489532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489532 prefixEnd_489532 := by exact prefixLift 489532
  have htrace : WordTrace (prefixWord ++ tailWord_489532) baseStart_489532 baseEnd_489532 := by
    simpa [prefixWord, tailWord_489532, baseEnd_489532] using wordTrace_append hprefix tailTrace_489532
  have hstable : (prefixWord ++ tailWord_489532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489532).length < 2 ^ (prefixWord ++ tailWord_489532).sum := by decide
  have hdescent : baseEnd_489532 < baseStart_489532 := by decide
  rcases family_descends (prefixWord ++ tailWord_489532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489554 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_489554 : Nat := 118140960795 + 489554 * 2 ^ 59
def prefixEnd_489554 : Nat := 4983230072969 + 3 ^ 40 * 489554 * 2
def baseEnd_489554 : Nat := 251376508331282851423589

theorem tailTrace_489554 : CollatzResearch.WordTrace tailWord_489554 prefixEnd_489554 251376508331282851423589 := by
  unfold tailWord_489554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463875317109235502960929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11903667512291294674562477 4463875317109235502960929)
  ·
    refine ⟨3347906487831926627220697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4463875317109235502960929 3347906487831926627220697)
    ·
      refine ⟨2510929865873944970415523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3347906487831926627220697 2510929865873944970415523)
      ·
        refine ⟨3766394798810917455623285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510929865873944970415523 3766394798810917455623285)
        ·
          refine ⟨353099512388523511464683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3766394798810917455623285 353099512388523511464683)
          ·
            refine ⟨529649268582785267197025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353099512388523511464683 529649268582785267197025)
            ·
              refine ⟨397236951437088950397769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529649268582785267197025 397236951437088950397769)
              ·
                refine ⟨297927713577816712798327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397236951437088950397769 297927713577816712798327)
                ·
                  refine ⟨446891570366725069197491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297927713577816712798327 446891570366725069197491)
                  ·
                    refine ⟨670337355550087603796237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446891570366725069197491 670337355550087603796237)
                    ·
                      refine ⟨251376508331282851423589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670337355550087603796237 251376508331282851423589)
                      ·
                        rfl

theorem cell23_489554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_489554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489554 prefixEnd_489554 := by exact prefixLift 489554
  have htrace : WordTrace (prefixWord ++ tailWord_489554) baseStart_489554 baseEnd_489554 := by
    simpa [prefixWord, tailWord_489554, baseEnd_489554] using wordTrace_append hprefix tailTrace_489554
  have hstable : (prefixWord ++ tailWord_489554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489554).length < 2 ^ (prefixWord ++ tailWord_489554).sum := by decide
  have hdescent : baseEnd_489554 < baseStart_489554 := by decide
  rcases family_descends (prefixWord ++ tailWord_489554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489560 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_489560 : Nat := 118140960795 + 489560 * 2 ^ 59
def prefixEnd_489560 : Nat := 4983230072969 + 3 ^ 40 * 489560 * 2
def baseEnd_489560 : Nat := 251379589215209827948561

theorem tailTrace_489560 : CollatzResearch.WordTrace tailWord_489560 prefixEnd_489560 251379589215209827948561 := by
  unfold tailWord_489560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927860053207602518281067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11903813404276803357708089 8927860053207602518281067)
  ·
    refine ⟨13391790079811403777421601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8927860053207602518281067 13391790079811403777421601)
    ·
      refine ⟨10043842559858552833066201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13391790079811403777421601 10043842559858552833066201)
      ·
        refine ⟨7532881919893914624799651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10043842559858552833066201 7532881919893914624799651)
        ·
          refine ⟨11299322879840871937199477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532881919893914624799651 11299322879840871937199477)
          ·
            refine ⟨1059311519985081744112451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11299322879840871937199477 1059311519985081744112451)
            ·
              refine ⟨1588967279977622616168677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059311519985081744112451 1588967279977622616168677)
              ·
                refine ⟨297931364995804240531627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588967279977622616168677 297931364995804240531627)
                ·
                  refine ⟨446897047493706360797441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297931364995804240531627 446897047493706360797441)
                  ·
                    refine ⟨335172785620279770598081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446897047493706360797441 335172785620279770598081)
                    ·
                      refine ⟨251379589215209827948561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335172785620279770598081 251379589215209827948561)
                      ·
                        rfl

theorem cell23_489560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_489560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489560 prefixEnd_489560 := by exact prefixLift 489560
  have htrace : WordTrace (prefixWord ++ tailWord_489560) baseStart_489560 baseEnd_489560 := by
    simpa [prefixWord, tailWord_489560, baseEnd_489560] using wordTrace_append hprefix tailTrace_489560
  have hstable : (prefixWord ++ tailWord_489560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489560).length < 2 ^ (prefixWord ++ tailWord_489560).sum := by decide
  have hdescent : baseEnd_489560 < baseStart_489560 := by decide
  rcases family_descends (prefixWord ++ tailWord_489560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489562 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_489562 : Nat := 118140960795 + 489562 * 2 ^ 59
def prefixEnd_489562 : Nat := 4983230072969 + 3 ^ 40 * 489562 * 2
def baseEnd_489562 : Nat := 83793538725506273374517

theorem tailTrace_489562 : CollatzResearch.WordTrace tailWord_489562 prefixEnd_489562 83793538725506273374517 := by
  unfold tailWord_489562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463948263101989844533735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11903862034938639585423293 4463948263101989844533735)
  ·
    refine ⟨6695922394652984766800603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463948263101989844533735 6695922394652984766800603)
    ·
      refine ⟨10043883591979477150200905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695922394652984766800603 10043883591979477150200905)
      ·
        refine ⟨7532912693984607862650679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10043883591979477150200905 7532912693984607862650679)
        ·
          refine ⟨11299369040976911793976019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532912693984607862650679 11299369040976911793976019)
          ·
            refine ⟨16949053561465367690964029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299369040976911793976019 16949053561465367690964029)
            ·
              refine ⟨6355895085549512884111511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16949053561465367690964029 6355895085549512884111511)
              ·
                refine ⟨9533842628324269326167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355895085549512884111511 9533842628324269326167267)
                ·
                  refine ⟨14300763942486403989250901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533842628324269326167267 14300763942486403989250901)
                  ·
                    refine ⟨83793538725506273374517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14300763942486403989250901 83793538725506273374517)
                    ·
                      rfl

theorem cell23_489562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_489562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489562 prefixEnd_489562 := by exact prefixLift 489562
  have htrace : WordTrace (prefixWord ++ tailWord_489562) baseStart_489562 baseEnd_489562 := by
    simpa [prefixWord, tailWord_489562, baseEnd_489562] using wordTrace_append hprefix tailTrace_489562
  have hstable : (prefixWord ++ tailWord_489562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489562).length < 2 ^ (prefixWord ++ tailWord_489562).sum := by decide
  have hdescent : baseEnd_489562 < baseStart_489562 := by decide
  rcases family_descends (prefixWord ++ tailWord_489562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489592 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_489592 : Nat := 118140960795 + 489592 * 2 ^ 59
def prefixEnd_489592 : Nat := 4983230072969 + 3 ^ 40 * 489592 * 2
def baseEnd_489592 : Nat := 83798673532051234249471

theorem tailTrace_489592 : CollatzResearch.WordTrace tailWord_489592 prefixEnd_489592 83798673532051234249471 := by
  unfold tailWord_489592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928443621149637250863515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11904591494866183001151353 8928443621149637250863515)
  ·
    refine ⟨13392665431724455876295273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8928443621149637250863515 13392665431724455876295273)
    ·
      refine ⟨10044499073793341907221455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13392665431724455876295273 10044499073793341907221455)
      ·
        refine ⟨15066748610690012860832183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044499073793341907221455 15066748610690012860832183)
        ·
          refine ⟨22600122916035019291248275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066748610690012860832183 22600122916035019291248275)
          ·
            refine ⟨33900184374052528936872413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22600122916035019291248275 33900184374052528936872413)
            ·
              refine ⟨12712569140269698351327155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33900184374052528936872413 12712569140269698351327155)
              ·
                refine ⟨19068853710404547526990733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12712569140269698351327155 19068853710404547526990733)
                ·
                  refine ⟨7150820141401705322621525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19068853710404547526990733 7150820141401705322621525)
                  ·
                    refine ⟨83798673532051234249471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7150820141401705322621525 83798673532051234249471)
                    ·
                      rfl

theorem cell23_489592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_489592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489592 prefixEnd_489592 := by exact prefixLift 489592
  have htrace : WordTrace (prefixWord ++ tailWord_489592) baseStart_489592 baseEnd_489592 := by
    simpa [prefixWord, tailWord_489592, baseEnd_489592] using wordTrace_append hprefix tailTrace_489592
  have hstable : (prefixWord ++ tailWord_489592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489592).length < 2 ^ (prefixWord ++ tailWord_489592).sum := by decide
  have hdescent : baseEnd_489592 < baseStart_489592 := by decide
  rcases family_descends (prefixWord ++ tailWord_489592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489603 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 1, 3, 2]
def baseStart_489603 : Nat := 118140960795 + 489603 * 2 ^ 59
def prefixEnd_489603 : Nat := 4983230072969 + 3 ^ 40 * 489603 * 2
def baseEnd_489603 : Nat := 251401668883353159710863

theorem tailTrace_489603 : CollatzResearch.WordTrace tailWord_489603 prefixEnd_489603 251401668883353159710863 := by
  unfold tailWord_489603
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857288445259423380377463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11904858963506282253584975 17857288445259423380377463)
  ·
    refine ⟨26785932667889135070566195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17857288445259423380377463 26785932667889135070566195)
    ·
      refine ⟨40178899001833702605849293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26785932667889135070566195 40178899001833702605849293)
      ·
        refine ⟨15067087125687638477193485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40178899001833702605849293 15067087125687638477193485)
        ·
          refine ⟨5650157672132864428947557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15067087125687638477193485 5650157672132864428947557)
          ·
            refine ⟨1059404563524912080427667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5650157672132864428947557 1059404563524912080427667)
            ·
              refine ⟨1589106845287368120641501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059404563524912080427667 1589106845287368120641501)
              ·
                refine ⟨595915066982763045240563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589106845287368120641501 595915066982763045240563)
                ·
                  refine ⟨893872600474144567860845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595915066982763045240563 893872600474144567860845)
                  ·
                    refine ⟨335202225177804212947817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893872600474144567860845 335202225177804212947817)
                    ·
                      refine ⟨251401668883353159710863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335202225177804212947817 251401668883353159710863)
                      ·
                        rfl

theorem cell23_489603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_489603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489603 prefixEnd_489603 := by exact prefixLift 489603
  have htrace : WordTrace (prefixWord ++ tailWord_489603) baseStart_489603 baseEnd_489603 := by
    simpa [prefixWord, tailWord_489603, baseEnd_489603] using wordTrace_append hprefix tailTrace_489603
  have hstable : (prefixWord ++ tailWord_489603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489603).length < 2 ^ (prefixWord ++ tailWord_489603).sum := by decide
  have hdescent : baseEnd_489603 < baseStart_489603 := by decide
  rcases family_descends (prefixWord ++ tailWord_489603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489610 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_489610 : Nat := 118140960795 + 489610 * 2 ^ 59
def prefixEnd_489610 : Nat := 4983230072969 + 3 ^ 40 * 489610 * 2
def baseEnd_489610 : Nat := 251405263247934632323331

theorem tailTrace_489610 : CollatzResearch.WordTrace tailWord_489610 prefixEnd_489610 251405263247934632323331 := by
  unfold tailWord_489610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464385939058515893970571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11905029170822709050588189 4464385939058515893970571)
  ·
    refine ⟨6696578908587773840955857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464385939058515893970571 6696578908587773840955857)
    ·
      refine ⟨5022434181440830380716893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696578908587773840955857 5022434181440830380716893)
      ·
        refine ⟨1883412818040311392768835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5022434181440830380716893 1883412818040311392768835)
        ·
          refine ⟨2825119227060467089153253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883412818040311392768835 2825119227060467089153253)
          ·
            refine ⟨529709855073837579216235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2825119227060467089153253 529709855073837579216235)
            ·
              refine ⟨794564782610756368824353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529709855073837579216235 794564782610756368824353)
              ·
                refine ⟨595923586958067276618265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794564782610756368824353 595923586958067276618265)
                ·
                  refine ⟨446942690218550457463699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595923586958067276618265 446942690218550457463699)
                  ·
                    refine ⟨670414035327825686195549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446942690218550457463699 670414035327825686195549)
                    ·
                      refine ⟨251405263247934632323331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670414035327825686195549 251405263247934632323331)
                      ·
                        rfl

theorem cell23_489610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_489610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489610 prefixEnd_489610 := by exact prefixLift 489610
  have htrace : WordTrace (prefixWord ++ tailWord_489610) baseStart_489610 baseEnd_489610 := by
    simpa [prefixWord, tailWord_489610, baseEnd_489610] using wordTrace_append hprefix tailTrace_489610
  have hstable : (prefixWord ++ tailWord_489610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489610).length < 2 ^ (prefixWord ++ tailWord_489610).sum := by decide
  have hdescent : baseEnd_489610 < baseStart_489610 := by decide
  rcases family_descends (prefixWord ++ tailWord_489610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489633 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_489633 : Nat := 118140960795 + 489633 * 2 ^ 59
def prefixEnd_489633 : Nat := 4983230072969 + 3 ^ 40 * 489633 * 2
def baseEnd_489633 : Nat := 251417073302988042335725

theorem tailTrace_489633 : CollatzResearch.WordTrace tailWord_489633 prefixEnd_489633 251417073302988042335725 := by
  unfold tailWord_489633
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858382635150738503969553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11905588423433825669313035 17858382635150738503969553)
  ·
    refine ⟨13393786976363053877977165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17858382635150738503969553 13393786976363053877977165)
    ·
      refine ⟨5022670116136145204241437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13393786976363053877977165 5022670116136145204241437)
      ·
        refine ⟨1883501293551054451590539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5022670116136145204241437 1883501293551054451590539)
        ·
          refine ⟨2825251940326581677385809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883501293551054451590539 2825251940326581677385809)
          ·
            refine ⟨2118938955244936258039357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2825251940326581677385809 2118938955244936258039357)
            ·
              refine ⟨794602108216851096764759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2118938955244936258039357 794602108216851096764759)
              ·
                refine ⟨1191903162325276645147139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794602108216851096764759 1191903162325276645147139)
                ·
                  refine ⟨1787854743487914967720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191903162325276645147139 1787854743487914967720709)
                  ·
                    refine ⟨335222764403984056447633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787854743487914967720709 335222764403984056447633)
                    ·
                      refine ⟨251417073302988042335725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335222764403984056447633 251417073302988042335725)
                      ·
                        rfl

theorem cell23_489633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_489633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489633 prefixEnd_489633 := by exact prefixLift 489633
  have htrace : WordTrace (prefixWord ++ tailWord_489633) baseStart_489633 baseEnd_489633 := by
    simpa [prefixWord, tailWord_489633, baseEnd_489633] using wordTrace_append hprefix tailTrace_489633
  have hstable : (prefixWord ++ tailWord_489633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489633).length < 2 ^ (prefixWord ++ tailWord_489633).sum := by decide
  have hdescent : baseEnd_489633 < baseStart_489633 := by decide
  rcases family_descends (prefixWord ++ tailWord_489633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489653 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_489653 : Nat := 118140960795 + 489653 * 2 ^ 59
def prefixEnd_489653 : Nat := 4983230072969 + 3 ^ 40 * 489653 * 2
def baseEnd_489653 : Nat := 251427342916077964085633

theorem tailTrace_489653 : CollatzResearch.WordTrace tailWord_489653 prefixEnd_489653 251427342916077964085633 := by
  unfold tailWord_489653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859112095078281919697613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11906074730052187946465075 17859112095078281919697613)
  ·
    refine ⟨6697167035654355719886605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17859112095078281919697613 6697167035654355719886605)
    ·
      refine ⟨2511437638370383394957477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6697167035654355719886605 2511437638370383394957477)
      ·
        refine ⟨470894557194446886554527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2511437638370383394957477 470894557194446886554527)
        ·
          refine ⟨706341835791670329831791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470894557194446886554527 706341835791670329831791)
          ·
            refine ⟨1059512753687505494747687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706341835791670329831791 1059512753687505494747687)
            ·
              refine ⟨1589269130531258242121531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059512753687505494747687 1589269130531258242121531)
              ·
                refine ⟨2383903695796887363182297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589269130531258242121531 2383903695796887363182297)
                ·
                  refine ⟨1787927771847665522386723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383903695796887363182297 1787927771847665522386723)
                  ·
                    refine ⟨2681891657771498283580085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787927771847665522386723 2681891657771498283580085)
                    ·
                      refine ⟨251427342916077964085633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2681891657771498283580085 251427342916077964085633)
                      ·
                        rfl

theorem cell23_489653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_489653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489653 prefixEnd_489653 := by exact prefixLift 489653
  have htrace : WordTrace (prefixWord ++ tailWord_489653) baseStart_489653 baseEnd_489653 := by
    simpa [prefixWord, tailWord_489653, baseEnd_489653] using wordTrace_append hprefix tailTrace_489653
  have hstable : (prefixWord ++ tailWord_489653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489653).length < 2 ^ (prefixWord ++ tailWord_489653).sum := by decide
  have hdescent : baseEnd_489653 < baseStart_489653 := by decide
  rcases family_descends (prefixWord ++ tailWord_489653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489669 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_489669 : Nat := 118140960795 + 489669 * 2 ^ 59
def prefixEnd_489669 : Nat := 4983230072969 + 3 ^ 40 * 489669 * 2
def baseEnd_489669 : Nat := 83811852868849967161853

theorem tailTrace_489669 : CollatzResearch.WordTrace tailWord_489669 prefixEnd_489669 83811852868849967161853 := by
  unfold tailWord_489669
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859695663020316652280061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11906463775346877768186707 17859695663020316652280061)
  ·
    refine ⟨6697385873632618744605023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17859695663020316652280061 6697385873632618744605023)
    ·
      refine ⟨10046078810448928116907535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6697385873632618744605023 10046078810448928116907535)
      ·
        refine ⟨15069118215673392175361303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046078810448928116907535 15069118215673392175361303)
        ·
          refine ⟨22603677323510088263041955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069118215673392175361303 22603677323510088263041955)
          ·
            refine ⟨33905515985265132394562933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603677323510088263041955 33905515985265132394562933)
            ·
              refine ⟨3178642123618606161990275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33905515985265132394562933 3178642123618606161990275)
              ·
                refine ⟨4767963185427909242985413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178642123618606161990275 4767963185427909242985413)
                ·
                  refine ⟨893993097267732983059765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4767963185427909242985413 893993097267732983059765)
                  ·
                    refine ⟨83811852868849967161853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 893993097267732983059765 83811852868849967161853)
                    ·
                      rfl

theorem cell23_489669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_489669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489669 prefixEnd_489669 := by exact prefixLift 489669
  have htrace : WordTrace (prefixWord ++ tailWord_489669) baseStart_489669 baseEnd_489669 := by
    simpa [prefixWord, tailWord_489669, baseEnd_489669] using wordTrace_append hprefix tailTrace_489669
  have hstable : (prefixWord ++ tailWord_489669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489669).length < 2 ^ (prefixWord ++ tailWord_489669).sum := by decide
  have hdescent : baseEnd_489669 < baseStart_489669 := by decide
  rcases family_descends (prefixWord ++ tailWord_489669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489679 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_489679 : Nat := 118140960795 + 489679 * 2 ^ 59
def prefixEnd_489679 : Nat := 4983230072969 + 3 ^ 40 * 489679 * 2
def baseEnd_489679 : Nat := 251440693413094862360513

theorem tailTrace_489679 : CollatzResearch.WordTrace tailWord_489679 prefixEnd_489679 251440693413094862360513 := by
  unfold tailWord_489679
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860060392984088360144091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11906706928656058906762727 17860060392984088360144091)
  ·
    refine ⟨26790090589476132540216137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860060392984088360144091 26790090589476132540216137)
    ·
      refine ⟨20092567942107099405162103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26790090589476132540216137 20092567942107099405162103)
      ·
        refine ⟨30138851913160649107743155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20092567942107099405162103 30138851913160649107743155)
        ·
          refine ⟨45208277869740973661614733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30138851913160649107743155 45208277869740973661614733)
          ·
            refine ⟨16953104201152865123105525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45208277869740973661614733 16953104201152865123105525)
            ·
              refine ⟨1589353518858081105291143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16953104201152865123105525 1589353518858081105291143)
              ·
                refine ⟨2384030278287121657936715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589353518858081105291143 2384030278287121657936715)
                ·
                  refine ⟨3576045417430682486905073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384030278287121657936715 3576045417430682486905073)
                  ·
                    refine ⟨2682034063073011865178805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3576045417430682486905073 2682034063073011865178805)
                    ·
                      refine ⟨251440693413094862360513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2682034063073011865178805 251440693413094862360513)
                      ·
                        rfl

theorem cell23_489679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_489679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489679 prefixEnd_489679 := by exact prefixLift 489679
  have htrace : WordTrace (prefixWord ++ tailWord_489679) baseStart_489679 baseEnd_489679 := by
    simpa [prefixWord, tailWord_489679, baseEnd_489679] using wordTrace_append hprefix tailTrace_489679
  have hstable : (prefixWord ++ tailWord_489679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489679).length < 2 ^ (prefixWord ++ tailWord_489679).sum := by decide
  have hdescent : baseEnd_489679 < baseStart_489679 := by decide
  rcases family_descends (prefixWord ++ tailWord_489679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489689 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_489689 : Nat := 118140960795 + 489689 * 2 ^ 59
def prefixEnd_489689 : Nat := 4983230072969 + 3 ^ 40 * 489689 * 2
def baseEnd_489689 : Nat := 251445828219639823235467

theorem tailTrace_489689 : CollatzResearch.WordTrace tailWord_489689 prefixEnd_489689 251445828219639823235467 := by
  unfold tailWord_489689
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860425122947860068008121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11906950081965240045338747 17860425122947860068008121)
  ·
    refine ⟨13395318842210895051006091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17860425122947860068008121 13395318842210895051006091)
    ·
      refine ⟨20092978263316342576509137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13395318842210895051006091 20092978263316342576509137)
      ·
        refine ⟨15069733697487256932381853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20092978263316342576509137 15069733697487256932381853)
        ·
          refine ⟨5651150136557721349643195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15069733697487256932381853 5651150136557721349643195)
          ·
            refine ⟨8476725204836582024464793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651150136557721349643195 8476725204836582024464793)
            ·
              refine ⟨6357543903627436518348595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476725204836582024464793 6357543903627436518348595)
              ·
                refine ⟨9536315855441154777522893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357543903627436518348595 9536315855441154777522893)
                ·
                  refine ⟨3576118445790433041571085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9536315855441154777522893 3576118445790433041571085)
                  ·
                    refine ⟨1341044417171412390589157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576118445790433041571085 1341044417171412390589157)
                    ·
                      refine ⟨251445828219639823235467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1341044417171412390589157 251445828219639823235467)
                      ·
                        rfl

theorem cell23_489689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_489689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489689 prefixEnd_489689 := by exact prefixLift 489689
  have htrace : WordTrace (prefixWord ++ tailWord_489689) baseStart_489689 baseEnd_489689 := by
    simpa [prefixWord, tailWord_489689, baseEnd_489689] using wordTrace_append hprefix tailTrace_489689
  have hstable : (prefixWord ++ tailWord_489689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489689).length < 2 ^ (prefixWord ++ tailWord_489689).sum := by decide
  have hdescent : baseEnd_489689 < baseStart_489689 := by decide
  rcases family_descends (prefixWord ++ tailWord_489689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489703 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 2, 5]
def baseStart_489703 : Nat := 118140960795 + 489703 * 2 ^ 59
def prefixEnd_489703 : Nat := 4983230072969 + 3 ^ 40 * 489703 * 2
def baseEnd_489703 : Nat := 83817672316267589486801

theorem tailTrace_489703 : CollatzResearch.WordTrace tailWord_489703 prefixEnd_489703 83817672316267589486801 := by
  unfold tailWord_489703
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860935744897140459017763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11907290496598093639345175 17860935744897140459017763)
  ·
    refine ⟨26791403617345710688526645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860935744897140459017763 26791403617345710688526645)
    ·
      refine ⟨2511694089126160377049373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26791403617345710688526645 2511694089126160377049373)
      ·
        refine ⟨941885283422310141393515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2511694089126160377049373 941885283422310141393515)
        ·
          refine ⟨1412827925133465212090273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941885283422310141393515 1412827925133465212090273)
          ·
            refine ⟨1059620943850098909067705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412827925133465212090273 1059620943850098909067705)
            ·
              refine ⟨794715707887574181800779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059620943850098909067705 794715707887574181800779)
              ·
                refine ⟨1192073561831361272701169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794715707887574181800779 1192073561831361272701169)
                ·
                  refine ⟨894055171373520954525877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192073561831361272701169 894055171373520954525877)
                  ·
                    refine ⟨83817672316267589486801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 894055171373520954525877 83817672316267589486801)
                    ·
                      rfl

theorem cell23_489703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_489703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489703 prefixEnd_489703 := by exact prefixLift 489703
  have htrace : WordTrace (prefixWord ++ tailWord_489703) baseStart_489703 baseEnd_489703 := by
    simpa [prefixWord, tailWord_489703, baseEnd_489703] using wordTrace_append hprefix tailTrace_489703
  have hstable : (prefixWord ++ tailWord_489703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489703).length < 2 ^ (prefixWord ++ tailWord_489703).sum := by decide
  have hdescent : baseEnd_489703 < baseStart_489703 := by decide
  rcases family_descends (prefixWord ++ tailWord_489703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489726 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_489726 : Nat := 118140960795 + 489726 * 2 ^ 59
def prefixEnd_489726 : Nat := 4983230072969 + 3 ^ 40 * 489726 * 2
def baseEnd_489726 : Nat := 251464827003856178472797

theorem tailTrace_489726 : CollatzResearch.WordTrace tailWord_489726 prefixEnd_489726 251464827003856178472797 := by
  unfold tailWord_489726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232721827976726923388129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11907849749209210258070021 2232721827976726923388129)
  ·
    refine ⟨1674541370982545192541097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232721827976726923388129 1674541370982545192541097)
    ·
      refine ⟨1255906028236908894405823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1674541370982545192541097 1255906028236908894405823)
      ·
        refine ⟨1883859042355363341608735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255906028236908894405823 1883859042355363341608735)
        ·
          refine ⟨2825788563533045012413103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883859042355363341608735 2825788563533045012413103)
          ·
            refine ⟨4238682845299567518619655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825788563533045012413103 4238682845299567518619655)
            ·
              refine ⟨6358024267949351277929483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238682845299567518619655 6358024267949351277929483)
              ·
                refine ⟨9537036401924026916894225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358024267949351277929483 9537036401924026916894225)
                ·
                  refine ⟨7152777301443020187670669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537036401924026916894225 7152777301443020187670669)
                  ·
                    refine ⟨2682291488041132570376501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7152777301443020187670669 2682291488041132570376501)
                    ·
                      refine ⟨251464827003856178472797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2682291488041132570376501 251464827003856178472797)
                      ·
                        rfl

theorem cell23_489726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_489726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489726 prefixEnd_489726 := by exact prefixLift 489726
  have htrace : WordTrace (prefixWord ++ tailWord_489726) baseStart_489726 baseEnd_489726 := by
    simpa [prefixWord, tailWord_489726, baseEnd_489726] using wordTrace_append hprefix tailTrace_489726
  have hstable : (prefixWord ++ tailWord_489726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489726).length < 2 ^ (prefixWord ++ tailWord_489726).sum := by decide
  have hdescent : baseEnd_489726 < baseStart_489726 := by decide
  rcases family_descends (prefixWord ++ tailWord_489726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489757 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_489757 : Nat := 118140960795 + 489757 * 2 ^ 59
def prefixEnd_489757 : Nat := 4983230072969 + 3 ^ 40 * 489757 * 2
def baseEnd_489757 : Nat := 251480744904145557185155

theorem tailTrace_489757 : CollatzResearch.WordTrace tailWord_489757 prefixEnd_489757 251480744904145557185155 := by
  unfold tailWord_489757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862905286701507681483525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11908603524467671787655683 17862905286701507681483525)
  ·
    refine ⟨3349294741256532690278161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17862905286701507681483525 3349294741256532690278161)
    ·
      refine ⟨2511971055942399517708621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349294741256532690278161 2511971055942399517708621)
      ·
        refine ⟨941989145978399819140733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2511971055942399517708621 941989145978399819140733)
        ·
          refine ⟨353245929741899932177775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941989145978399819140733 353245929741899932177775)
          ·
            refine ⟨529868894612849898266663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353245929741899932177775 529868894612849898266663)
            ·
              refine ⟨794803341919274847399995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529868894612849898266663 794803341919274847399995)
              ·
                refine ⟨1192205012878912271099993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794803341919274847399995 1192205012878912271099993)
                ·
                  refine ⟨894153759659184203324995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192205012878912271099993 894153759659184203324995)
                  ·
                    refine ⟨1341230639488776304987493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 894153759659184203324995 1341230639488776304987493)
                    ·
                      refine ⟨251480744904145557185155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1341230639488776304987493 251480744904145557185155)
                      ·
                        rfl

theorem cell23_489757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_489757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489757 prefixEnd_489757 := by exact prefixLift 489757
  have htrace : WordTrace (prefixWord ++ tailWord_489757) baseStart_489757 baseEnd_489757 := by
    simpa [prefixWord, tailWord_489757, baseEnd_489757] using wordTrace_append hprefix tailTrace_489757
  have hstable : (prefixWord ++ tailWord_489757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489757).length < 2 ^ (prefixWord ++ tailWord_489757).sum := by decide
  have hdescent : baseEnd_489757 < baseStart_489757 := by decide
  rcases family_descends (prefixWord ++ tailWord_489757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489760 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_489760 : Nat := 118140960795 + 489760 * 2 ^ 59
def prefixEnd_489760 : Nat := 4983230072969 + 3 ^ 40 * 489760 * 2
def baseEnd_489760 : Nat := 251482285346109045447641

theorem tailTrace_489760 : CollatzResearch.WordTrace tailWord_489760 prefixEnd_489760 251482285346109045447641 := by
  unfold tailWord_489760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931507352845319596921367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11908676470460426129228489 8931507352845319596921367)
  ·
    refine ⟨13397261029267979395382051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931507352845319596921367 13397261029267979395382051)
    ·
      refine ⟨20095891543901969093073077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397261029267979395382051 20095891543901969093073077)
      ·
        refine ⟨1883989832240809602475601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20095891543901969093073077 1883989832240809602475601)
        ·
          refine ⟨1412992374180607201856701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883989832240809602475601 1412992374180607201856701)
          ·
            refine ⟨529872140317727700696263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1412992374180607201856701 529872140317727700696263)
            ·
              refine ⟨794808210476591551044395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529872140317727700696263 794808210476591551044395)
              ·
                refine ⟨1192212315714887326566593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794808210476591551044395 1192212315714887326566593)
                ·
                  refine ⟨894159236786165494924945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192212315714887326566593 894159236786165494924945)
                  ·
                    refine ⟨670619427589624121193709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894159236786165494924945 670619427589624121193709)
                    ·
                      refine ⟨251482285346109045447641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670619427589624121193709 251482285346109045447641)
                      ·
                        rfl

theorem cell23_489760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_489760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489760 prefixEnd_489760 := by exact prefixLift 489760
  have htrace : WordTrace (prefixWord ++ tailWord_489760) baseStart_489760 baseEnd_489760 := by
    simpa [prefixWord, tailWord_489760, baseEnd_489760] using wordTrace_append hprefix tailTrace_489760
  have hstable : (prefixWord ++ tailWord_489760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489760).length < 2 ^ (prefixWord ++ tailWord_489760).sum := by decide
  have hdescent : baseEnd_489760 < baseStart_489760 := by decide
  rcases family_descends (prefixWord ++ tailWord_489760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489780 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 6]
def baseStart_489780 : Nat := 118140960795 + 489780 * 2 ^ 59
def prefixEnd_489780 : Nat := 4983230072969 + 3 ^ 40 * 489780 * 2
def baseEnd_489780 : Nat := 27943617217688774133061

theorem tailTrace_489780 : CollatzResearch.WordTrace tailWord_489780 prefixEnd_489780 27943617217688774133061 := by
  unfold tailWord_489780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931872082809091304785397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11909162777078788406380529 8931872082809091304785397)
  ·
    refine ⟨837363007763352309823631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8931872082809091304785397 837363007763352309823631)
    ·
      refine ⟨1256044511645028464735447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837363007763352309823631 1256044511645028464735447)
      ·
        refine ⟨1884066767467542697103171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256044511645028464735447 1884066767467542697103171)
        ·
          refine ⟨2826100151201314045654757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884066767467542697103171 2826100151201314045654757)
          ·
            refine ⟨529893778350246383560267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2826100151201314045654757 529893778350246383560267)
            ·
              refine ⟨794840667525369575340401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529893778350246383560267 794840667525369575340401)
              ·
                refine ⟨596130500644027181505301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794840667525369575340401 596130500644027181505301)
                ·
                  refine ⟨27943617217688774133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 596130500644027181505301 27943617217688774133061)
                  ·
                    rfl

theorem cell23_489780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_489780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489780 prefixEnd_489780 := by exact prefixLift 489780
  have htrace : WordTrace (prefixWord ++ tailWord_489780) baseStart_489780 baseEnd_489780 := by
    simpa [prefixWord, tailWord_489780, baseEnd_489780] using wordTrace_append hprefix tailTrace_489780
  have hstable : (prefixWord ++ tailWord_489780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489780).length < 2 ^ (prefixWord ++ tailWord_489780).sum := by decide
  have hdescent : baseEnd_489780 < baseStart_489780 := by decide
  rcases family_descends (prefixWord ++ tailWord_489780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489783 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_489783 : Nat := 118140960795 + 489783 * 2 ^ 59
def prefixEnd_489783 : Nat := 4983230072969 + 3 ^ 40 * 489783 * 2
def baseEnd_489783 : Nat := 251494095401162455460035

theorem tailTrace_489783 : CollatzResearch.WordTrace tailWord_489783 prefixEnd_489783 251494095401162455460035 := by
  unfold tailWord_489783
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863853584607314121930003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11909235723071542747953335 17863853584607314121930003)
  ·
    refine ⟨26795780376910971182895005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17863853584607314121930003 26795780376910971182895005)
    ·
      refine ⟨10048417641341614193585627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26795780376910971182895005 10048417641341614193585627)
      ·
        refine ⟨15072626462012421290378441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048417641341614193585627 15072626462012421290378441)
        ·
          refine ⟨11304469846509315967783831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15072626462012421290378441 11304469846509315967783831)
          ·
            refine ⟨16956704769763973951675747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304469846509315967783831 16956704769763973951675747)
            ·
              refine ⟨25435057154645960927513621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16956704769763973951675747 25435057154645960927513621)
              ·
                refine ⟨1192268304124029418477201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25435057154645960927513621 1192268304124029418477201)
                ·
                  refine ⟨894201228093022063857901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192268304124029418477201 894201228093022063857901)
                  ·
                    refine ⟨335325460534883273946713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894201228093022063857901 335325460534883273946713)
                    ·
                      refine ⟨251494095401162455460035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335325460534883273946713 251494095401162455460035)
                      ·
                        rfl

theorem cell23_489783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_489783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489783 prefixEnd_489783 := by exact prefixLift 489783
  have htrace : WordTrace (prefixWord ++ tailWord_489783) baseStart_489783 baseEnd_489783 := by
    simpa [prefixWord, tailWord_489783, baseEnd_489783] using wordTrace_append hprefix tailTrace_489783
  have hstable : (prefixWord ++ tailWord_489783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489783).length < 2 ^ (prefixWord ++ tailWord_489783).sum := by decide
  have hdescent : baseEnd_489783 < baseStart_489783 := by decide
  rcases family_descends (prefixWord ++ tailWord_489783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489790 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_489790 : Nat := 118140960795 + 489790 * 2 ^ 59
def prefixEnd_489790 : Nat := 4983230072969 + 3 ^ 40 * 489790 * 2
def baseEnd_489790 : Nat := 251497689765743928072503

theorem tailTrace_489790 : CollatzResearch.WordTrace tailWord_489790 prefixEnd_489790 251497689765743928072503 := by
  unfold tailWord_489790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233013611947744289679353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11909405930387969544956549 2233013611947744289679353)
  ·
    refine ⟨1674760208960808217259515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2233013611947744289679353 1674760208960808217259515)
    ·
      refine ⟨2512140313441212325889273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674760208960808217259515 2512140313441212325889273)
      ·
        refine ⟨1884105235080909244416955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512140313441212325889273 1884105235080909244416955)
        ·
          refine ⟨2826157852621363866625433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884105235080909244416955 2826157852621363866625433)
          ·
            refine ⟨2119618389466022899969075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826157852621363866625433 2119618389466022899969075)
            ·
              refine ⟨3179427584199034349953613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119618389466022899969075 3179427584199034349953613)
              ·
                refine ⟨1192285344074637881232605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179427584199034349953613 1192285344074637881232605)
                ·
                  refine ⟨447107004027989205462227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192285344074637881232605 447107004027989205462227)
                  ·
                    refine ⟨670660506041983808193341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 447107004027989205462227 670660506041983808193341)
                    ·
                      refine ⟨251497689765743928072503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670660506041983808193341 251497689765743928072503)
                      ·
                        rfl

theorem cell23_489790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_489790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489790 prefixEnd_489790 := by exact prefixLift 489790
  have htrace : WordTrace (prefixWord ++ tailWord_489790) baseStart_489790 baseEnd_489790 := by
    simpa [prefixWord, tailWord_489790, baseEnd_489790] using wordTrace_append hprefix tailTrace_489790
  have hstable : (prefixWord ++ tailWord_489790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489790).length < 2 ^ (prefixWord ++ tailWord_489790).sum := by decide
  have hdescent : baseEnd_489790 < baseStart_489790 := by decide
  rcases family_descends (prefixWord ++ tailWord_489790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489806 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_489806 : Nat := 118140960795 + 489806 * 2 ^ 59
def prefixEnd_489806 : Nat := 4983230072969 + 3 ^ 40 * 489806 * 2
def baseEnd_489806 : Nat := 83835301818738621824143

theorem tailTrace_489806 : CollatzResearch.WordTrace tailWord_489806 prefixEnd_489806 83835301818738621824143 := by
  unfold tailWord_489806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233086557940498631252159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11909794975682659366678181 2233086557940498631252159)
  ·
    refine ⟨3349629836910747946878239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233086557940498631252159 3349629836910747946878239)
    ·
      refine ⟨5024444755366121920317359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3349629836910747946878239 5024444755366121920317359)
      ·
        refine ⟨7536667133049182880476039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024444755366121920317359 7536667133049182880476039)
        ·
          refine ⟨11305000699573774320714059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536667133049182880476039 11305000699573774320714059)
          ·
            refine ⟨16957501049360661481071089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11305000699573774320714059 16957501049360661481071089)
            ·
              refine ⟨12718125787020496110803317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16957501049360661481071089 12718125787020496110803317)
              ·
                refine ⟨1192324292533171510387811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12718125787020496110803317 1192324292533171510387811)
                ·
                  refine ⟨1788486438799757265581717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192324292533171510387811 1788486438799757265581717)
                  ·
                    refine ⟨83835301818738621824143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1788486438799757265581717 83835301818738621824143)
                    ·
                      rfl

theorem cell23_489806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_489806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489806 prefixEnd_489806 := by exact prefixLift 489806
  have htrace : WordTrace (prefixWord ++ tailWord_489806) baseStart_489806 baseEnd_489806 := by
    simpa [prefixWord, tailWord_489806, baseEnd_489806] using wordTrace_append hprefix tailTrace_489806
  have hstable : (prefixWord ++ tailWord_489806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489806).length < 2 ^ (prefixWord ++ tailWord_489806).sum := by decide
  have hdescent : baseEnd_489806 < baseStart_489806 := by decide
  rcases family_descends (prefixWord ++ tailWord_489806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489824 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 1, 1, 3]
def baseStart_489824 : Nat := 118140960795 + 489824 * 2 ^ 59
def prefixEnd_489824 : Nat := 4983230072969 + 3 ^ 40 * 489824 * 2
def baseEnd_489824 : Nat := 251515148107996795047347

theorem tailTrace_489824 : CollatzResearch.WordTrace tailWord_489824 prefixEnd_489824 251515148107996795047347 := by
  unfold tailWord_489824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932674488729389062086263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11910232651639185416115017 8932674488729389062086263)
  ·
    refine ⟨13399011733094083593129395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932674488729389062086263 13399011733094083593129395)
    ·
      refine ⟨20098517599641125389694093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399011733094083593129395 20098517599641125389694093)
      ·
        refine ⟨7536944099865422021135285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20098517599641125389694093 7536944099865422021135285)
        ·
          refine ⟨706588509362383314481433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7536944099865422021135285 706588509362383314481433)
          ·
            refine ⟨529941382021787485861075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706588509362383314481433 529941382021787485861075)
            ·
              refine ⟨794912073032681228791613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529941382021787485861075 794912073032681228791613)
              ·
                refine ⟨298092027387255460796855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794912073032681228791613 298092027387255460796855)
                ·
                  refine ⟨447138041080883191195283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298092027387255460796855 447138041080883191195283)
                  ·
                    refine ⟨670707061621324786792925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 447138041080883191195283 670707061621324786792925)
                    ·
                      refine ⟨251515148107996795047347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670707061621324786792925 251515148107996795047347)
                      ·
                        rfl

theorem cell23_489824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_489824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489824 prefixEnd_489824 := by exact prefixLift 489824
  have htrace : WordTrace (prefixWord ++ tailWord_489824) baseStart_489824 baseEnd_489824 := by
    simpa [prefixWord, tailWord_489824, baseEnd_489824] using wordTrace_append hprefix tailTrace_489824
  have hstable : (prefixWord ++ tailWord_489824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489824).length < 2 ^ (prefixWord ++ tailWord_489824).sum := by decide
  have hdescent : baseEnd_489824 < baseStart_489824 := by decide
  rcases family_descends (prefixWord ++ tailWord_489824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489833 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_489833 : Nat := 118140960795 + 489833 * 2 ^ 59
def prefixEnd_489833 : Nat := 4983230072969 + 3 ^ 40 * 489833 * 2
def baseEnd_489833 : Nat := 251519769433887259834805

theorem tailTrace_489833 : CollatzResearch.WordTrace tailWord_489833 prefixEnd_489833 251519769433887259834805 := by
  unfold tailWord_489833
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865677234426172661250153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11910451489617448440833435 17865677234426172661250153)
  ·
    refine ⟨13399257925819629495937615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17865677234426172661250153 13399257925819629495937615)
    ·
      refine ⟨20098886888729444243906423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399257925819629495937615 20098886888729444243906423)
      ·
        refine ⟨30148330333094166365859635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20098886888729444243906423 30148330333094166365859635)
        ·
          refine ⟨45222495499641249548789453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30148330333094166365859635 45222495499641249548789453)
          ·
            refine ⟨16958435812365468580796045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45222495499641249548789453 16958435812365468580796045)
            ·
              refine ⟨6359413429637050717798517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16958435812365468580796045 6359413429637050717798517)
              ·
                refine ⟨596195009028473504793611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6359413429637050717798517 596195009028473504793611)
                ·
                  refine ⟨894292513542710257190417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596195009028473504793611 894292513542710257190417)
                  ·
                    refine ⟨670719385157032692892813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894292513542710257190417 670719385157032692892813)
                    ·
                      refine ⟨251519769433887259834805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670719385157032692892813 251519769433887259834805)
                      ·
                        rfl

theorem cell23_489833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_489833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489833 prefixEnd_489833 := by exact prefixLift 489833
  have htrace : WordTrace (prefixWord ++ tailWord_489833) baseStart_489833 baseEnd_489833 := by
    simpa [prefixWord, tailWord_489833, baseEnd_489833] using wordTrace_append hprefix tailTrace_489833
  have hstable : (prefixWord ++ tailWord_489833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489833).length < 2 ^ (prefixWord ++ tailWord_489833).sum := by decide
  have hdescent : baseEnd_489833 < baseStart_489833 := by decide
  rcases family_descends (prefixWord ++ tailWord_489833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489857 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_489857 : Nat := 118140960795 + 489857 * 2 ^ 59
def prefixEnd_489857 : Nat := 4983230072969 + 3 ^ 40 * 489857 * 2
def baseEnd_489857 : Nat := 83844030989865055311565

theorem tailTrace_489857 : CollatzResearch.WordTrace tailWord_489857 prefixEnd_489857 83844030989865055311565 := by
  unfold tailWord_489857
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866552586339224760123825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11911035057559483173415883 17866552586339224760123825)
  ·
    refine ⟨13399914439754418570092869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17866552586339224760123825 13399914439754418570092869)
    ·
      refine ⟨2512483957453953481892413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13399914439754418570092869 2512483957453953481892413)
      ·
        refine ⟨942181484045232555709655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2512483957453953481892413 942181484045232555709655)
        ·
          refine ⟨1413272226067848833564483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942181484045232555709655 1413272226067848833564483)
          ·
            refine ⟨2119908339101773250346725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413272226067848833564483 2119908339101773250346725)
            ·
              refine ⟨397482813581582484440011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2119908339101773250346725 397482813581582484440011)
              ·
                refine ⟨596224220372373726660017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397482813581582484440011 596224220372373726660017)
                ·
                  refine ⟨447168165279280294995013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596224220372373726660017 447168165279280294995013)
                  ·
                    refine ⟨83844030989865055311565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 447168165279280294995013 83844030989865055311565)
                    ·
                      rfl

theorem cell23_489857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_489857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489857 prefixEnd_489857 := by exact prefixLift 489857
  have htrace : WordTrace (prefixWord ++ tailWord_489857) baseStart_489857 baseEnd_489857 := by
    simpa [prefixWord, tailWord_489857, baseEnd_489857] using wordTrace_append hprefix tailTrace_489857
  have hstable : (prefixWord ++ tailWord_489857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489857).length < 2 ^ (prefixWord ++ tailWord_489857).sum := by decide
  have hdescent : baseEnd_489857 < baseStart_489857 := by decide
  rcases family_descends (prefixWord ++ tailWord_489857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489863 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_489863 : Nat := 118140960795 + 489863 * 2 ^ 59
def prefixEnd_489863 : Nat := 4983230072969 + 3 ^ 40 * 489863 * 2
def baseEnd_489863 : Nat := 251535173853522142459667

theorem tailTrace_489863 : CollatzResearch.WordTrace tailWord_489863 prefixEnd_489863 251535173853522142459667 := by
  unfold tailWord_489863
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866771424317487784842243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11911180949544991856561495 17866771424317487784842243)
  ·
    refine ⟨26800157136476231677263365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17866771424317487784842243 26800157136476231677263365)
    ·
      refine ⟨5025029463089293439486881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26800157136476231677263365 5025029463089293439486881)
      ·
        refine ⟨3768772097316970079615161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025029463089293439486881 3768772097316970079615161)
        ·
          refine ⟨2826579072987727559711371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3768772097316970079615161 2826579072987727559711371)
          ·
            refine ⟨4239868609481591339567057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826579072987727559711371 4239868609481591339567057)
            ·
              refine ⟨3179901457111193504675293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239868609481591339567057 3179901457111193504675293)
              ·
                refine ⟨1192463046416697564253235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179901457111193504675293 1192463046416697564253235)
                ·
                  refine ⟨1788694569625046346379853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192463046416697564253235 1788694569625046346379853)
                  ·
                    refine ⟨670760463609392379892445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788694569625046346379853 670760463609392379892445)
                    ·
                      refine ⟨251535173853522142459667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670760463609392379892445 251535173853522142459667)
                      ·
                        rfl

theorem cell23_489863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_489863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489863 prefixEnd_489863 := by exact prefixLift 489863
  have htrace : WordTrace (prefixWord ++ tailWord_489863) baseStart_489863 baseEnd_489863 := by
    simpa [prefixWord, tailWord_489863, baseEnd_489863] using wordTrace_append hprefix tailTrace_489863
  have hstable : (prefixWord ++ tailWord_489863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489863).length < 2 ^ (prefixWord ++ tailWord_489863).sum := by decide
  have hdescent : baseEnd_489863 < baseStart_489863 := by decide
  rcases family_descends (prefixWord ++ tailWord_489863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489880 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_489880 : Nat := 118140960795 + 489880 * 2 ^ 59
def prefixEnd_489880 : Nat := 4983230072969 + 3 ^ 40 * 489880 * 2
def baseEnd_489880 : Nat := 251543903024648575947089

theorem tailTrace_489880 : CollatzResearch.WordTrace tailWord_489880 prefixEnd_489880 251543903024648575947089 := by
  unfold tailWord_489880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8933695732627949844105547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11911594310170599792140729 8933695732627949844105547)
  ·
    refine ⟨13400543598941924766158321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8933695732627949844105547 13400543598941924766158321)
    ·
      refine ⟨10050407699206443574618741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13400543598941924766158321 10050407699206443574618741)
      ·
        refine ⟨942225721800604085120507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10050407699206443574618741 942225721800604085120507)
        ·
          refine ⟨1413338582700906127680761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942225721800604085120507 1413338582700906127680761)
          ·
            refine ⟨1060003937025679595760571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413338582700906127680761 1060003937025679595760571)
            ·
              refine ⟨1590005905538519393640857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060003937025679595760571 1590005905538519393640857)
              ·
                refine ⟨1192504429153889545230643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590005905538519393640857 1192504429153889545230643)
                ·
                  refine ⟨1788756643730834317845965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192504429153889545230643 1788756643730834317845965)
                  ·
                    refine ⟨670783741399062869192237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788756643730834317845965 670783741399062869192237)
                    ·
                      refine ⟨251543903024648575947089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670783741399062869192237 251543903024648575947089)
                      ·
                        rfl

theorem cell23_489880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_489880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489880 prefixEnd_489880 := by exact prefixLift 489880
  have htrace : WordTrace (prefixWord ++ tailWord_489880) baseStart_489880 baseEnd_489880 := by
    simpa [prefixWord, tailWord_489880, baseEnd_489880] using wordTrace_append hprefix tailTrace_489880
  have hstable : (prefixWord ++ tailWord_489880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489880).length < 2 ^ (prefixWord ++ tailWord_489880).sum := by decide
  have hdescent : baseEnd_489880 < baseStart_489880 := by decide
  rcases family_descends (prefixWord ++ tailWord_489880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489913 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_489913 : Nat := 118140960795 + 489913 * 2 ^ 59
def prefixEnd_489913 : Nat := 4983230072969 + 3 ^ 40 * 489913 * 2
def baseEnd_489913 : Nat := 83853615962082315611479

theorem tailTrace_489913 : CollatzResearch.WordTrace tailWord_489913 prefixEnd_489913 83853615962082315611479 := by
  unfold tailWord_489913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868595074136346324162393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11912396716090897549441595 17868595074136346324162393)
  ·
    refine ⟨13401446305602259743121795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17868595074136346324162393 13401446305602259743121795)
    ·
      refine ⟨20102169458403389614682693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401446305602259743121795 20102169458403389614682693)
      ·
        refine ⟨3769156773450635552753005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20102169458403389614682693 3769156773450635552753005)
        ·
          refine ⟨1413433790043988332282377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3769156773450635552753005 1413433790043988332282377)
          ·
            refine ⟨1060075342532991249211783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413433790043988332282377 1060075342532991249211783)
            ·
              refine ⟨1590113013799486873817675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060075342532991249211783 1590113013799486873817675)
              ·
                refine ⟨2385169520699230310726513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590113013799486873817675 2385169520699230310726513)
                ·
                  refine ⟨1788877140524422733044885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385169520699230310726513 1788877140524422733044885)
                  ·
                    refine ⟨83853615962082315611479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1788877140524422733044885 83853615962082315611479)
                    ·
                      rfl

theorem cell23_489913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_489913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489913 prefixEnd_489913 := by exact prefixLift 489913
  have htrace : WordTrace (prefixWord ++ tailWord_489913) baseStart_489913 baseEnd_489913 := by
    simpa [prefixWord, tailWord_489913, baseEnd_489913] using wordTrace_append hprefix tailTrace_489913
  have hstable : (prefixWord ++ tailWord_489913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489913).length < 2 ^ (prefixWord ++ tailWord_489913).sum := by decide
  have hdescent : baseEnd_489913 < baseStart_489913 := by decide
  rcases family_descends (prefixWord ++ tailWord_489913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489920 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2]
def baseStart_489920 : Nat := 118140960795 + 489920 * 2 ^ 59
def prefixEnd_489920 : Nat := 4983230072969 + 3 ^ 40 * 489920 * 2
def baseEnd_489920 : Nat := 251564442250828419446905

theorem tailTrace_489920 : CollatzResearch.WordTrace tailWord_489920 prefixEnd_489920 251564442250828419446905 := by
  unfold tailWord_489920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934425192555493259833607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11912566923407324346444809 8934425192555493259833607)
  ·
    refine ⟨13401637788833239889750411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8934425192555493259833607 13401637788833239889750411)
    ·
      refine ⟨20102456683249859834625617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401637788833239889750411 20102456683249859834625617)
      ·
        refine ⟨15076842512437394875969213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20102456683249859834625617 15076842512437394875969213)
        ·
          refine ⟨5653815942164023078488455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15076842512437394875969213 5653815942164023078488455)
          ·
            refine ⟨8480723913246034617732683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653815942164023078488455 8480723913246034617732683)
            ·
              refine ⟨12721085869869051926599025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480723913246034617732683 12721085869869051926599025)
              ·
                refine ⟨9540814402401788944949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12721085869869051926599025 9540814402401788944949269)
                ·
                  refine ⟨447225675112583856794497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9540814402401788944949269 447225675112583856794497)
                  ·
                    refine ⟨335419256334437892595873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447225675112583856794497 335419256334437892595873)
                    ·
                      refine ⟨251564442250828419446905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335419256334437892595873 251564442250828419446905)
                      ·
                        rfl

theorem cell23_489920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_489920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489920 prefixEnd_489920 := by exact prefixLift 489920
  have htrace : WordTrace (prefixWord ++ tailWord_489920) baseStart_489920 baseEnd_489920 := by
    simpa [prefixWord, tailWord_489920, baseEnd_489920] using wordTrace_append hprefix tailTrace_489920
  have hstable : (prefixWord ++ tailWord_489920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489920).length < 2 ^ (prefixWord ++ tailWord_489920).sum := by decide
  have hdescent : baseEnd_489920 < baseStart_489920 := by decide
  rcases family_descends (prefixWord ++ tailWord_489920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489953 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_489953 : Nat := 118140960795 + 489953 * 2 ^ 59
def prefixEnd_489953 : Nat := 4983230072969 + 3 ^ 40 * 489953 * 2
def baseEnd_489953 : Nat := 251581387112426790334253

theorem tailTrace_489953 : CollatzResearch.WordTrace tailWord_489953 prefixEnd_489953 251581387112426790334253 := by
  unfold tailWord_489953
  simp only [CollatzResearch.WordTrace]
  refine ⟨17870053993991433155618513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11913369329327622103745675 17870053993991433155618513)
  ·
    refine ⟨13402540495493574866713885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17870053993991433155618513 13402540495493574866713885)
    ·
      refine ⟨5025952685810090575017707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13402540495493574866713885 5025952685810090575017707)
      ·
        refine ⟨7538929028715135862526561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025952685810090575017707 7538929028715135862526561)
        ·
          refine ⟨5654196771536351896894921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538929028715135862526561 5654196771536351896894921)
          ·
            refine ⟨4240647578652263922671191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5654196771536351896894921 4240647578652263922671191)
            ·
              refine ⟨6360971367978395884006787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240647578652263922671191 6360971367978395884006787)
              ·
                refine ⟨9541457051967593826010181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360971367978395884006787 9541457051967593826010181)
                ·
                  refine ⟨1789023197243923842376909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9541457051967593826010181 1789023197243923842376909)
                  ·
                    refine ⟨670883698966471440891341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789023197243923842376909 670883698966471440891341)
                    ·
                      refine ⟨251581387112426790334253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 670883698966471440891341 251581387112426790334253)
                      ·
                        rfl

theorem cell23_489953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_489953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489953 prefixEnd_489953 := by exact prefixLift 489953
  have htrace : WordTrace (prefixWord ++ tailWord_489953) baseStart_489953 baseEnd_489953 := by
    simpa [prefixWord, tailWord_489953, baseEnd_489953] using wordTrace_append hprefix tailTrace_489953
  have hstable : (prefixWord ++ tailWord_489953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489953).length < 2 ^ (prefixWord ++ tailWord_489953).sum := by decide
  have hdescent : baseEnd_489953 < baseStart_489953 := by decide
  rcases family_descends (prefixWord ++ tailWord_489953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489960 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 5]
def baseStart_489960 : Nat := 118140960795 + 489960 * 2 ^ 59
def prefixEnd_489960 : Nat := 4983230072969 + 3 ^ 40 * 489960 * 2
def baseEnd_489960 : Nat := 27953886830778695882969

theorem tailTrace_489960 : CollatzResearch.WordTrace tailWord_489960 prefixEnd_489960 27953886830778695882969 := by
  unfold tailWord_489960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935154652483036675561667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11913539536644048900748889 8935154652483036675561667)
  ·
    refine ⟨13402731978724555013342501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935154652483036675561667 13402731978724555013342501)
    ·
      refine ⟨2513012246010854065001719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13402731978724555013342501 2513012246010854065001719)
      ·
        refine ⟨3769518369016281097502579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513012246010854065001719 3769518369016281097502579)
        ·
          refine ⟨5654277553524421646253869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769518369016281097502579 5654277553524421646253869)
          ·
            refine ⟨2120354082571658117345201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5654277553524421646253869 2120354082571658117345201)
            ·
              refine ⟨1590265561928743588008901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120354082571658117345201 1590265561928743588008901)
              ·
                refine ⟨298174792861639422751669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1590265561928743588008901 298174792861639422751669)
                ·
                  refine ⟨27953886830778695882969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298174792861639422751669 27953886830778695882969)
                  ·
                    rfl

theorem cell23_489960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 5].length) (baseStart_489960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489960 prefixEnd_489960 := by exact prefixLift 489960
  have htrace : WordTrace (prefixWord ++ tailWord_489960) baseStart_489960 baseEnd_489960 := by
    simpa [prefixWord, tailWord_489960, baseEnd_489960] using wordTrace_append hprefix tailTrace_489960
  have hstable : (prefixWord ++ tailWord_489960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489960).length < 2 ^ (prefixWord ++ tailWord_489960).sum := by decide
  have hdescent : baseEnd_489960 < baseStart_489960 := by decide
  rcases family_descends (prefixWord ++ tailWord_489960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490007 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 2, 5]
def baseStart_490007 : Nat := 118140960795 + 490007 * 2 ^ 59
def prefixEnd_490007 : Nat := 4983230072969 + 3 ^ 40 * 490007 * 2
def baseEnd_490007 : Nat := 83869705022589859686335

theorem tailTrace_490007 : CollatzResearch.WordTrace tailWord_490007 prefixEnd_490007 83869705022589859686335 := by
  unfold tailWord_490007
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872023535795800378084275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11914682357197200252056183 17872023535795800378084275)
  ·
    refine ⟨26808035303693700567126413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872023535795800378084275 26808035303693700567126413)
    ·
      refine ⟨10053013238885137712672405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26808035303693700567126413 10053013238885137712672405)
      ·
        refine ⟨471234995572740830281519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10053013238885137712672405 471234995572740830281519)
        ·
          refine ⟨706852493359111245422279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471234995572740830281519 706852493359111245422279)
          ·
            refine ⟨1060278740038666868133419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706852493359111245422279 1060278740038666868133419)
            ·
              refine ⟨1590418110058000302200129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060278740038666868133419 1590418110058000302200129)
              ·
                refine ⟨1192813582543500226650097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590418110058000302200129 1192813582543500226650097)
                ·
                  refine ⟨894610186907625169987573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192813582543500226650097 894610186907625169987573)
                  ·
                    refine ⟨83869705022589859686335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 894610186907625169987573 83869705022589859686335)
                    ·
                      rfl

theorem cell23_490007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_490007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490007 prefixEnd_490007 := by exact prefixLift 490007
  have htrace : WordTrace (prefixWord ++ tailWord_490007) baseStart_490007 baseEnd_490007 := by
    simpa [prefixWord, tailWord_490007, baseEnd_490007] using wordTrace_append hprefix tailTrace_490007
  have hstable : (prefixWord ++ tailWord_490007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490007).length < 2 ^ (prefixWord ++ tailWord_490007).sum := by decide
  have hdescent : baseEnd_490007 < baseStart_490007 := by decide
  rcases family_descends (prefixWord ++ tailWord_490007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490010 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_490010 : Nat := 118140960795 + 490010 * 2 ^ 59
def prefixEnd_490010 : Nat := 4983230072969 + 3 ^ 40 * 490010 * 2
def baseEnd_490010 : Nat := 251610655509733067321491

theorem tailTrace_490010 : CollatzResearch.WordTrace tailWord_490010 prefixEnd_490010 251610655509733067321491 := by
  unfold tailWord_490010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468033238696232972610871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11914755303189954593628989 4468033238696232972610871)
  ·
    refine ⟨6702049858044349458916307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468033238696232972610871 6702049858044349458916307)
    ·
      refine ⟨10053074787066524188374461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702049858044349458916307 10053074787066524188374461)
      ·
        refine ⟨3769903045149946570640423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10053074787066524188374461 3769903045149946570640423)
        ·
          refine ⟨5654854567724919855960635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769903045149946570640423 5654854567724919855960635)
          ·
            refine ⟨8482281851587379783940953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654854567724919855960635 8482281851587379783940953)
            ·
              refine ⟨6361711388690534837955715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482281851587379783940953 6361711388690534837955715)
              ·
                refine ⟨9542567083035802256933573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361711388690534837955715 9542567083035802256933573)
                ·
                  refine ⟨1789231328069212923175045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9542567083035802256933573 1789231328069212923175045)
                  ·
                    refine ⟨335480874012977423095321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789231328069212923175045 335480874012977423095321)
                    ·
                      refine ⟨251610655509733067321491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335480874012977423095321 251610655509733067321491)
                      ·
                        rfl

theorem cell23_490010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_490010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490010 prefixEnd_490010 := by exact prefixLift 490010
  have htrace : WordTrace (prefixWord ++ tailWord_490010) baseStart_490010 baseEnd_490010 := by
    simpa [prefixWord, tailWord_490010, baseEnd_490010] using wordTrace_append hprefix tailTrace_490010
  have hstable : (prefixWord ++ tailWord_490010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490010).length < 2 ^ (prefixWord ++ tailWord_490010).sum := by decide
  have hdescent : baseEnd_490010 < baseStart_490010 := by decide
  rcases family_descends (prefixWord ++ tailWord_490010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490078 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_490078 : Nat := 118140960795 + 490078 * 2 ^ 59
def prefixEnd_490078 : Nat := 4983230072969 + 3 ^ 40 * 490078 * 2
def baseEnd_490078 : Nat := 251645572194238801271179

theorem tailTrace_490078 : CollatzResearch.WordTrace tailWord_490078 prefixEnd_490078 251645572194238801271179 := by
  unfold tailWord_490078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234326639817322437989861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11916408745692386335945925 2234326639817322437989861)
  ·
    refine ⟨418936244965747957123099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2234326639817322437989861 418936244965747957123099)
    ·
      refine ⟨628404367448621935684649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418936244965747957123099 628404367448621935684649)
      ·
        refine ⟨471303275586466451763487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628404367448621935684649 471303275586466451763487)
        ·
          refine ⟨706954913379699677645231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471303275586466451763487 706954913379699677645231)
          ·
            refine ⟨1060432370069549516467847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706954913379699677645231 1060432370069549516467847)
            ·
              refine ⟨1590648555104324274701771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060432370069549516467847 1590648555104324274701771)
              ·
                refine ⟨2385972832656486412052657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590648555104324274701771 2385972832656486412052657)
                ·
                  refine ⟨1789479624492364809039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385972832656486412052657 1789479624492364809039493)
                  ·
                    refine ⟨335527429592318401694905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789479624492364809039493 335527429592318401694905)
                    ·
                      refine ⟨251645572194238801271179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335527429592318401694905 251645572194238801271179)
                      ·
                        rfl

theorem cell23_490078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_490078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490078 prefixEnd_490078 := by exact prefixLift 490078
  have htrace : WordTrace (prefixWord ++ tailWord_490078) baseStart_490078 baseEnd_490078 := by
    simpa [prefixWord, tailWord_490078, baseEnd_490078] using wordTrace_append hprefix tailTrace_490078
  have hstable : (prefixWord ++ tailWord_490078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490078).length < 2 ^ (prefixWord ++ tailWord_490078).sum := by decide
  have hdescent : baseEnd_490078 < baseStart_490078 := by decide
  rcases family_descends (prefixWord ++ tailWord_490078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490094 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_490094 : Nat := 118140960795 + 490094 * 2 ^ 59
def prefixEnd_490094 : Nat := 4983230072969 + 3 ^ 40 * 490094 * 2
def baseEnd_490094 : Nat := 251653787884710738671105

theorem tailTrace_490094 : CollatzResearch.WordTrace tailWord_490094 prefixEnd_490094 251653787884710738671105 := by
  unfold tailWord_490094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234399585810076779562667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11916797790987076157667557 2234399585810076779562667)
  ·
    refine ⟨3351599378715115169344001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234399585810076779562667 3351599378715115169344001)
    ·
      refine ⟨2513699534036336377008001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351599378715115169344001 2513699534036336377008001)
      ·
        refine ⟨1885274650527252282756001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2513699534036336377008001 1885274650527252282756001)
        ·
          refine ⟨1413955987895439212067001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885274650527252282756001 1413955987895439212067001)
          ·
            refine ⟨1060466990921579409050251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413955987895439212067001 1060466990921579409050251)
            ·
              refine ⟨1590700486382369113575377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060466990921579409050251 1590700486382369113575377)
              ·
                refine ⟨1193025364786776835181533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590700486382369113575377 1193025364786776835181533)
                ·
                  refine ⟨447384511795041313193075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193025364786776835181533 447384511795041313193075)
                  ·
                    refine ⟨671076767692561969789613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 447384511795041313193075 671076767692561969789613)
                    ·
                      refine ⟨251653787884710738671105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671076767692561969789613 251653787884710738671105)
                      ·
                        rfl

theorem cell23_490094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_490094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490094 prefixEnd_490094 := by exact prefixLift 490094
  have htrace : WordTrace (prefixWord ++ tailWord_490094) baseStart_490094 baseEnd_490094 := by
    simpa [prefixWord, tailWord_490094, baseEnd_490094] using wordTrace_append hprefix tailTrace_490094
  have hstable : (prefixWord ++ tailWord_490094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490094).length < 2 ^ (prefixWord ++ tailWord_490094).sum := by decide
  have hdescent : baseEnd_490094 < baseStart_490094 := by decide
  rcases family_descends (prefixWord ++ tailWord_490094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490117 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_490117 : Nat := 118140960795 + 490117 * 2 ^ 59
def prefixEnd_490117 : Nat := 4983230072969 + 3 ^ 40 * 490117 * 2
def baseEnd_490117 : Nat := 251665597939764148683499

theorem tailTrace_490117 : CollatzResearch.WordTrace tailWord_490117 prefixEnd_490117 251665597939764148683499 := by
  unfold tailWord_490117
  simp only [CollatzResearch.WordTrace]
  refine ⟨17876035565397289164588605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11917357043598192776392403 17876035565397289164588605)
  ·
    refine ⟨6703513337023983436720727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17876035565397289164588605 6703513337023983436720727)
    ·
      refine ⟨10055270005535975155081091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703513337023983436720727 10055270005535975155081091)
      ·
        refine ⟨15082905008303962732621637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055270005535975155081091 15082905008303962732621637)
        ·
          refine ⟨2828044689056993012366557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15082905008303962732621637 2828044689056993012366557)
          ·
            refine ⟨1060516758396372379637459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2828044689056993012366557 1060516758396372379637459)
            ·
              refine ⟨1590775137594558569456189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060516758396372379637459 1590775137594558569456189)
              ·
                refine ⟨596540676597959463546071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590775137594558569456189 596540676597959463546071)
                ·
                  refine ⟨894811014896939195319107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596540676597959463546071 894811014896939195319107)
                  ·
                    refine ⟨1342216522345408792978661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 894811014896939195319107 1342216522345408792978661)
                    ·
                      refine ⟨251665597939764148683499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1342216522345408792978661 251665597939764148683499)
                      ·
                        rfl

theorem cell23_490117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_490117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490117 prefixEnd_490117 := by exact prefixLift 490117
  have htrace : WordTrace (prefixWord ++ tailWord_490117) baseStart_490117 baseEnd_490117 := by
    simpa [prefixWord, tailWord_490117, baseEnd_490117] using wordTrace_append hprefix tailTrace_490117
  have hstable : (prefixWord ++ tailWord_490117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490117).length < 2 ^ (prefixWord ++ tailWord_490117).sum := by decide
  have hdescent : baseEnd_490117 < baseStart_490117 := by decide
  rcases family_descends (prefixWord ++ tailWord_490117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490133 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_490133 : Nat := 118140960795 + 490133 * 2 ^ 59
def prefixEnd_490133 : Nat := 4983230072969 + 3 ^ 40 * 490133 * 2
def baseEnd_490133 : Nat := 251673813630236086083425

theorem tailTrace_490133 : CollatzResearch.WordTrace tailWord_490133 prefixEnd_490133 251673813630236086083425 := by
  unfold tailWord_490133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17876619133339323897171053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11917746088892882598114035 17876619133339323897171053)
  ·
    refine ⟨6703732175002246461439145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17876619133339323897171053 6703732175002246461439145)
    ·
      refine ⟨5027799131251684846079359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6703732175002246461439145 5027799131251684846079359)
      ·
        refine ⟨7541698696877527269119039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027799131251684846079359 7541698696877527269119039)
        ·
          refine ⟨11312548045316290903678559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541698696877527269119039 11312548045316290903678559)
          ·
            refine ⟨16968822067974436355517839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312548045316290903678559 16968822067974436355517839)
            ·
              refine ⟨25453233101961654533276759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16968822067974436355517839 25453233101961654533276759)
              ·
                refine ⟨38179849652942481799915139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25453233101961654533276759 38179849652942481799915139)
                ·
                  refine ⟨57269774479413722699872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38179849652942481799915139 57269774479413722699872709)
                  ·
                    refine ⟨10738082714890073006226133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57269774479413722699872709 10738082714890073006226133)
                    ·
                      refine ⟨251673813630236086083425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10738082714890073006226133 251673813630236086083425)
                      ·
                        rfl

theorem cell23_490133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_490133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490133 prefixEnd_490133 := by exact prefixLift 490133
  have htrace : WordTrace (prefixWord ++ tailWord_490133) baseStart_490133 baseEnd_490133 := by
    simpa [prefixWord, tailWord_490133, baseEnd_490133] using wordTrace_append hprefix tailTrace_490133
  have hstable : (prefixWord ++ tailWord_490133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490133).length < 2 ^ (prefixWord ++ tailWord_490133).sum := by decide
  have hdescent : baseEnd_490133 < baseStart_490133 := by decide
  rcases family_descends (prefixWord ++ tailWord_490133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490144 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_490144 : Nat := 118140960795 + 490144 * 2 ^ 59
def prefixEnd_490144 : Nat := 4983230072969 + 3 ^ 40 * 490144 * 2
def baseEnd_490144 : Nat := 83893153972478514348625

theorem tailTrace_490144 : CollatzResearch.WordTrace tailWord_490144 prefixEnd_490144 83893153972478514348625 := by
  unfold tailWord_490144
  simp only [CollatzResearch.WordTrace]
  refine ⟨8938510168149736387910743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11918013557532981850547657 8938510168149736387910743)
  ·
    refine ⟨13407765252224604581866115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8938510168149736387910743 13407765252224604581866115)
    ·
      refine ⟨20111647878336906872799173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13407765252224604581866115 20111647878336906872799173)
      ·
        refine ⟨3770933977188170038649845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20111647878336906872799173 3770933977188170038649845)
        ·
          refine ⟨353525060361390941123423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3770933977188170038649845 353525060361390941123423)
          ·
            refine ⟨530287590542086411685135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353525060361390941123423 530287590542086411685135)
            ·
              refine ⟨795431385813129617527703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530287590542086411685135 795431385813129617527703)
              ·
                refine ⟨1193147078719694426291555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795431385813129617527703 1193147078719694426291555)
                ·
                  refine ⟨1789720618079541639437333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193147078719694426291555 1789720618079541639437333)
                  ·
                    refine ⟨83893153972478514348625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1789720618079541639437333 83893153972478514348625)
                    ·
                      rfl

theorem cell23_490144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_490144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490144 prefixEnd_490144 := by exact prefixLift 490144
  have htrace : WordTrace (prefixWord ++ tailWord_490144) baseStart_490144 baseEnd_490144 := by
    simpa [prefixWord, tailWord_490144, baseEnd_490144] using wordTrace_append hprefix tailTrace_490144
  have hstable : (prefixWord ++ tailWord_490144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490144).length < 2 ^ (prefixWord ++ tailWord_490144).sum := by decide
  have hdescent : baseEnd_490144 < baseStart_490144 := by decide
  rcases family_descends (prefixWord ++ tailWord_490144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490151 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_490151 : Nat := 118140960795 + 490151 * 2 ^ 59
def prefixEnd_490151 : Nat := 4983230072969 + 3 ^ 40 * 490151 * 2
def baseEnd_490151 : Nat := 251683056282017015658343

theorem tailTrace_490151 : CollatzResearch.WordTrace tailWord_490151 prefixEnd_490151 251683056282017015658343 := by
  unfold tailWord_490151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877275647274112971326307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918183764849408647550871 17877275647274112971326307)
  ·
    refine ⟨26815913470911169456989461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877275647274112971326307 26815913470911169456989461)
    ·
      refine ⟨1256995943948961068296381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26815913470911169456989461 1256995943948961068296381)
      ·
        refine ⟨471373478980860400611143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1256995943948961068296381 471373478980860400611143)
        ·
          refine ⟨707060218471290600916715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471373478980860400611143 707060218471290600916715)
          ·
            refine ⟨1060590327706935901375073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707060218471290600916715 1060590327706935901375073)
            ·
              refine ⟨795442745780201926031305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060590327706935901375073 795442745780201926031305)
              ·
                refine ⟨596582059335151444523479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795442745780201926031305 596582059335151444523479)
                ·
                  refine ⟨894873089002727166785219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596582059335151444523479 894873089002727166785219)
                  ·
                    refine ⟨1342309633504090750177829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 894873089002727166785219 1342309633504090750177829)
                    ·
                      refine ⟨251683056282017015658343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1342309633504090750177829 251683056282017015658343)
                      ·
                        rfl

theorem cell23_490151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_490151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490151 prefixEnd_490151 := by exact prefixLift 490151
  have htrace : WordTrace (prefixWord ++ tailWord_490151) baseStart_490151 baseEnd_490151 := by
    simpa [prefixWord, tailWord_490151, baseEnd_490151] using wordTrace_append hprefix tailTrace_490151
  have hstable : (prefixWord ++ tailWord_490151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490151).length < 2 ^ (prefixWord ++ tailWord_490151).sum := by decide
  have hdescent : baseEnd_490151 < baseStart_490151 := by decide
  rcases family_descends (prefixWord ++ tailWord_490151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490153 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_490153 : Nat := 118140960795 + 490153 * 2 ^ 59
def prefixEnd_490153 : Nat := 4983230072969 + 3 ^ 40 * 490153 * 2
def baseEnd_490153 : Nat := 83894694414442002611111

theorem tailTrace_490153 : CollatzResearch.WordTrace tailWord_490153 prefixEnd_490153 83894694414442002611111 := by
  unfold tailWord_490153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877348593266867312899113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918232395511244875266075 17877348593266867312899113)
  ·
    refine ⟨13408011444950150484674335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17877348593266867312899113 13408011444950150484674335)
    ·
      refine ⟨20112017167425225727011503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408011444950150484674335 20112017167425225727011503)
      ·
        refine ⟨30168025751137838590517255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112017167425225727011503 30168025751137838590517255)
        ·
          refine ⟨45252038626706757885775883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30168025751137838590517255 45252038626706757885775883)
          ·
            refine ⟨67878057940060136828663825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45252038626706757885775883 67878057940060136828663825)
            ·
              refine ⟨50908543455045102621497869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67878057940060136828663825 50908543455045102621497869)
              ·
                refine ⟨19090703795641913483061701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50908543455045102621497869 19090703795641913483061701)
                ·
                  refine ⟨3579506961682858778074069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19090703795641913483061701 3579506961682858778074069)
                  ·
                    refine ⟨83894694414442002611111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3579506961682858778074069 83894694414442002611111)
                    ·
                      rfl

theorem cell23_490153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_490153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490153 prefixEnd_490153 := by exact prefixLift 490153
  have htrace : WordTrace (prefixWord ++ tailWord_490153) baseStart_490153 baseEnd_490153 := by
    simpa [prefixWord, tailWord_490153, baseEnd_490153] using wordTrace_append hprefix tailTrace_490153
  have hstable : (prefixWord ++ tailWord_490153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490153).length < 2 ^ (prefixWord ++ tailWord_490153).sum := by decide
  have hdescent : baseEnd_490153 < baseStart_490153 := by decide
  rcases family_descends (prefixWord ++ tailWord_490153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490157 : List Nat := [1, 5, 2, 1, 1, 2, 4, 7]
def baseStart_490157 : Nat := 118140960795 + 490157 * 2 ^ 59
def prefixEnd_490157 : Nat := 4983230072969 + 3 ^ 40 * 490157 * 2
def baseEnd_490157 : Nat := 9321708783923851562345

theorem tailTrace_490157 : CollatzResearch.WordTrace tailWord_490157 prefixEnd_490157 9321708783923851562345 := by
  unfold tailWord_490157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877494485252375996044725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918329656834917330696483 17877494485252375996044725)
  ·
    refine ⟨1676015107992410249629193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17877494485252375996044725 1676015107992410249629193)
    ·
      refine ⟨1257011330994307687221895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1676015107992410249629193 1257011330994307687221895)
      ·
        refine ⟨1885516996491461530832843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257011330994307687221895 1885516996491461530832843)
        ·
          refine ⟨2828275494737192296249265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885516996491461530832843 2828275494737192296249265)
          ·
            refine ⟨2121206621052894222186949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828275494737192296249265 2121206621052894222186949)
            ·
              refine ⟨397726241447417666660053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2121206621052894222186949 397726241447417666660053)
              ·
                refine ⟨9321708783923851562345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397726241447417666660053 9321708783923851562345)
                ·
                  rfl

theorem cell23_490157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 7].length) (baseStart_490157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490157 prefixEnd_490157 := by exact prefixLift 490157
  have htrace : WordTrace (prefixWord ++ tailWord_490157) baseStart_490157 baseEnd_490157 := by
    simpa [prefixWord, tailWord_490157, baseEnd_490157] using wordTrace_append hprefix tailTrace_490157
  have hstable : (prefixWord ++ tailWord_490157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490157).length < 2 ^ (prefixWord ++ tailWord_490157).sum := by decide
  have hdescent : baseEnd_490157 < baseStart_490157 := by decide
  rcases family_descends (prefixWord ++ tailWord_490157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490211 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 1, 3, 2]
def baseStart_490211 : Nat := 118140960795 + 490211 * 2 ^ 59
def prefixEnd_490211 : Nat := 4983230072969 + 3 ^ 40 * 490211 * 2
def baseEnd_490211 : Nat := 251713865121286780908067

theorem tailTrace_490211 : CollatzResearch.WordTrace tailWord_490211 prefixEnd_490211 251713865121286780908067 := by
  unfold tailWord_490211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879464027056743218510487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11919642684704495479006991 17879464027056743218510487)
  ·
    refine ⟨26819196040585114827765731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879464027056743218510487 26819196040585114827765731)
    ·
      refine ⟨40228794060877672241648597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26819196040585114827765731 40228794060877672241648597)
      ·
        refine ⟨942862360801820443163639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 40228794060877672241648597 942862360801820443163639)
        ·
          refine ⟨1414293541202730664745459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942862360801820443163639 1414293541202730664745459)
          ·
            refine ⟨2121440311804095997118189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414293541202730664745459 2121440311804095997118189)
            ·
              refine ⟨795540116926535998919321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2121440311804095997118189 795540116926535998919321)
              ·
                refine ⟨596655087694901999189491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795540116926535998919321 596655087694901999189491)
                ·
                  refine ⟨894982631542352998784237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596655087694901999189491 894982631542352998784237)
                  ·
                    refine ⟨335618486828382374544089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894982631542352998784237 335618486828382374544089)
                    ·
                      refine ⟨251713865121286780908067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335618486828382374544089 251713865121286780908067)
                      ·
                        rfl

theorem cell23_490211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_490211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490211 prefixEnd_490211 := by exact prefixLift 490211
  have htrace : WordTrace (prefixWord ++ tailWord_490211) baseStart_490211 baseEnd_490211 := by
    simpa [prefixWord, tailWord_490211, baseEnd_490211] using wordTrace_append hprefix tailTrace_490211
  have hstable : (prefixWord ++ tailWord_490211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490211).length < 2 ^ (prefixWord ++ tailWord_490211).sum := by decide
  have hdescent : baseEnd_490211 < baseStart_490211 := by decide
  rcases family_descends (prefixWord ++ tailWord_490211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490220 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_490220 : Nat := 118140960795 + 490220 * 2 ^ 59
def prefixEnd_490220 : Nat := 4983230072969 + 3 ^ 40 * 490220 * 2
def baseEnd_490220 : Nat := 251718486447177245695525

theorem tailTrace_490220 : CollatzResearch.WordTrace tailWord_490220 prefixEnd_490220 251718486447177245695525 := by
  unfold tailWord_490220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939896142012068877794057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11919861522682758503725409 8939896142012068877794057)
  ·
    refine ⟨6704922106509051658345543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8939896142012068877794057 6704922106509051658345543)
    ·
      refine ⟨10057383159763577487518315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704922106509051658345543 10057383159763577487518315)
      ·
        refine ⟨15086074739645366231277473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057383159763577487518315 15086074739645366231277473)
        ·
          refine ⟨11314556054734024673458105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086074739645366231277473 11314556054734024673458105)
          ·
            refine ⟨8485917041050518505093579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314556054734024673458105 8485917041050518505093579)
            ·
              refine ⟨12728875561575777757640369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485917041050518505093579 12728875561575777757640369)
              ·
                refine ⟨9546656671181833318230277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728875561575777757640369 9546656671181833318230277)
                ·
                  refine ⟨1789998125846593747168177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9546656671181833318230277 1789998125846593747168177)
                  ·
                    refine ⟨1342498594384945310376133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1789998125846593747168177 1342498594384945310376133)
                    ·
                      refine ⟨251718486447177245695525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1342498594384945310376133 251718486447177245695525)
                      ·
                        rfl

theorem cell23_490220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_490220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490220 prefixEnd_490220 := by exact prefixLift 490220
  have htrace : WordTrace (prefixWord ++ tailWord_490220) baseStart_490220 baseEnd_490220 := by
    simpa [prefixWord, tailWord_490220, baseEnd_490220] using wordTrace_append hprefix tailTrace_490220
  have hstable : (prefixWord ++ tailWord_490220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490220).length < 2 ^ (prefixWord ++ tailWord_490220).sum := by decide
  have hdescent : baseEnd_490220 < baseStart_490220 := by decide
  rcases family_descends (prefixWord ++ tailWord_490220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490258 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_490258 : Nat := 118140960795 + 490258 * 2 ^ 59
def prefixEnd_490258 : Nat := 4983230072969 + 3 ^ 40 * 490258 * 2
def baseEnd_490258 : Nat := 251737998712048097020351

theorem tailTrace_490258 : CollatzResearch.WordTrace tailWord_490258 prefixEnd_490258 251737998712048097020351 := by
  unfold tailWord_490258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470294564471617561367857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11920785505257646830314285 4470294564471617561367857)
  ·
    refine ⟨3352720923353713171025893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4470294564471617561367857 3352720923353713171025893)
    ·
      refine ⟨628635173128821219567355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3352720923353713171025893 628635173128821219567355)
      ·
        refine ⟨942952759693231829351033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628635173128821219567355 942952759693231829351033)
        ·
          refine ⟨707214569769923872013275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942952759693231829351033 707214569769923872013275)
          ·
            refine ⟨1060821854654885808019913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707214569769923872013275 1060821854654885808019913)
            ·
              refine ⟨795616390991164356014935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060821854654885808019913 795616390991164356014935)
              ·
                refine ⟨1193424586486746534022403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795616390991164356014935 1193424586486746534022403)
                ·
                  refine ⟨1790136879730119801033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193424586486746534022403 1790136879730119801033605)
                  ·
                    refine ⟨335650664949397462693801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1790136879730119801033605 335650664949397462693801)
                    ·
                      refine ⟨251737998712048097020351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335650664949397462693801 251737998712048097020351)
                      ·
                        rfl

theorem cell23_490258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_490258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490258 prefixEnd_490258 := by exact prefixLift 490258
  have htrace : WordTrace (prefixWord ++ tailWord_490258) baseStart_490258 baseEnd_490258 := by
    simpa [prefixWord, tailWord_490258, baseEnd_490258] using wordTrace_append hprefix tailTrace_490258
  have hstable : (prefixWord ++ tailWord_490258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490258).length < 2 ^ (prefixWord ++ tailWord_490258).sum := by decide
  have hdescent : baseEnd_490258 < baseStart_490258 := by decide
  rcases family_descends (prefixWord ++ tailWord_490258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490292 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_490292 : Nat := 118140960795 + 490292 * 2 ^ 59
def prefixEnd_490292 : Nat := 4983230072969 + 3 ^ 40 * 490292 * 2
def baseEnd_490292 : Nat := 251755457054300963995195

theorem tailTrace_490292 : CollatzResearch.WordTrace tailWord_490292 prefixEnd_490292 251755457054300963995195 := by
  unfold tailWord_490292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941209169881647026104565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11921612226508862701472753 8941209169881647026104565)
  ·
    refine ⟨838238359676404408697303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8941209169881647026104565 838238359676404408697303)
    ·
      refine ⟨1257357539514606613045955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838238359676404408697303 1257357539514606613045955)
      ·
        refine ⟨1886036309271909919568933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257357539514606613045955 1886036309271909919568933)
        ·
          refine ⟨353631807988483109919175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1886036309271909919568933 353631807988483109919175)
          ·
            refine ⟨530447711982724664878763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353631807988483109919175 530447711982724664878763)
            ·
              refine ⟨795671567974086997318145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530447711982724664878763 795671567974086997318145)
              ·
                refine ⟨596753675980565247988609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795671567974086997318145 596753675980565247988609)
                ·
                  refine ⟨447565256985423935991457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596753675980565247988609 447565256985423935991457)
                  ·
                    refine ⟨335673942739067951993593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447565256985423935991457 335673942739067951993593)
                    ·
                      refine ⟨251755457054300963995195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335673942739067951993593 251755457054300963995195)
                      ·
                        rfl

theorem cell23_490292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_490292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490292 prefixEnd_490292 := by exact prefixLift 490292
  have htrace : WordTrace (prefixWord ++ tailWord_490292) baseStart_490292 baseEnd_490292 := by
    simpa [prefixWord, tailWord_490292, baseEnd_490292] using wordTrace_append hprefix tailTrace_490292
  have hstable : (prefixWord ++ tailWord_490292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490292).length < 2 ^ (prefixWord ++ tailWord_490292).sum := by decide
  have hdescent : baseEnd_490292 < baseStart_490292 := by decide
  rcases family_descends (prefixWord ++ tailWord_490292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490341 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_490341 : Nat := 118140960795 + 490341 * 2 ^ 59
def prefixEnd_490341 : Nat := 4983230072969 + 3 ^ 40 * 490341 * 2
def baseEnd_490341 : Nat := 83926872535457090760823

theorem tailTrace_490341 : CollatzResearch.WordTrace tailWord_490341 prefixEnd_490341 83926872535457090760823 := by
  unfold tailWord_490341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884205516585775420742877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11922803677723850280495251 17884205516585775420742877)
  ·
    refine ⟨6706577068719665782778579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17884205516585775420742877 6706577068719665782778579)
    ·
      refine ⟨10059865603079498674167869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706577068719665782778579 10059865603079498674167869)
      ·
        refine ⟨3772449601154812002812951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10059865603079498674167869 3772449601154812002812951)
        ·
          refine ⟨5658674401732218004219427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772449601154812002812951 5658674401732218004219427)
          ·
            refine ⟨8488011602598327006329141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658674401732218004219427 8488011602598327006329141)
            ·
              refine ⟨795751087743593156843357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8488011602598327006329141 795751087743593156843357)
              ·
                refine ⟨298406657903847433816259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795751087743593156843357 298406657903847433816259)
                ·
                  refine ⟨447609986855771150724389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298406657903847433816259 447609986855771150724389)
                  ·
                    refine ⟨83926872535457090760823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 447609986855771150724389 83926872535457090760823)
                    ·
                      rfl

theorem cell23_490341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_490341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490341 prefixEnd_490341 := by exact prefixLift 490341
  have htrace : WordTrace (prefixWord ++ tailWord_490341) baseStart_490341 baseEnd_490341 := by
    simpa [prefixWord, tailWord_490341, baseEnd_490341] using wordTrace_append hprefix tailTrace_490341
  have hstable : (prefixWord ++ tailWord_490341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490341).length < 2 ^ (prefixWord ++ tailWord_490341).sum := by decide
  have hdescent : baseEnd_490341 < baseStart_490341 := by decide
  rcases family_descends (prefixWord ++ tailWord_490341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490358 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_490358 : Nat := 118140960795 + 490358 * 2 ^ 59
def prefixEnd_490358 : Nat := 4983230072969 + 3 ^ 40 * 490358 * 2
def baseEnd_490358 : Nat := 83929782259165901923297

theorem tailTrace_490358 : CollatzResearch.WordTrace tailWord_490358 prefixEnd_490358 83929782259165901923297 := by
  unfold tailWord_490358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117801597345261707756983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11923217038349458216074485 1117801597345261707756983)
  ·
    refine ⟨1676702396017892561635475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117801597345261707756983 1676702396017892561635475)
    ·
      refine ⟨2515053594026838842453213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676702396017892561635475 2515053594026838842453213)
      ·
        refine ⟨943145097760064565919955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2515053594026838842453213 943145097760064565919955)
        ·
          refine ⟨1414717646640096848879933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943145097760064565919955 1414717646640096848879933)
          ·
            refine ⟨530519117490036318329975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1414717646640096848879933 530519117490036318329975)
            ·
              refine ⟨795778676235054477494963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530519117490036318329975 795778676235054477494963)
              ·
                refine ⟨1193668014352581716242445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795778676235054477494963 1193668014352581716242445)
                ·
                  refine ⟨447625505382218143590917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193668014352581716242445 447625505382218143590917)
                  ·
                    refine ⟨83929782259165901923297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 447625505382218143590917 83929782259165901923297)
                    ·
                      rfl

theorem cell23_490358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_490358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490358 prefixEnd_490358 := by exact prefixLift 490358
  have htrace : WordTrace (prefixWord ++ tailWord_490358) baseStart_490358 baseEnd_490358 := by
    simpa [prefixWord, tailWord_490358, baseEnd_490358] using wordTrace_append hprefix tailTrace_490358
  have hstable : (prefixWord ++ tailWord_490358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490358).length < 2 ^ (prefixWord ++ tailWord_490358).sum := by decide
  have hdescent : baseEnd_490358 < baseStart_490358 := by decide
  rcases family_descends (prefixWord ++ tailWord_490358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490391 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_490391 : Nat := 118140960795 + 490391 * 2 ^ 59
def prefixEnd_490391 : Nat := 4983230072969 + 3 ^ 40 * 490391 * 2
def baseEnd_490391 : Nat := 251806291639096076657239

theorem tailTrace_490391 : CollatzResearch.WordTrace tailWord_490391 prefixEnd_490391 251806291639096076657239 := by
  unfold tailWord_490391
  simp only [CollatzResearch.WordTrace]
  refine ⟨17886029166404633960063027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11924019444269755973375351 17886029166404633960063027)
  ·
    refine ⟨26829043749606950940094541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17886029166404633960063027 26829043749606950940094541)
    ·
      refine ⟨10060891406102606602535453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26829043749606950940094541 10060891406102606602535453)
      ·
        refine ⟨3772834277288477475950795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10060891406102606602535453 3772834277288477475950795)
        ·
          refine ⟨5659251415932716213926193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772834277288477475950795 5659251415932716213926193)
          ·
            refine ⟨4244438561949537160444645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659251415932716213926193 4244438561949537160444645)
            ·
              refine ⟨795832230365538217583371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4244438561949537160444645 795832230365538217583371)
              ·
                refine ⟨1193748345548307326375057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795832230365538217583371 1193748345548307326375057)
                ·
                  refine ⟨895311259161230494781293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193748345548307326375057 895311259161230494781293)
                  ·
                    refine ⟨335741722185461435542985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895311259161230494781293 335741722185461435542985)
                    ·
                      refine ⟨251806291639096076657239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335741722185461435542985 251806291639096076657239)
                      ·
                        rfl

theorem cell23_490391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_490391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490391 prefixEnd_490391 := by exact prefixLift 490391
  have htrace : WordTrace (prefixWord ++ tailWord_490391) baseStart_490391 baseEnd_490391 := by
    simpa [prefixWord, tailWord_490391, baseEnd_490391] using wordTrace_append hprefix tailTrace_490391
  have hstable : (prefixWord ++ tailWord_490391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490391).length < 2 ^ (prefixWord ++ tailWord_490391).sum := by decide
  have hdescent : baseEnd_490391 < baseStart_490391 := by decide
  rcases family_descends (prefixWord ++ tailWord_490391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490424 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_490424 : Nat := 118140960795 + 490424 * 2 ^ 59
def prefixEnd_490424 : Nat := 4983230072969 + 3 ^ 40 * 490424 * 2
def baseEnd_490424 : Nat := 251823236500694447544587

theorem tailTrace_490424 : CollatzResearch.WordTrace tailWord_490424 prefixEnd_490424 251823236500694447544587 := by
  unfold tailWord_490424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943616387642540298007163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11924821850190053730676217 8943616387642540298007163)
  ·
    refine ⟨13415424581463810447010745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943616387642540298007163 13415424581463810447010745)
    ·
      refine ⟨10061568436097857835258059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13415424581463810447010745 10061568436097857835258059)
      ·
        refine ⟨15092352654146786752887089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061568436097857835258059 15092352654146786752887089)
        ·
          refine ⟨11319264490610090064665317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15092352654146786752887089 11319264490610090064665317)
          ·
            refine ⟨2122362091989391887124747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11319264490610090064665317 2122362091989391887124747)
            ·
              refine ⟨3183543137984087830687121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122362091989391887124747 3183543137984087830687121)
              ·
                refine ⟨2387657353488065873015341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183543137984087830687121 2387657353488065873015341)
                ·
                  refine ⟨895371507558024702380753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2387657353488065873015341 895371507558024702380753)
                  ·
                    refine ⟨671528630668518526785565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895371507558024702380753 671528630668518526785565)
                    ·
                      refine ⟨251823236500694447544587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671528630668518526785565 251823236500694447544587)
                      ·
                        rfl

theorem cell23_490424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_490424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490424 prefixEnd_490424 := by exact prefixLift 490424
  have htrace : WordTrace (prefixWord ++ tailWord_490424) baseStart_490424 baseEnd_490424 := by
    simpa [prefixWord, tailWord_490424, baseEnd_490424] using wordTrace_append hprefix tailTrace_490424
  have hstable : (prefixWord ++ tailWord_490424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490424).length < 2 ^ (prefixWord ++ tailWord_490424).sum := by decide
  have hdescent : baseEnd_490424 < baseStart_490424 := by decide
  rcases family_descends (prefixWord ++ tailWord_490424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490444 : List Nat := [2, 2, 1, 4, 1, 1, 5, 7]
def baseStart_490444 : Nat := 118140960795 + 490444 * 2 ^ 59
def prefixEnd_490444 : Nat := 4983230072969 + 3 ^ 40 * 490444 * 2
def baseEnd_490444 : Nat := 9327166893103124788685

theorem tailTrace_490444 : CollatzResearch.WordTrace tailWord_490444 prefixEnd_490444 9327166893103124788685 := by
  unfold tailWord_490444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943981117606312005871193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11925308156808416007828257 8943981117606312005871193)
  ·
    refine ⟨6707985838204734004403395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8943981117606312005871193 6707985838204734004403395)
    ·
      refine ⟨10061978757307101006605093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6707985838204734004403395 10061978757307101006605093)
      ·
        refine ⟨1886621016995081438738455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10061978757307101006605093 1886621016995081438738455)
        ·
          refine ⟨2829931525492622158107683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886621016995081438738455 2829931525492622158107683)
          ·
            refine ⟨4244897288238933237161525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829931525492622158107683 4244897288238933237161525)
            ·
              refine ⟨397959120772399990983893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4244897288238933237161525 397959120772399990983893)
              ·
                refine ⟨9327166893103124788685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397959120772399990983893 9327166893103124788685)
                ·
                  rfl

theorem cell23_490444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 7].length) (baseStart_490444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490444 prefixEnd_490444 := by exact prefixLift 490444
  have htrace : WordTrace (prefixWord ++ tailWord_490444) baseStart_490444 baseEnd_490444 := by
    simpa [prefixWord, tailWord_490444, baseEnd_490444] using wordTrace_append hprefix tailTrace_490444
  have hstable : (prefixWord ++ tailWord_490444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490444).length < 2 ^ (prefixWord ++ tailWord_490444).sum := by decide
  have hdescent : baseEnd_490444 < baseStart_490444 := by decide
  rcases family_descends (prefixWord ++ tailWord_490444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490458 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_490458 : Nat := 118140960795 + 490458 * 2 ^ 59
def prefixEnd_490458 : Nat := 4983230072969 + 3 ^ 40 * 490458 * 2
def baseEnd_490458 : Nat := 251840694842947314519431

theorem tailTrace_490458 : CollatzResearch.WordTrace tailWord_490458 prefixEnd_490458 251840694842947314519431 := by
  unfold tailWord_490458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472118214290476100688007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11925648571441269601834685 4472118214290476100688007)
  ·
    refine ⟨6708177321435714151032011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472118214290476100688007 6708177321435714151032011)
    ·
      refine ⟨10062265982153571226548017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708177321435714151032011 10062265982153571226548017)
      ·
        refine ⟨7546699486615178419911013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10062265982153571226548017 7546699486615178419911013)
        ·
          refine ⟨1415006153740345953733315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7546699486615178419911013 1415006153740345953733315)
          ·
            refine ⟨2122509230610518930599973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415006153740345953733315 2122509230610518930599973)
            ·
              refine ⟨397970480739472299487495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2122509230610518930599973 397970480739472299487495)
              ·
                refine ⟨596955721109208449231243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397970480739472299487495 596955721109208449231243)
                ·
                  refine ⟨895433581663812673846865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596955721109208449231243 895433581663812673846865)
                  ·
                    refine ⟨671575186247859505385149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895433581663812673846865 671575186247859505385149)
                    ·
                      refine ⟨251840694842947314519431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671575186247859505385149 251840694842947314519431)
                      ·
                        rfl

theorem cell23_490458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_490458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490458 prefixEnd_490458 := by exact prefixLift 490458
  have htrace : WordTrace (prefixWord ++ tailWord_490458) baseStart_490458 baseEnd_490458 := by
    simpa [prefixWord, tailWord_490458, baseEnd_490458] using wordTrace_append hprefix tailTrace_490458
  have hstable : (prefixWord ++ tailWord_490458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490458).length < 2 ^ (prefixWord ++ tailWord_490458).sum := by decide
  have hdescent : baseEnd_490458 < baseStart_490458 := by decide
  rcases family_descends (prefixWord ++ tailWord_490458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490485 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_490485 : Nat := 118140960795 + 490485 * 2 ^ 59
def prefixEnd_490485 : Nat := 4983230072969 + 3 ^ 40 * 490485 * 2
def baseEnd_490485 : Nat := 251854558820618708881807

theorem tailTrace_490485 : CollatzResearch.WordTrace tailWord_490485 prefixEnd_490485 251854558820618708881807 := by
  unfold tailWord_490485
  simp only [CollatzResearch.WordTrace]
  refine ⟨17889457628064088013984909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11926305085376058675989939 17889457628064088013984909)
  ·
    refine ⟨6708546610524033005244341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17889457628064088013984909 6708546610524033005244341)
    ·
      refine ⟨628926244736628094241657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6708546610524033005244341 628926244736628094241657)
      ·
        refine ⟨471694683552471070681243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628926244736628094241657 471694683552471070681243)
        ·
          refine ⟨707542025328706606021865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471694683552471070681243 707542025328706606021865)
          ·
            refine ⟨530656518996529954516399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707542025328706606021865 530656518996529954516399)
            ·
              refine ⟨795984778494794931774599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530656518996529954516399 795984778494794931774599)
              ·
                refine ⟨1193977167742192397661899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795984778494794931774599 1193977167742192397661899)
                ·
                  refine ⟨1790965751613288596492849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193977167742192397661899 1790965751613288596492849)
                  ·
                    refine ⟨1343224313709966447369637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790965751613288596492849 1343224313709966447369637)
                    ·
                      refine ⟨251854558820618708881807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1343224313709966447369637 251854558820618708881807)
                      ·
                        rfl

theorem cell23_490485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_490485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490485 prefixEnd_490485 := by exact prefixLift 490485
  have htrace : WordTrace (prefixWord ++ tailWord_490485) baseStart_490485 baseEnd_490485 := by
    simpa [prefixWord, tailWord_490485, baseEnd_490485] using wordTrace_append hprefix tailTrace_490485
  have hstable : (prefixWord ++ tailWord_490485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490485).length < 2 ^ (prefixWord ++ tailWord_490485).sum := by decide
  have hdescent : baseEnd_490485 < baseStart_490485 := by decide
  rcases family_descends (prefixWord ++ tailWord_490485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490544 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_490544 : Nat := 118140960795 + 490544 * 2 ^ 59
def prefixEnd_490544 : Nat := 4983230072969 + 3 ^ 40 * 490544 * 2
def baseEnd_490544 : Nat := 251884854179233978044035

theorem tailTrace_490544 : CollatzResearch.WordTrace tailWord_490544 prefixEnd_490544 251884854179233978044035 := by
  unfold tailWord_490544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945804767425170545191343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11927739689900227393588457 8945804767425170545191343)
  ·
    refine ⟨13418707151137755817787015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8945804767425170545191343 13418707151137755817787015)
    ·
      refine ⟨20128060726706633726680523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13418707151137755817787015 20128060726706633726680523)
      ·
        refine ⟨30192091090059950590020785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128060726706633726680523 30192091090059950590020785)
        ·
          refine ⟨22644068317544962942515589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30192091090059950590020785 22644068317544962942515589)
          ·
            refine ⟨4245762809539680551721673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22644068317544962942515589 4245762809539680551721673)
            ·
              refine ⟨3184322107154760413791255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245762809539680551721673 3184322107154760413791255)
              ·
                refine ⟨4776483160732140620686883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184322107154760413791255 4776483160732140620686883)
                ·
                  refine ⟨7164724741098210931030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776483160732140620686883 7164724741098210931030325)
                  ·
                    refine ⟨671692944477957274784093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7164724741098210931030325 671692944477957274784093)
                    ·
                      refine ⟨251884854179233978044035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671692944477957274784093 251884854179233978044035)
                      ·
                        rfl

theorem cell23_490544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_490544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490544 prefixEnd_490544 := by exact prefixLift 490544
  have htrace : WordTrace (prefixWord ++ tailWord_490544) baseStart_490544 baseEnd_490544 := by
    simpa [prefixWord, tailWord_490544, baseEnd_490544] using wordTrace_append hprefix tailTrace_490544
  have hstable : (prefixWord ++ tailWord_490544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490544).length < 2 ^ (prefixWord ++ tailWord_490544).sum := by decide
  have hdescent : baseEnd_490544 < baseStart_490544 := by decide
  rcases family_descends (prefixWord ++ tailWord_490544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490574 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_490574 : Nat := 118140960795 + 490574 * 2 ^ 59
def prefixEnd_490574 : Nat := 4983230072969 + 3 ^ 40 * 490574 * 2
def baseEnd_490574 : Nat := 251900258598868860668897

theorem tailTrace_490574 : CollatzResearch.WordTrace tailWord_490574 prefixEnd_490574 251900258598868860668897 := by
  unfold tailWord_490574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236587965592707026746847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11928469149827770809316517 2236587965592707026746847)
  ·
    refine ⟨3354881948389060540120271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2236587965592707026746847 3354881948389060540120271)
    ·
      refine ⟨5032322922583590810180407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354881948389060540120271 5032322922583590810180407)
      ·
        refine ⟨7548484383875386215270611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032322922583590810180407 7548484383875386215270611)
        ·
          refine ⟨11322726575813079322905917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548484383875386215270611 11322726575813079322905917)
          ·
            refine ⟨4246022465929904746089719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11322726575813079322905917 4246022465929904746089719)
            ·
              refine ⟨6369033698894857119134579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246022465929904746089719 6369033698894857119134579)
              ·
                refine ⟨9553550548342285678701869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369033698894857119134579 9553550548342285678701869)
                ·
                  refine ⟨3582581455628357129513201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9553550548342285678701869 3582581455628357129513201)
                  ·
                    refine ⟨2686936091721267847134901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582581455628357129513201 2686936091721267847134901)
                    ·
                      refine ⟨251900258598868860668897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2686936091721267847134901 251900258598868860668897)
                      ·
                        rfl

theorem cell23_490574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_490574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490574 prefixEnd_490574 := by exact prefixLift 490574
  have htrace : WordTrace (prefixWord ++ tailWord_490574) baseStart_490574 baseEnd_490574 := by
    simpa [prefixWord, tailWord_490574, baseEnd_490574] using wordTrace_append hprefix tailTrace_490574
  have hstable : (prefixWord ++ tailWord_490574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490574).length < 2 ^ (prefixWord ++ tailWord_490574).sum := by decide
  have hdescent : baseEnd_490574 < baseStart_490574 := by decide
  rcases family_descends (prefixWord ++ tailWord_490574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490601 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 6, 2]
def baseStart_490601 : Nat := 118140960795 + 490601 * 2 ^ 59
def prefixEnd_490601 : Nat := 4983230072969 + 3 ^ 40 * 490601 * 2
def baseEnd_490601 : Nat := 251914122576540255031273

theorem tailTrace_490601 : CollatzResearch.WordTrace tailWord_490601 prefixEnd_490601 251914122576540255031273 := by
  unfold tailWord_490601
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893688495643839825207657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929125663762559883471771 17893688495643839825207657)
  ·
    refine ⟨13420266371732879868905743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17893688495643839825207657 13420266371732879868905743)
    ·
      refine ⟨20130399557599319803358615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13420266371732879868905743 20130399557599319803358615)
      ·
        refine ⟨30195599336398979705037923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20130399557599319803358615 30195599336398979705037923)
        ·
          refine ⟨45293399004598469557556885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30195599336398979705037923 45293399004598469557556885)
          ·
            refine ⟨2123128078340553260510479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45293399004598469557556885 2123128078340553260510479)
            ·
              refine ⟨3184692117510829890765719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123128078340553260510479 3184692117510829890765719)
              ·
                refine ⟨4777038176266244836148579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184692117510829890765719 4777038176266244836148579)
                ·
                  refine ⟨7165557264399367254222869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777038176266244836148579 7165557264399367254222869)
                  ·
                    refine ⟨335885496768720340041697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7165557264399367254222869 335885496768720340041697)
                    ·
                      refine ⟨251914122576540255031273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 335885496768720340041697 251914122576540255031273)
                      ·
                        rfl

theorem cell23_490601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6, 2].length) (baseStart_490601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490601 prefixEnd_490601 := by exact prefixLift 490601
  have htrace : WordTrace (prefixWord ++ tailWord_490601) baseStart_490601 baseEnd_490601 := by
    simpa [prefixWord, tailWord_490601, baseEnd_490601] using wordTrace_append hprefix tailTrace_490601
  have hstable : (prefixWord ++ tailWord_490601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490601).length < 2 ^ (prefixWord ++ tailWord_490601).sum := by decide
  have hdescent : baseEnd_490601 < baseStart_490601 := by decide
  rcases family_descends (prefixWord ++ tailWord_490601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490621 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_490621 : Nat := 118140960795 + 490621 * 2 ^ 59
def prefixEnd_490621 : Nat := 4983230072969 + 3 ^ 40 * 490621 * 2
def baseEnd_490621 : Nat := 251924392189630176781181

theorem tailTrace_490621 : CollatzResearch.WordTrace tailWord_490621 prefixEnd_490621 251924392189630176781181 := by
  unfold tailWord_490621
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894417955571383240935717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929611970380922160623811 17894417955571383240935717)
  ·
    refine ⟨3355203366669634357675447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17894417955571383240935717 3355203366669634357675447)
    ·
      refine ⟨5032805050004451536513171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355203366669634357675447 5032805050004451536513171)
      ·
        refine ⟨7549207575006677304769757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032805050004451536513171 7549207575006677304769757)
        ·
          refine ⟨2830952840627503989288659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7549207575006677304769757 2830952840627503989288659)
          ·
            refine ⟨4246429260941255983932989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830952840627503989288659 4246429260941255983932989)
            ·
              refine ⟨1592410972852970993974871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246429260941255983932989 1592410972852970993974871)
              ·
                refine ⟨2388616459279456490962307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592410972852970993974871 2388616459279456490962307)
                ·
                  refine ⟨3582924688919184736443461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388616459279456490962307 3582924688919184736443461)
                  ·
                    refine ⟨671798379172347138083149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3582924688919184736443461 671798379172347138083149)
                    ·
                      refine ⟨251924392189630176781181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671798379172347138083149 251924392189630176781181)
                      ·
                        rfl

theorem cell23_490621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_490621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490621 prefixEnd_490621 := by exact prefixLift 490621
  have htrace : WordTrace (prefixWord ++ tailWord_490621) baseStart_490621 baseEnd_490621 := by
    simpa [prefixWord, tailWord_490621, baseEnd_490621] using wordTrace_append hprefix tailTrace_490621
  have hstable : (prefixWord ++ tailWord_490621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490621).length < 2 ^ (prefixWord ++ tailWord_490621).sum := by decide
  have hdescent : baseEnd_490621 < baseStart_490621 := by decide
  rcases family_descends (prefixWord ++ tailWord_490621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490671 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 1, 5]
def baseStart_490671 : Nat := 118140960795 + 490671 * 2 ^ 59
def prefixEnd_490671 : Nat := 4983230072969 + 3 ^ 40 * 490671 * 2
def baseEnd_490671 : Nat := 83983355407451660385317

theorem tailTrace_490671 : CollatzResearch.WordTrace tailWord_490671 prefixEnd_490671 83983355407451660385317 := by
  unfold tailWord_490671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896241605390241780255867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11930827736926827853503911 17896241605390241780255867)
  ·
    refine ⟨26844362408085362670383801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17896241605390241780255867 26844362408085362670383801)
    ·
      refine ⟨20133271806064022002787851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26844362408085362670383801 20133271806064022002787851)
      ·
        refine ⟨30199907709096033004181777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133271806064022002787851 30199907709096033004181777)
        ·
          refine ⟨22649930781822024753136333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30199907709096033004181777 22649930781822024753136333)
          ·
            refine ⟨8493724043183259282426125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22649930781822024753136333 8493724043183259282426125)
            ·
              refine ⟨3185146516193722230909797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8493724043183259282426125 3185146516193722230909797)
              ·
                refine ⟨597214971786322918295587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3185146516193722230909797 597214971786322918295587)
                ·
                  refine ⟨895822457679484377443381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597214971786322918295587 895822457679484377443381)
                  ·
                    refine ⟨83983355407451660385317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 895822457679484377443381 83983355407451660385317)
                    ·
                      rfl

theorem cell23_490671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_490671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490671 prefixEnd_490671 := by exact prefixLift 490671
  have htrace : WordTrace (prefixWord ++ tailWord_490671) baseStart_490671 baseEnd_490671 := by
    simpa [prefixWord, tailWord_490671, baseEnd_490671] using wordTrace_append hprefix tailTrace_490671
  have hstable : (prefixWord ++ tailWord_490671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490671).length < 2 ^ (prefixWord ++ tailWord_490671).sum := by decide
  have hdescent : baseEnd_490671 < baseStart_490671 := by decide
  rcases family_descends (prefixWord ++ tailWord_490671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490702 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_490702 : Nat := 118140960795 + 490702 * 2 ^ 59
def prefixEnd_490702 : Nat := 4983230072969 + 3 ^ 40 * 490702 * 2
def baseEnd_490702 : Nat := 251965984122644359868309

theorem tailTrace_490702 : CollatzResearch.WordTrace tailWord_490702 prefixEnd_490702 251965984122644359868309 := by
  unfold tailWord_490702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237171533534741759329295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11931581512185289383089573 2237171533534741759329295)
  ·
    refine ⟨3355757300302112638993943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237171533534741759329295 3355757300302112638993943)
    ·
      refine ⟨5033635950453168958490915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355757300302112638993943 5033635950453168958490915)
      ·
        refine ⟨7550453925679753437736373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033635950453168958490915 7550453925679753437736373)
        ·
          refine ⟨707855055532476884787785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7550453925679753437736373 707855055532476884787785)
          ·
            refine ⟨530891291649357663590839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707855055532476884787785 530891291649357663590839)
            ·
              refine ⟨796336937474036495386259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530891291649357663590839 796336937474036495386259)
              ·
                refine ⟨1194505406211054743079389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796336937474036495386259 1194505406211054743079389)
                ·
                  refine ⟨447939527329145528654771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194505406211054743079389 447939527329145528654771)
                  ·
                    refine ⟨671909290993718292982157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 447939527329145528654771 671909290993718292982157)
                    ·
                      refine ⟨251965984122644359868309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671909290993718292982157 251965984122644359868309)
                      ·
                        rfl

theorem cell23_490702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_490702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490702 prefixEnd_490702 := by exact prefixLift 490702
  have htrace : WordTrace (prefixWord ++ tailWord_490702) baseStart_490702 baseEnd_490702 := by
    simpa [prefixWord, tailWord_490702, baseEnd_490702] using wordTrace_append hprefix tailTrace_490702
  have hstable : (prefixWord ++ tailWord_490702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490702).length < 2 ^ (prefixWord ++ tailWord_490702).sum := by decide
  have hdescent : baseEnd_490702 < baseStart_490702 := by decide
  rcases family_descends (prefixWord ++ tailWord_490702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490711 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_490711 : Nat := 118140960795 + 490711 * 2 ^ 59
def prefixEnd_490711 : Nat := 4983230072969 + 3 ^ 40 * 490711 * 2
def baseEnd_490711 : Nat := 251970605448534824655767

theorem tailTrace_490711 : CollatzResearch.WordTrace tailWord_490711 prefixEnd_490711 251970605448534824655767 := by
  unfold tailWord_490711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897700525245328611711987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11931800350163552407807991 17897700525245328611711987)
  ·
    refine ⟨26846550787867992917567981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17897700525245328611711987 26846550787867992917567981)
    ·
      refine ⟨10067456545450497344087993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26846550787867992917567981 10067456545450497344087993)
      ·
        refine ⟨7550592409087873008065995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10067456545450497344087993 7550592409087873008065995)
        ·
          refine ⟨11325888613631809512098993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550592409087873008065995 11325888613631809512098993)
          ·
            refine ⟨8494416460223857134074245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11325888613631809512098993 8494416460223857134074245)
            ·
              refine ⟨1592703086291973212638921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8494416460223857134074245 1592703086291973212638921)
              ·
                refine ⟨1194527314718979909479191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592703086291973212638921 1194527314718979909479191)
                ·
                  refine ⟨1791790972078469864218787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194527314718979909479191 1791790972078469864218787)
                  ·
                    refine ⟨2687686458117704796328181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791790972078469864218787 2687686458117704796328181)
                    ·
                      refine ⟨251970605448534824655767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2687686458117704796328181 251970605448534824655767)
                      ·
                        rfl

theorem cell23_490711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_490711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490711 prefixEnd_490711 := by exact prefixLift 490711
  have htrace : WordTrace (prefixWord ++ tailWord_490711) baseStart_490711 baseEnd_490711 := by
    simpa [prefixWord, tailWord_490711, baseEnd_490711] using wordTrace_append hprefix tailTrace_490711
  have hstable : (prefixWord ++ tailWord_490711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490711).length < 2 ^ (prefixWord ++ tailWord_490711).sum := by decide
  have hdescent : baseEnd_490711 < baseStart_490711 := by decide
  rcases family_descends (prefixWord ++ tailWord_490711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490721 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_490721 : Nat := 118140960795 + 490721 * 2 ^ 59
def prefixEnd_490721 : Nat := 4983230072969 + 3 ^ 40 * 490721 * 2
def baseEnd_490721 : Nat := 251975740255079785530721

theorem tailTrace_490721 : CollatzResearch.WordTrace tailWord_490721 prefixEnd_490721 251975740255079785530721 := by
  unfold tailWord_490721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898065255209100319576017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11932043503472733546384011 17898065255209100319576017)
  ·
    refine ⟨13423548941406825239682013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17898065255209100319576017 13423548941406825239682013)
    ·
      refine ⟨5033830853027559464880755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13423548941406825239682013 5033830853027559464880755)
      ·
        refine ⟨7550746279541339197321133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033830853027559464880755 7550746279541339197321133)
        ·
          refine ⟨2831529854828002198995425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7550746279541339197321133 2831529854828002198995425)
          ·
            refine ⟨2123647391121001649246569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2831529854828002198995425 2123647391121001649246569)
            ·
              refine ⟨1592735543340751236934927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123647391121001649246569 1592735543340751236934927)
              ·
                refine ⟨2389103315011126855402391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592735543340751236934927 2389103315011126855402391)
                ·
                  refine ⟨3583654972516690283103587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389103315011126855402391 3583654972516690283103587)
                  ·
                    refine ⟨5375482458775035424655381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583654972516690283103587 5375482458775035424655381)
                    ·
                      refine ⟨251975740255079785530721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5375482458775035424655381 251975740255079785530721)
                      ·
                        rfl

theorem cell23_490721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_490721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490721 prefixEnd_490721 := by exact prefixLift 490721
  have htrace : WordTrace (prefixWord ++ tailWord_490721) baseStart_490721 baseEnd_490721 := by
    simpa [prefixWord, tailWord_490721, baseEnd_490721] using wordTrace_append hprefix tailTrace_490721
  have hstable : (prefixWord ++ tailWord_490721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490721).length < 2 ^ (prefixWord ++ tailWord_490721).sum := by decide
  have hdescent : baseEnd_490721 < baseStart_490721 := by decide
  rcases family_descends (prefixWord ++ tailWord_490721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490728 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_490728 : Nat := 118140960795 + 490728 * 2 ^ 59
def prefixEnd_490728 : Nat := 4983230072969 + 3 ^ 40 * 490728 * 2
def baseEnd_490728 : Nat := 251979334619661258143189

theorem tailTrace_490728 : CollatzResearch.WordTrace tailWord_490728 prefixEnd_490728 251979334619661258143189 := by
  unfold tailWord_490728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949160283091870257540419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11932213710789160343387225 8949160283091870257540419)
  ·
    refine ⟨13423740424637805386310629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949160283091870257540419 13423740424637805386310629)
    ·
      refine ⟨2516951329619588509933243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13423740424637805386310629 2516951329619588509933243)
      ·
        refine ⟨3775426994429382764899865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516951329619588509933243 3775426994429382764899865)
        ·
          refine ⟨2831570245822037073674899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775426994429382764899865 2831570245822037073674899)
          ·
            refine ⟨4247355368733055610512349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831570245822037073674899 4247355368733055610512349)
            ·
              refine ⟨1592758263274895853942131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4247355368733055610512349 1592758263274895853942131)
              ·
                refine ⟨2389137394912343780913197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592758263274895853942131 2389137394912343780913197)
                ·
                  refine ⟨895926523092128917842449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2389137394912343780913197 895926523092128917842449)
                  ·
                    refine ⟨671944892319096688381837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895926523092128917842449 671944892319096688381837)
                    ·
                      refine ⟨251979334619661258143189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671944892319096688381837 251979334619661258143189)
                      ·
                        rfl

theorem cell23_490728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_490728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490728 prefixEnd_490728 := by exact prefixLift 490728
  have htrace : WordTrace (prefixWord ++ tailWord_490728) baseStart_490728 baseEnd_490728 := by
    simpa [prefixWord, tailWord_490728, baseEnd_490728] using wordTrace_append hprefix tailTrace_490728
  have hstable : (prefixWord ++ tailWord_490728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490728).length < 2 ^ (prefixWord ++ tailWord_490728).sum := by decide
  have hdescent : baseEnd_490728 < baseStart_490728 := by decide
  rcases family_descends (prefixWord ++ tailWord_490728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490745 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 1, 2, 3]
def baseStart_490745 : Nat := 118140960795 + 490745 * 2 ^ 59
def prefixEnd_490745 : Nat := 4983230072969 + 3 ^ 40 * 490745 * 2
def baseEnd_490745 : Nat := 251988063790787691630611

theorem tailTrace_490745 : CollatzResearch.WordTrace tailWord_490745 prefixEnd_490745 251988063790787691630611 := by
  unfold tailWord_490745
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898940607122152418449689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11932627071414768278966459 17898940607122152418449689)
  ·
    refine ⟨13424205455341614313837267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17898940607122152418449689 13424205455341614313837267)
    ·
      refine ⟨20136308183012421470755901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424205455341614313837267 20136308183012421470755901)
      ·
        refine ⟨7551115568629658051533463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20136308183012421470755901 7551115568629658051533463)
        ·
          refine ⟨11326673352944487077300195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551115568629658051533463 11326673352944487077300195)
          ·
            refine ⟨16990010029416730615950293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11326673352944487077300195 16990010029416730615950293)
            ·
              refine ⟨398203360064454623811335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16990010029416730615950293 398203360064454623811335)
              ·
                refine ⟨597305040096681935717003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398203360064454623811335 597305040096681935717003)
                ·
                  refine ⟨895957560145022903575505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597305040096681935717003 895957560145022903575505)
                  ·
                    refine ⟨671968170108767177681629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895957560145022903575505 671968170108767177681629)
                    ·
                      refine ⟨251988063790787691630611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 671968170108767177681629 251988063790787691630611)
                      ·
                        rfl

theorem cell23_490745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_490745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490745 prefixEnd_490745 := by exact prefixLift 490745
  have htrace : WordTrace (prefixWord ++ tailWord_490745) baseStart_490745 baseEnd_490745 := by
    simpa [prefixWord, tailWord_490745, baseEnd_490745] using wordTrace_append hprefix tailTrace_490745
  have hstable : (prefixWord ++ tailWord_490745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490745).length < 2 ^ (prefixWord ++ tailWord_490745).sum := by decide
  have hdescent : baseEnd_490745 < baseStart_490745 := by decide
  rcases family_descends (prefixWord ++ tailWord_490745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490775 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_490775 : Nat := 118140960795 + 490775 * 2 ^ 59
def prefixEnd_490775 : Nat := 4983230072969 + 3 ^ 40 * 490775 * 2
def baseEnd_490775 : Nat := 252003468210422574255473

theorem tailTrace_490775 : CollatzResearch.WordTrace tailWord_490775 prefixEnd_490775 252003468210422574255473 := by
  unfold tailWord_490775
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900034797013467542041779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11933356531342311694694519 17900034797013467542041779)
  ·
    refine ⟨26850052195520201313062669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17900034797013467542041779 26850052195520201313062669)
    ·
      refine ⟨10068769573320075492398501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26850052195520201313062669 10068769573320075492398501)
      ·
        refine ⟨1887894294997514154824719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10068769573320075492398501 1887894294997514154824719)
        ·
          refine ⟨2831841442496271232237079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887894294997514154824719 2831841442496271232237079)
          ·
            refine ⟨4247762163744406848355619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831841442496271232237079 4247762163744406848355619)
            ·
              refine ⟨6371643245616610272533429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247762163744406848355619 6371643245616610272533429)
              ·
                refine ⟨597341554276557213050009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6371643245616610272533429 597341554276557213050009)
                ·
                  refine ⟨448006165707417909787507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597341554276557213050009 448006165707417909787507)
                  ·
                    refine ⟨672009248561126864681261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448006165707417909787507 672009248561126864681261)
                    ·
                      refine ⟨252003468210422574255473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672009248561126864681261 252003468210422574255473)
                      ·
                        rfl

theorem cell23_490775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_490775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490775 prefixEnd_490775 := by exact prefixLift 490775
  have htrace : WordTrace (prefixWord ++ tailWord_490775) baseStart_490775 baseEnd_490775 := by
    simpa [prefixWord, tailWord_490775, baseEnd_490775] using wordTrace_append hprefix tailTrace_490775
  have hstable : (prefixWord ++ tailWord_490775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490775).length < 2 ^ (prefixWord ++ tailWord_490775).sum := by decide
  have hdescent : baseEnd_490775 < baseStart_490775 := by decide
  rcases family_descends (prefixWord ++ tailWord_490775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490782 : List Nat := [4, 3, 2, 1, 2, 1, 3, 7]
def baseStart_490782 : Nat := 118140960795 + 490782 * 2 ^ 59
def prefixEnd_490782 : Nat := 4983230072969 + 3 ^ 40 * 490782 * 2
def baseEnd_490782 : Nat := 9333594910185335069183

theorem tailTrace_490782 : CollatzResearch.WordTrace tailWord_490782 prefixEnd_490782 9333594910185335069183 := by
  unfold tailWord_490782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237536263498513467193325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11933526738658738491697733 2237536263498513467193325)
  ·
    refine ⟨839076098811942550197497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2237536263498513467193325 839076098811942550197497)
    ·
      refine ⟨629307074108956912648123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839076098811942550197497 629307074108956912648123)
      ·
        refine ⟨943960611163435368972185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629307074108956912648123 943960611163435368972185)
        ·
          refine ⟨707970458372576526729139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943960611163435368972185 707970458372576526729139)
          ·
            refine ⟨1061955687558864790093709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707970458372576526729139 1061955687558864790093709)
            ·
              refine ⟨398233382834574296285141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061955687558864790093709 398233382834574296285141)
              ·
                refine ⟨9333594910185335069183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398233382834574296285141 9333594910185335069183)
                ·
                  rfl

theorem cell23_490782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_490782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490782 prefixEnd_490782 := by exact prefixLift 490782
  have htrace : WordTrace (prefixWord ++ tailWord_490782) baseStart_490782 baseEnd_490782 := by
    simpa [prefixWord, tailWord_490782, baseEnd_490782] using wordTrace_append hprefix tailTrace_490782
  have hstable : (prefixWord ++ tailWord_490782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490782).length < 2 ^ (prefixWord ++ tailWord_490782).sum := by decide
  have hdescent : baseEnd_490782 < baseStart_490782 := by decide
  rcases family_descends (prefixWord ++ tailWord_490782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490785 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_490785 : Nat := 118140960795 + 490785 * 2 ^ 59
def prefixEnd_490785 : Nat := 4983230072969 + 3 ^ 40 * 490785 * 2
def baseEnd_490785 : Nat := 252008603016967535130427

theorem tailTrace_490785 : CollatzResearch.WordTrace tailWord_490785 prefixEnd_490785 252008603016967535130427 := by
  unfold tailWord_490785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900399526977239249905809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11933599684651492833270539 17900399526977239249905809)
  ·
    refine ⟨13425299645232929437429357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17900399526977239249905809 13425299645232929437429357)
    ·
      refine ⟨5034487366962348539036009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13425299645232929437429357 5034487366962348539036009)
      ·
        refine ⟨3775865525221761404277007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034487366962348539036009 3775865525221761404277007)
        ·
          refine ⟨5663798287832642106415511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775865525221761404277007 5663798287832642106415511)
          ·
            refine ⟨8495697431748963159623267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663798287832642106415511 8495697431748963159623267)
            ·
              refine ⟨12743546147623444739434901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495697431748963159623267 12743546147623444739434901)
              ·
                refine ⟨597353725669848972161011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12743546147623444739434901 597353725669848972161011)
                ·
                  refine ⟨896030588504773458241517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597353725669848972161011 896030588504773458241517)
                  ·
                    refine ⟨336011470689290046840569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896030588504773458241517 336011470689290046840569)
                    ·
                      refine ⟨252008603016967535130427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336011470689290046840569 252008603016967535130427)
                      ·
                        rfl

theorem cell23_490785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_490785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490785 prefixEnd_490785 := by exact prefixLift 490785
  have htrace : WordTrace (prefixWord ++ tailWord_490785) baseStart_490785 baseEnd_490785 := by
    simpa [prefixWord, tailWord_490785, baseEnd_490785] using wordTrace_append hprefix tailTrace_490785
  have hstable : (prefixWord ++ tailWord_490785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490785).length < 2 ^ (prefixWord ++ tailWord_490785).sum := by decide
  have hdescent : baseEnd_490785 < baseStart_490785 := by decide
  rcases family_descends (prefixWord ++ tailWord_490785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490802 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_490802 : Nat := 118140960795 + 490802 * 2 ^ 59
def prefixEnd_490802 : Nat := 4983230072969 + 3 ^ 40 * 490802 * 2
def baseEnd_490802 : Nat := 252017332188093968617849

theorem tailTrace_490802 : CollatzResearch.WordTrace tailWord_490802 prefixEnd_490802 252017332188093968617849 := by
  unfold tailWord_490802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475254891978912788318665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11934013045277100768849773 4475254891978912788318665)
  ·
    refine ⟨3356441168984184591238999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4475254891978912788318665 3356441168984184591238999)
    ·
      refine ⟨5034661753476276886858499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356441168984184591238999 5034661753476276886858499)
      ·
        refine ⟨7551992630214415330287749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034661753476276886858499 7551992630214415330287749)
        ·
          refine ⟨1415998618165202874428953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7551992630214415330287749 1415998618165202874428953)
          ·
            refine ⟨1061998963623902155821715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415998618165202874428953 1061998963623902155821715)
            ·
              refine ⟨1592998445435853233732573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061998963623902155821715 1592998445435853233732573)
              ·
                refine ⟨597374417038444962649715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592998445435853233732573 597374417038444962649715)
                ·
                  refine ⟨896061625557667443974573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597374417038444962649715 896061625557667443974573)
                  ·
                    refine ⟨336023109584125291490465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896061625557667443974573 336023109584125291490465)
                    ·
                      refine ⟨252017332188093968617849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336023109584125291490465 252017332188093968617849)
                      ·
                        rfl

theorem cell23_490802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_490802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490802 prefixEnd_490802 := by exact prefixLift 490802
  have htrace : WordTrace (prefixWord ++ tailWord_490802) baseStart_490802 baseEnd_490802 := by
    simpa [prefixWord, tailWord_490802, baseEnd_490802] using wordTrace_append hprefix tailTrace_490802
  have hstable : (prefixWord ++ tailWord_490802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490802).length < 2 ^ (prefixWord ++ tailWord_490802).sum := by decide
  have hdescent : baseEnd_490802 < baseStart_490802 := by decide
  rcases family_descends (prefixWord ++ tailWord_490802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490809 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_490809 : Nat := 118140960795 + 490809 * 2 ^ 59
def prefixEnd_490809 : Nat := 4983230072969 + 3 ^ 40 * 490809 * 2
def baseEnd_490809 : Nat := 252020926552675441230317

theorem tailTrace_490809 : CollatzResearch.WordTrace tailWord_490809 prefixEnd_490809 252020926552675441230317 := by
  unfold tailWord_490809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901274878890291348779481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11934183252593527565852987 17901274878890291348779481)
  ·
    refine ⟨13425956159167718511584611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17901274878890291348779481 13425956159167718511584611)
    ·
      refine ⟨20138934238751577767376917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425956159167718511584611 20138934238751577767376917)
      ·
        refine ⟨944012542441480207845793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20138934238751577767376917 944012542441480207845793)
        ·
          refine ⟨708009406831110155884345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944012542441480207845793 708009406831110155884345)
          ·
            refine ⟨531007055123332616913259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708009406831110155884345 531007055123332616913259)
            ·
              refine ⟨796510582684998925369889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531007055123332616913259 796510582684998925369889)
              ·
                refine ⟨597382937013749194027417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796510582684998925369889 597382937013749194027417)
                ·
                  refine ⟨448037202760311895520563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597382937013749194027417 448037202760311895520563)
                  ·
                    refine ⟨672055804140467843280845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448037202760311895520563 672055804140467843280845)
                    ·
                      refine ⟨252020926552675441230317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672055804140467843280845 252020926552675441230317)
                      ·
                        rfl

theorem cell23_490809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_490809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490809 prefixEnd_490809 := by exact prefixLift 490809
  have htrace : WordTrace (prefixWord ++ tailWord_490809) baseStart_490809 baseEnd_490809 := by
    simpa [prefixWord, tailWord_490809, baseEnd_490809] using wordTrace_append hprefix tailTrace_490809
  have hstable : (prefixWord ++ tailWord_490809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490809).length < 2 ^ (prefixWord ++ tailWord_490809).sum := by decide
  have hdescent : baseEnd_490809 < baseStart_490809 := by decide
  rcases family_descends (prefixWord ++ tailWord_490809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490828 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_490828 : Nat := 118140960795 + 490828 * 2 ^ 59
def prefixEnd_490828 : Nat := 4983230072969 + 3 ^ 40 * 490828 * 2
def baseEnd_490828 : Nat := 252030682685110866892729

theorem tailTrace_490828 : CollatzResearch.WordTrace tailWord_490828 prefixEnd_490828 252030682685110866892729 := by
  unfold tailWord_490828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950983932910728796860569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11934645243880971729147425 8950983932910728796860569)
  ·
    refine ⟨6713237949683046597645427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8950983932910728796860569 6713237949683046597645427)
    ·
      refine ⟨10069856924524569896468141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713237949683046597645427 10069856924524569896468141)
      ·
        refine ⟨3776196346696713711175553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10069856924524569896468141 3776196346696713711175553)
        ·
          refine ⟨2832147260022535283381665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3776196346696713711175553 2832147260022535283381665)
          ·
            refine ⟨2124110445016901462536249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832147260022535283381665 2124110445016901462536249)
            ·
              refine ⟨1593082833762676096902187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124110445016901462536249 1593082833762676096902187)
              ·
                refine ⟨2389624250644014145353281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593082833762676096902187 2389624250644014145353281)
                ·
                  refine ⟨1792218187983010609014961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389624250644014145353281 1792218187983010609014961)
                  ·
                    refine ⟨1344163640987257956761221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792218187983010609014961 1344163640987257956761221)
                    ·
                      refine ⟨252030682685110866892729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1344163640987257956761221 252030682685110866892729)
                      ·
                        rfl

theorem cell23_490828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_490828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490828 prefixEnd_490828 := by exact prefixLift 490828
  have htrace : WordTrace (prefixWord ++ tailWord_490828) baseStart_490828 baseEnd_490828 := by
    simpa [prefixWord, tailWord_490828, baseEnd_490828] using wordTrace_append hprefix tailTrace_490828
  have hstable : (prefixWord ++ tailWord_490828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490828).length < 2 ^ (prefixWord ++ tailWord_490828).sum := by decide
  have hdescent : baseEnd_490828 < baseStart_490828 := by decide
  rcases family_descends (prefixWord ++ tailWord_490828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490905 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_490905 : Nat := 118140960795 + 490905 * 2 ^ 59
def prefixEnd_490905 : Nat := 4983230072969 + 3 ^ 40 * 490905 * 2
def baseEnd_490905 : Nat := 252070220695507065629875

theorem tailTrace_490905 : CollatzResearch.WordTrace tailWord_490905 prefixEnd_490905 252070220695507065629875 := by
  unfold tailWord_490905
  simp only [CollatzResearch.WordTrace]
  refine ⟨17904776286542499744274169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11936517524361666496182779 17904776286542499744274169)
  ·
    refine ⟨13428582214906874808205627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17904776286542499744274169 13428582214906874808205627)
    ·
      refine ⟨20142873322360312212308441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13428582214906874808205627 20142873322360312212308441)
      ·
        refine ⟨15107154991770234159231331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20142873322360312212308441 15107154991770234159231331)
        ·
          refine ⟨22660732487655351238846997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107154991770234159231331 22660732487655351238846997)
          ·
            refine ⟨1062221835358844589320953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22660732487655351238846997 1062221835358844589320953)
            ·
              refine ⟨796666376519133441990715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062221835358844589320953 796666376519133441990715)
              ·
                refine ⟨1194999564778700162986073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796666376519133441990715 1194999564778700162986073)
                ·
                  refine ⟨896249673584025122239555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194999564778700162986073 896249673584025122239555)
                  ·
                    refine ⟨1344374510376037683359333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896249673584025122239555 1344374510376037683359333)
                    ·
                      refine ⟨252070220695507065629875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1344374510376037683359333 252070220695507065629875)
                      ·
                        rfl

theorem cell23_490905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_490905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490905 prefixEnd_490905 := by exact prefixLift 490905
  have htrace : WordTrace (prefixWord ++ tailWord_490905) baseStart_490905 baseEnd_490905 := by
    simpa [prefixWord, tailWord_490905, baseEnd_490905] using wordTrace_append hprefix tailTrace_490905
  have hstable : (prefixWord ++ tailWord_490905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490905).length < 2 ^ (prefixWord ++ tailWord_490905).sum := by decide
  have hdescent : baseEnd_490905 < baseStart_490905 := by decide
  rcases family_descends (prefixWord ++ tailWord_490905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490938 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_490938 : Nat := 118140960795 + 490938 * 2 ^ 59
def prefixEnd_490938 : Nat := 4983230072969 + 3 ^ 40 * 490938 * 2
def baseEnd_490938 : Nat := 252087165557105436517223

theorem tailTrace_490938 : CollatzResearch.WordTrace tailWord_490938 prefixEnd_490938 252087165557105436517223 := by
  unfold tailWord_490938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476494973855736595056367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11937319930281964253483645 4476494973855736595056367)
  ·
    refine ⟨6714742460783604892584551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4476494973855736595056367 6714742460783604892584551)
    ·
      refine ⟨10072113691175407338876827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6714742460783604892584551 10072113691175407338876827)
      ·
        refine ⟨15108170536763111008315241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072113691175407338876827 15108170536763111008315241)
        ·
          refine ⟨11331127902572333256236431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15108170536763111008315241 11331127902572333256236431)
          ·
            refine ⟨16996691853858499884354647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331127902572333256236431 16996691853858499884354647)
            ·
              refine ⟨25495037780787749826531971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996691853858499884354647 25495037780787749826531971)
              ·
                refine ⟨38242556671181624739797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25495037780787749826531971 38242556671181624739797957)
                ·
                  refine ⟨7170479375846554638712117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38242556671181624739797957 7170479375846554638712117)
                  ·
                    refine ⟨672232441485614497379261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7170479375846554638712117 672232441485614497379261)
                    ·
                      refine ⟨252087165557105436517223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672232441485614497379261 252087165557105436517223)
                      ·
                        rfl

theorem cell23_490938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_490938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490938 prefixEnd_490938 := by exact prefixLift 490938
  have htrace : WordTrace (prefixWord ++ tailWord_490938) baseStart_490938 baseEnd_490938 := by
    simpa [prefixWord, tailWord_490938, baseEnd_490938] using wordTrace_append hprefix tailTrace_490938
  have hstable : (prefixWord ++ tailWord_490938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490938).length < 2 ^ (prefixWord ++ tailWord_490938).sum := by decide
  have hdescent : baseEnd_490938 < baseStart_490938 := by decide
  rcases family_descends (prefixWord ++ tailWord_490938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490955 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 3]
def baseStart_490955 : Nat := 118140960795 + 490955 * 2 ^ 59
def prefixEnd_490955 : Nat := 4983230072969 + 3 ^ 40 * 490955 * 2
def baseEnd_490955 : Nat := 252095894728231870004645

theorem tailTrace_490955 : CollatzResearch.WordTrace tailWord_490955 prefixEnd_490955 252095894728231870004645 := by
  unfold tailWord_490955
  simp only [CollatzResearch.WordTrace]
  refine ⟨17906599936361358283594319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11937733290907572189062879 17906599936361358283594319)
  ·
    refine ⟨26859899904542037425391479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17906599936361358283594319 26859899904542037425391479)
    ·
      refine ⟨40289849856813056138087219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26859899904542037425391479 40289849856813056138087219)
      ·
        refine ⟨60434774785219584207130829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40289849856813056138087219 60434774785219584207130829)
        ·
          refine ⟨22663040544457344077674061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60434774785219584207130829 22663040544457344077674061)
          ·
            refine ⟨8498640204171504029127773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22663040544457344077674061 8498640204171504029127773)
            ·
              refine ⟨3186990076564314010922915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8498640204171504029127773 3186990076564314010922915)
              ·
                refine ⟨4780485114846471016384373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186990076564314010922915 4780485114846471016384373)
                ·
                  refine ⟨448170479516856657786035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4780485114846471016384373 448170479516856657786035)
                  ·
                    refine ⟨672255719275284986679053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448170479516856657786035 672255719275284986679053)
                    ·
                      refine ⟨252095894728231870004645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672255719275284986679053 252095894728231870004645)
                      ·
                        rfl

theorem cell23_490955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 3].length) (baseStart_490955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490955 prefixEnd_490955 := by exact prefixLift 490955
  have htrace : WordTrace (prefixWord ++ tailWord_490955) baseStart_490955 baseEnd_490955 := by
    simpa [prefixWord, tailWord_490955, baseEnd_490955] using wordTrace_append hprefix tailTrace_490955
  have hstable : (prefixWord ++ tailWord_490955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490955).length < 2 ^ (prefixWord ++ tailWord_490955).sum := by decide
  have hdescent : baseEnd_490955 < baseStart_490955 := by decide
  rcases family_descends (prefixWord ++ tailWord_490955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490966 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_490966 : Nat := 118140960795 + 490966 * 2 ^ 59
def prefixEnd_490966 : Nat := 4983230072969 + 3 ^ 40 * 490966 * 2
def baseEnd_490966 : Nat := 84033847671810442322365

theorem tailTrace_490966 : CollatzResearch.WordTrace tailWord_490966 prefixEnd_490966 84033847671810442322365 := by
  unfold tailWord_490966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119187571207594197640297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11938000759547671441496501 1119187571207594197640297)
  ·
    refine ⟨839390678405695648230223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119187571207594197640297 839390678405695648230223)
    ·
      refine ⟨1259086017608543472345335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839390678405695648230223 1259086017608543472345335)
      ·
        refine ⟨1888629026412815208518003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259086017608543472345335 1888629026412815208518003)
        ·
          refine ⟨2832943539619222812777005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888629026412815208518003 2832943539619222812777005)
          ·
            refine ⟨1062353827357208554791377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2832943539619222812777005 1062353827357208554791377)
            ·
              refine ⟨796765370517906416093533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062353827357208554791377 796765370517906416093533)
              ·
                refine ⟨298787013944214906035075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796765370517906416093533 298787013944214906035075)
                ·
                  refine ⟨448180520916322359052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298787013944214906035075 448180520916322359052613)
                  ·
                    refine ⟨84033847671810442322365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448180520916322359052613 84033847671810442322365)
                    ·
                      rfl

theorem cell23_490966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_490966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490966 prefixEnd_490966 := by exact prefixLift 490966
  have htrace : WordTrace (prefixWord ++ tailWord_490966) baseStart_490966 baseEnd_490966 := by
    simpa [prefixWord, tailWord_490966, baseEnd_490966] using wordTrace_append hprefix tailTrace_490966
  have hstable : (prefixWord ++ tailWord_490966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490966).length < 2 ^ (prefixWord ++ tailWord_490966).sum := by decide
  have hdescent : baseEnd_490966 < baseStart_490966 := by decide
  rcases family_descends (prefixWord ++ tailWord_490966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490975 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 1, 5]
def baseStart_490975 : Nat := 118140960795 + 490975 * 2 ^ 59
def prefixEnd_490975 : Nat := 4983230072969 + 3 ^ 40 * 490975 * 2
def baseEnd_490975 : Nat := 84035388113773930584851

theorem tailTrace_490975 : CollatzResearch.WordTrace tailWord_490975 prefixEnd_490975 84035388113773930584851 := by
  unfold tailWord_490975
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907329396288901699322379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938219597525934466214919 17907329396288901699322379)
  ·
    refine ⟨26860994094433352548983569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17907329396288901699322379 26860994094433352548983569)
    ·
      refine ⟨20145745570825014411737677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26860994094433352548983569 20145745570825014411737677)
      ·
        refine ⟨7554654589059380404401629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20145745570825014411737677 7554654589059380404401629)
        ·
          refine ⟨2832995470897267651650611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7554654589059380404401629 2832995470897267651650611)
          ·
            refine ⟨4249493206345901477475917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832995470897267651650611 4249493206345901477475917)
            ·
              refine ⟨1593559952379713054053469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249493206345901477475917 1593559952379713054053469)
              ·
                refine ⟨597584982142392395270051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593559952379713054053469 597584982142392395270051)
                ·
                  refine ⟨896377473213588592905077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597584982142392395270051 896377473213588592905077)
                  ·
                    refine ⟨84035388113773930584851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 896377473213588592905077 84035388113773930584851)
                    ·
                      rfl

theorem cell23_490975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_490975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_490975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_490975 prefixEnd_490975 := by exact prefixLift 490975
  have htrace : WordTrace (prefixWord ++ tailWord_490975) baseStart_490975 baseEnd_490975 := by
    simpa [prefixWord, tailWord_490975, baseEnd_490975] using wordTrace_append hprefix tailTrace_490975
  have hstable : (prefixWord ++ tailWord_490975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490975).length < 2 ^ (prefixWord ++ tailWord_490975).sum := by decide
  have hdescent : baseEnd_490975 < baseStart_490975 := by decide
  rcases family_descends (prefixWord ++ tailWord_490975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491005 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_491005 : Nat := 118140960795 + 491005 * 2 ^ 59
def prefixEnd_491005 : Nat := 4983230072969 + 3 ^ 40 * 491005 * 2
def baseEnd_491005 : Nat := 84040522920318891459805

theorem tailTrace_491005 : CollatzResearch.WordTrace tailWord_491005 prefixEnd_491005 84040522920318891459805 := by
  unfold tailWord_491005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908423586180216822914469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938949057453477881942979 17908423586180216822914469)
  ·
    refine ⟨3357829422408790654296463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17908423586180216822914469 3357829422408790654296463)
    ·
      refine ⟨5036744133613185981444695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357829422408790654296463 5036744133613185981444695)
      ·
        refine ⟨7555116200419778972167043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036744133613185981444695 7555116200419778972167043)
        ·
          refine ⟨11332674300629668458250565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555116200419778972167043 11332674300629668458250565)
          ·
            refine ⟨2124876431368062835921981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11332674300629668458250565 2124876431368062835921981)
            ·
              refine ⟨796828661763023563470743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124876431368062835921981 796828661763023563470743)
              ·
                refine ⟨1195242992644535345206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796828661763023563470743 1195242992644535345206115)
                ·
                  refine ⟨1792864488966803017809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195242992644535345206115 1792864488966803017809173)
                  ·
                    refine ⟨84040522920318891459805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1792864488966803017809173 84040522920318891459805)
                    ·
                      rfl

theorem cell23_491005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_491005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491005 prefixEnd_491005 := by exact prefixLift 491005
  have htrace : WordTrace (prefixWord ++ tailWord_491005) baseStart_491005 baseEnd_491005 := by
    simpa [prefixWord, tailWord_491005, baseEnd_491005] using wordTrace_append hprefix tailTrace_491005
  have hstable : (prefixWord ++ tailWord_491005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491005).length < 2 ^ (prefixWord ++ tailWord_491005).sum := by decide
  have hdescent : baseEnd_491005 < baseStart_491005 := by decide
  rcases family_descends (prefixWord ++ tailWord_491005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491032 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_491032 : Nat := 118140960795 + 491032 * 2 ^ 59
def prefixEnd_491032 : Nat := 4983230072969 + 3 ^ 40 * 491032 * 2
def baseEnd_491032 : Nat := 252135432738628068741791

theorem tailTrace_491032 : CollatzResearch.WordTrace tailWord_491032 prefixEnd_491032 252135432738628068741791 := by
  unfold tailWord_491032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954704178541200217073675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11939605571388266956098233 8954704178541200217073675)
  ·
    refine ⟨13432056267811800325610513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954704178541200217073675 13432056267811800325610513)
    ·
      refine ⟨10074042200858850244207885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13432056267811800325610513 10074042200858850244207885)
      ·
        refine ⟨3777765825322068841577957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10074042200858850244207885 3777765825322068841577957)
        ·
          refine ⟨708331092247887907795867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3777765825322068841577957 708331092247887907795867)
          ·
            refine ⟨1062496638371831861693801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708331092247887907795867 1062496638371831861693801)
            ·
              refine ⟨796872478778873896270351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062496638371831861693801 796872478778873896270351)
              ·
                refine ⟨1195308718168310844405527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796872478778873896270351 1195308718168310844405527)
                ·
                  refine ⟨1792963077252466266608291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195308718168310844405527 1792963077252466266608291)
                  ·
                    refine ⟨2689444615878699399912437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792963077252466266608291 2689444615878699399912437)
                    ·
                      refine ⟨252135432738628068741791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2689444615878699399912437 252135432738628068741791)
                      ·
                        rfl

theorem cell23_491032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_491032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491032 prefixEnd_491032 := by exact prefixLift 491032
  have htrace : WordTrace (prefixWord ++ tailWord_491032) baseStart_491032 baseEnd_491032 := by
    simpa [prefixWord, tailWord_491032, baseEnd_491032] using wordTrace_append hprefix tailTrace_491032
  have hstable : (prefixWord ++ tailWord_491032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491032).length < 2 ^ (prefixWord ++ tailWord_491032).sum := by decide
  have hdescent : baseEnd_491032 < baseStart_491032 := by decide
  rcases family_descends (prefixWord ++ tailWord_491032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491105 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_491105 : Nat := 118140960795 + 491105 * 2 ^ 59
def prefixEnd_491105 : Nat := 4983230072969 + 3 ^ 40 * 491105 * 2
def baseEnd_491105 : Nat := 252172916826406283128955

theorem tailTrace_491105 : CollatzResearch.WordTrace tailWord_491105 prefixEnd_491105 252172916826406283128955 := by
  unfold tailWord_491105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17912070885817933901554769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11941380590545289267703179 17912070885817933901554769)
  ·
    refine ⟨13434053164363450426166077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17912070885817933901554769 13434053164363450426166077)
    ·
      refine ⟨5037769936636293909812279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13434053164363450426166077 5037769936636293909812279)
      ·
        refine ⟨7556654904954440864718419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037769936636293909812279 7556654904954440864718419)
        ·
          refine ⟨11334982357431661297077629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556654904954440864718419 11334982357431661297077629)
          ·
            refine ⟨4250618384036872986404111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11334982357431661297077629 4250618384036872986404111)
            ·
              refine ⟨6375927576055309479606167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250618384036872986404111 6375927576055309479606167)
              ·
                refine ⟨9563891364082964219409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375927576055309479606167 9563891364082964219409251)
                ·
                  refine ⟨14345837046124446329113877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563891364082964219409251 14345837046124446329113877)
                  ·
                    refine ⟨672461111537083421677213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14345837046124446329113877 672461111537083421677213)
                    ·
                      refine ⟨252172916826406283128955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672461111537083421677213 252172916826406283128955)
                      ·
                        rfl

theorem cell23_491105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_491105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491105 prefixEnd_491105 := by exact prefixLift 491105
  have htrace : WordTrace (prefixWord ++ tailWord_491105) baseStart_491105 baseEnd_491105 := by
    simpa [prefixWord, tailWord_491105, baseEnd_491105] using wordTrace_append hprefix tailTrace_491105
  have hstable : (prefixWord ++ tailWord_491105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491105).length < 2 ^ (prefixWord ++ tailWord_491105).sum := by decide
  have hdescent : baseEnd_491105 < baseStart_491105 := by decide
  rcases family_descends (prefixWord ++ tailWord_491105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491112 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_491112 : Nat := 118140960795 + 491112 * 2 ^ 59
def prefixEnd_491112 : Nat := 4983230072969 + 3 ^ 40 * 491112 * 2
def baseEnd_491112 : Nat := 84058837063662585247141

theorem tailTrace_491112 : CollatzResearch.WordTrace tailWord_491112 prefixEnd_491112 84058837063662585247141 := by
  unfold tailWord_491112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956163098396287048529795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11941550797861716064706393 8956163098396287048529795)
  ·
    refine ⟨13434244647594430572794693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8956163098396287048529795 13434244647594430572794693)
    ·
      refine ⟨2518920871423955732399005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13434244647594430572794693 2518920871423955732399005)
      ·
        refine ⟨944595326783983399649627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2518920871423955732399005 944595326783983399649627)
        ·
          refine ⟨1416892990175975099474441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944595326783983399649627 1416892990175975099474441)
          ·
            refine ⟨1062669742631981324605831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416892990175975099474441 1062669742631981324605831)
            ·
              refine ⟨1594004613947971986908747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062669742631981324605831 1594004613947971986908747)
              ·
                refine ⟨2391006920921957980363121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594004613947971986908747 2391006920921957980363121)
                ·
                  refine ⟨1793255190691468485272341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391006920921957980363121 1793255190691468485272341)
                  ·
                    refine ⟨84058837063662585247141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1793255190691468485272341 84058837063662585247141)
                    ·
                      rfl

theorem cell23_491112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_491112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491112 prefixEnd_491112 := by exact prefixLift 491112
  have htrace : WordTrace (prefixWord ++ tailWord_491112) baseStart_491112 baseEnd_491112 := by
    simpa [prefixWord, tailWord_491112, baseEnd_491112] using wordTrace_append hprefix tailTrace_491112
  have hstable : (prefixWord ++ tailWord_491112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491112).length < 2 ^ (prefixWord ++ tailWord_491112).sum := by decide
  have hdescent : baseEnd_491112 < baseStart_491112 := by decide
  rcases family_descends (prefixWord ++ tailWord_491112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491140 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_491140 : Nat := 118140960795 + 491140 * 2 ^ 59
def prefixEnd_491140 : Nat := 4983230072969 + 3 ^ 40 * 491140 * 2
def baseEnd_491140 : Nat := 252190888649313646191295

theorem tailTrace_491140 : CollatzResearch.WordTrace tailWord_491140 prefixEnd_491140 252190888649313646191295 := by
  unfold tailWord_491140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956673720345567439539437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11942231627127423252719249 8956673720345567439539437)
  ·
    refine ⟨3358752645129587789827289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8956673720345567439539437 3358752645129587789827289)
    ·
      refine ⟨2519064483847190842370467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3358752645129587789827289 2519064483847190842370467)
      ·
        refine ⟨3778596725770786263555701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519064483847190842370467 3778596725770786263555701)
        ·
          refine ⟨354243443041011212208347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3778596725770786263555701 354243443041011212208347)
          ·
            refine ⟨531365164561516818312521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354243443041011212208347 531365164561516818312521)
            ·
              refine ⟨398523873421137613734391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531365164561516818312521 398523873421137613734391)
              ·
                refine ⟨597785810131706420601587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398523873421137613734391 597785810131706420601587)
                ·
                  refine ⟨896678715197559630902381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597785810131706420601587 896678715197559630902381)
                  ·
                    refine ⟨336254518199084861588393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896678715197559630902381 336254518199084861588393)
                    ·
                      refine ⟨252190888649313646191295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336254518199084861588393 252190888649313646191295)
                      ·
                        rfl

theorem cell23_491140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_491140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491140 prefixEnd_491140 := by exact prefixLift 491140
  have htrace : WordTrace (prefixWord ++ tailWord_491140) baseStart_491140 baseEnd_491140 := by
    simpa [prefixWord, tailWord_491140, baseEnd_491140] using wordTrace_append hprefix tailTrace_491140
  have hstable : (prefixWord ++ tailWord_491140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491140).length < 2 ^ (prefixWord ++ tailWord_491140).sum := by decide
  have hdescent : baseEnd_491140 < baseStart_491140 := by decide
  rcases family_descends (prefixWord ++ tailWord_491140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491165 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_491165 : Nat := 118140960795 + 491165 * 2 ^ 59
def prefixEnd_491165 : Nat := 4983230072969 + 3 ^ 40 * 491165 * 2
def baseEnd_491165 : Nat := 252203725665676048378679

theorem tailTrace_491165 : CollatzResearch.WordTrace tailWord_491165 prefixEnd_491165 252203725665676048378679 := by
  unfold tailWord_491165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17914259265600564148738949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11942839510400376099159299 17914259265600564148738949)
  ·
    refine ⟨3358923612300105777888553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17914259265600564148738949 3358923612300105777888553)
    ·
      refine ⟨2519192709225079333416415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3358923612300105777888553 2519192709225079333416415)
      ·
        refine ⟨3778789063837619000124623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519192709225079333416415 3778789063837619000124623)
        ·
          refine ⟨5668183595756428500186935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778789063837619000124623 5668183595756428500186935)
          ·
            refine ⟨8502275393634642750280403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668183595756428500186935 8502275393634642750280403)
            ·
              refine ⟨12753413090451964125420605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502275393634642750280403 12753413090451964125420605)
              ·
                refine ⟨4782529908919486547032727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12753413090451964125420605 4782529908919486547032727)
                ·
                  refine ⟨7173794863379229820549091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782529908919486547032727 7173794863379229820549091)
                  ·
                    refine ⟨10760692295068844730823637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173794863379229820549091 10760692295068844730823637)
                    ·
                      refine ⟨252203725665676048378679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10760692295068844730823637 252203725665676048378679)
                      ·
                        rfl

theorem cell23_491165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_491165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491165 prefixEnd_491165 := by exact prefixLift 491165
  have htrace : WordTrace (prefixWord ++ tailWord_491165) baseStart_491165 baseEnd_491165 := by
    simpa [prefixWord, tailWord_491165, baseEnd_491165] using wordTrace_append hprefix tailTrace_491165
  have hstable : (prefixWord ++ tailWord_491165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491165).length < 2 ^ (prefixWord ++ tailWord_491165).sum := by decide
  have hdescent : baseEnd_491165 < baseStart_491165 := by decide
  rcases family_descends (prefixWord ++ tailWord_491165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491170 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_491170 : Nat := 118140960795 + 491170 * 2 ^ 59
def prefixEnd_491170 : Nat := 4983230072969 + 3 ^ 40 * 491170 * 2
def baseEnd_491170 : Nat := 252206293068948528816157

theorem tailTrace_491170 : CollatzResearch.WordTrace tailWord_491170 prefixEnd_491170 252206293068948528816157 := by
  unfold tailWord_491170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478610407645612500667741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11942961087054966668447309 4478610407645612500667741)
  ·
    refine ⟨1679478902867104687750403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4478610407645612500667741 1679478902867104687750403)
    ·
      refine ⟨2519218354300657031625605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1679478902867104687750403 2519218354300657031625605)
      ·
        refine ⟨472353441431373193429801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2519218354300657031625605 472353441431373193429801)
        ·
          refine ⟨354265081073529895072351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472353441431373193429801 354265081073529895072351)
          ·
            refine ⟨531397621610294842608527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354265081073529895072351 531397621610294842608527)
            ·
              refine ⟨797096432415442263912791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531397621610294842608527 797096432415442263912791)
              ·
                refine ⟨1195644648623163395869187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797096432415442263912791 1195644648623163395869187)
                ·
                  refine ⟨1793466972934745093803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195644648623163395869187 1793466972934745093803781)
                  ·
                    refine ⟨336275057425264705088209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793466972934745093803781 336275057425264705088209)
                    ·
                      refine ⟨252206293068948528816157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336275057425264705088209 252206293068948528816157)
                      ·
                        rfl

theorem cell23_491170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_491170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491170 prefixEnd_491170 := by exact prefixLift 491170
  have htrace : WordTrace (prefixWord ++ tailWord_491170) baseStart_491170 baseEnd_491170 := by
    simpa [prefixWord, tailWord_491170, baseEnd_491170] using wordTrace_append hprefix tailTrace_491170
  have hstable : (prefixWord ++ tailWord_491170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491170).length < 2 ^ (prefixWord ++ tailWord_491170).sum := by decide
  have hdescent : baseEnd_491170 < baseStart_491170 := by decide
  rcases family_descends (prefixWord ++ tailWord_491170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491192 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_491192 : Nat := 118140960795 + 491192 * 2 ^ 59
def prefixEnd_491192 : Nat := 4983230072969 + 3 ^ 40 * 491192 * 2
def baseEnd_491192 : Nat := 252217589643347442741055

theorem tailTrace_491192 : CollatzResearch.WordTrace tailWord_491192 prefixEnd_491192 252217589643347442741055 := by
  unfold tailWord_491192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957622018251373879985915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11943496024335165173314553 8957622018251373879985915)
  ·
    refine ⟨13436433027377060819978873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957622018251373879985915 13436433027377060819978873)
    ·
      refine ⟨10077324770532795614984155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13436433027377060819978873 10077324770532795614984155)
      ·
        refine ⟨15115987155799193422476233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077324770532795614984155 15115987155799193422476233)
        ·
          refine ⟨11336990366849395066857175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15115987155799193422476233 11336990366849395066857175)
          ·
            refine ⟨17005485550274092600285763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336990366849395066857175 17005485550274092600285763)
            ·
              refine ⟨25508228325411138900428645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005485550274092600285763 25508228325411138900428645)
              ·
                refine ⟨4782792811014588543830371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25508228325411138900428645 4782792811014588543830371)
                ·
                  refine ⟨7174189216521882815745557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782792811014588543830371 7174189216521882815745557)
                  ·
                    refine ⟨336290119524463256988073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7174189216521882815745557 336290119524463256988073)
                    ·
                      refine ⟨252217589643347442741055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336290119524463256988073 252217589643347442741055)
                      ·
                        rfl

theorem cell23_491192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_491192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491192 prefixEnd_491192 := by exact prefixLift 491192
  have htrace : WordTrace (prefixWord ++ tailWord_491192) baseStart_491192 baseEnd_491192 := by
    simpa [prefixWord, tailWord_491192, baseEnd_491192] using wordTrace_append hprefix tailTrace_491192
  have hstable : (prefixWord ++ tailWord_491192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491192).length < 2 ^ (prefixWord ++ tailWord_491192).sum := by decide
  have hdescent : baseEnd_491192 < baseStart_491192 := by decide
  rcases family_descends (prefixWord ++ tailWord_491192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491205 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_491205 : Nat := 118140960795 + 491205 * 2 ^ 59
def prefixEnd_491205 : Nat := 4983230072969 + 3 ^ 40 * 491205 * 2
def baseEnd_491205 : Nat := 252224264891855891878495

theorem tailTrace_491205 : CollatzResearch.WordTrace tailWord_491205 prefixEnd_491205 252224264891855891878495 := by
  unfold tailWord_491205
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915718185455650980195069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11943812123637100653463379 17915718185455650980195069)
  ·
    refine ⟨6718394319545869117573151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17915718185455650980195069 6718394319545869117573151)
    ·
      refine ⟨10077591479318803676359727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718394319545869117573151 10077591479318803676359727)
      ·
        refine ⟨15116387218978205514539591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077591479318803676359727 15116387218978205514539591)
        ·
          refine ⟨22674580828467308271809387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116387218978205514539591 22674580828467308271809387)
          ·
            refine ⟨34011871242700962407714081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22674580828467308271809387 34011871242700962407714081)
            ·
              refine ⟨25508903432025721805785561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34011871242700962407714081 25508903432025721805785561)
              ·
                refine ⟨19131677574019291354339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25508903432025721805785561 19131677574019291354339171)
                ·
                  refine ⟨28697516361028937031508757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19131677574019291354339171 28697516361028937031508757)
                  ·
                    refine ⟨1345196079423231423351973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28697516361028937031508757 1345196079423231423351973)
                    ·
                      refine ⟨252224264891855891878495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1345196079423231423351973 252224264891855891878495)
                      ·
                        rfl

theorem cell23_491205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_491205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491205 prefixEnd_491205 := by exact prefixLift 491205
  have htrace : WordTrace (prefixWord ++ tailWord_491205) baseStart_491205 baseEnd_491205 := by
    simpa [prefixWord, tailWord_491205, baseEnd_491205] using wordTrace_append hprefix tailTrace_491205
  have hstable : (prefixWord ++ tailWord_491205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491205).length < 2 ^ (prefixWord ++ tailWord_491205).sum := by decide
  have hdescent : baseEnd_491205 < baseStart_491205 := by decide
  rcases family_descends (prefixWord ++ tailWord_491205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491206 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_491206 : Nat := 118140960795 + 491206 * 2 ^ 59
def prefixEnd_491206 : Nat := 4983230072969 + 3 ^ 40 * 491206 * 2
def baseEnd_491206 : Nat := 84074926124170129321997

theorem tailTrace_491206 : CollatzResearch.WordTrace tailWord_491206 prefixEnd_491206 84074926124170129321997 := by
  unfold tailWord_491206
  simp only [CollatzResearch.WordTrace]
  refine ⟨559867333076625879718171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11943836438968018767320981 559867333076625879718171)
  ·
    refine ⟨839800999614938819577257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559867333076625879718171 839800999614938819577257)
    ·
      refine ⟨629850749711204114682943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839800999614938819577257 629850749711204114682943)
      ·
        refine ⟨944776124566806172024415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629850749711204114682943 944776124566806172024415)
        ·
          refine ⟨1417164186850209258036623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944776124566806172024415 1417164186850209258036623)
          ·
            refine ⟨2125746280275313887054935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417164186850209258036623 2125746280275313887054935)
            ·
              refine ⟨3188619420412970830582403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125746280275313887054935 3188619420412970830582403)
              ·
                refine ⟨4782929130619456245873605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188619420412970830582403 4782929130619456245873605)
                ·
                  refine ⟨896799211991148046101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4782929130619456245873605 896799211991148046101301)
                  ·
                    refine ⟨84074926124170129321997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 896799211991148046101301 84074926124170129321997)
                    ·
                      rfl

theorem cell23_491206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_491206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491206 prefixEnd_491206 := by exact prefixLift 491206
  have htrace : WordTrace (prefixWord ++ tailWord_491206) baseStart_491206 baseEnd_491206 := by
    simpa [prefixWord, tailWord_491206, baseEnd_491206] using wordTrace_append hprefix tailTrace_491206
  have hstable : (prefixWord ++ tailWord_491206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491206).length < 2 ^ (prefixWord ++ tailWord_491206).sum := by decide
  have hdescent : baseEnd_491206 < baseStart_491206 := by decide
  rcases family_descends (prefixWord ++ tailWord_491206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491242 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_491242 : Nat := 118140960795 + 491242 * 2 ^ 59
def prefixEnd_491242 : Nat := 4983230072969 + 3 ^ 40 * 491242 * 2
def baseEnd_491242 : Nat := 252243263676072247115825

theorem tailTrace_491242 : CollatzResearch.WordTrace tailWord_491242 prefixEnd_491242 252243263676072247115825 := by
  unfold tailWord_491242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479266921580401574822995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11944711790881070866194653 4479266921580401574822995)
  ·
    refine ⟨6718900382370602362234493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479266921580401574822995 6718900382370602362234493)
    ·
      refine ⟨2519587643388975885837935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6718900382370602362234493 2519587643388975885837935)
      ·
        refine ⟨3779381465083463828756903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519587643388975885837935 3779381465083463828756903)
        ·
          refine ⟨5669072197625195743135355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779381465083463828756903 5669072197625195743135355)
          ·
            refine ⟨8503608296437793614703033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669072197625195743135355 8503608296437793614703033)
            ·
              refine ⟨6377706222328345211027275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8503608296437793614703033 6377706222328345211027275)
              ·
                refine ⟨9566559333492517816540913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377706222328345211027275 9566559333492517816540913)
                ·
                  refine ⟨7174919500119388362405685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9566559333492517816540913 7174919500119388362405685)
                  ·
                    refine ⟨672648703136192658975533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7174919500119388362405685 672648703136192658975533)
                    ·
                      refine ⟨252243263676072247115825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672648703136192658975533 252243263676072247115825)
                      ·
                        rfl

theorem cell23_491242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_491242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491242 prefixEnd_491242 := by exact prefixLift 491242
  have htrace : WordTrace (prefixWord ++ tailWord_491242) baseStart_491242 baseEnd_491242 := by
    simpa [prefixWord, tailWord_491242, baseEnd_491242] using wordTrace_append hprefix tailTrace_491242
  have hstable : (prefixWord ++ tailWord_491242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491242).length < 2 ^ (prefixWord ++ tailWord_491242).sum := by decide
  have hdescent : baseEnd_491242 < baseStart_491242 := by decide
  rcases family_descends (prefixWord ++ tailWord_491242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491277 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_491277 : Nat := 118140960795 + 491277 * 2 ^ 59
def prefixEnd_491277 : Nat := 4983230072969 + 3 ^ 40 * 491277 * 2
def baseEnd_491277 : Nat := 252261235498979610178165

theorem tailTrace_491277 : CollatzResearch.WordTrace tailWord_491277 prefixEnd_491277 252261235498979610178165 := by
  unfold tailWord_491277
  simp only [CollatzResearch.WordTrace]
  refine ⟨17918344241194807276816085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11945562827463204851210723 17918344241194807276816085)
  ·
    refine ⟨419961193153003295550377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17918344241194807276816085 419961193153003295550377)
    ·
      refine ⟨314970894864752471662783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419961193153003295550377 314970894864752471662783)
      ·
        refine ⟨472456342297128707494175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314970894864752471662783 472456342297128707494175)
        ·
          refine ⟨708684513445693061241263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472456342297128707494175 708684513445693061241263)
          ·
            refine ⟨1063026770168539591861895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708684513445693061241263 1063026770168539591861895)
            ·
              refine ⟨1594540155252809387792843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063026770168539591861895 1594540155252809387792843)
              ·
                refine ⟨2391810232879214081689265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594540155252809387792843 2391810232879214081689265)
                ·
                  refine ⟨1793857674659410561266949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391810232879214081689265 1793857674659410561266949)
                  ·
                    refine ⟨336348313998639480237553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793857674659410561266949 336348313998639480237553)
                    ·
                      refine ⟨252261235498979610178165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336348313998639480237553 252261235498979610178165)
                      ·
                        rfl

theorem cell23_491277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_491277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491277 prefixEnd_491277 := by exact prefixLift 491277
  have htrace : WordTrace (prefixWord ++ tailWord_491277) baseStart_491277 baseEnd_491277 := by
    simpa [prefixWord, tailWord_491277, baseEnd_491277] using wordTrace_append hprefix tailTrace_491277
  have hstable : (prefixWord ++ tailWord_491277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491277).length < 2 ^ (prefixWord ++ tailWord_491277).sum := by decide
  have hdescent : baseEnd_491277 < baseStart_491277 := by decide
  rcases family_descends (prefixWord ++ tailWord_491277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491322 : List Nat := [3, 1, 1, 1, 5, 2, 10]
def baseStart_491322 : Nat := 118140960795 + 491322 * 2 ^ 59
def prefixEnd_491322 : Nat := 4983230072969 + 3 ^ 40 * 491322 * 2
def baseEnd_491322 : Nat := 3114621507758418939697

theorem tailTrace_491322 : CollatzResearch.WordTrace tailWord_491322 prefixEnd_491322 3114621507758418939697 := by
  unfold tailWord_491322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479996381507944990551055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11946657017354519974802813 4479996381507944990551055)
  ·
    refine ⟨6719994572261917485826583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479996381507944990551055 6719994572261917485826583)
    ·
      refine ⟨10079991858392876228739875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719994572261917485826583 10079991858392876228739875)
      ·
        refine ⟨15119987787589314343109813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079991858392876228739875 15119987787589314343109813)
        ·
          refine ⟨1417498855086498219666545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15119987787589314343109813 1417498855086498219666545)
          ·
            refine ⟨1063124141314873664749909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417498855086498219666545 1063124141314873664749909)
            ·
              refine ⟨3114621507758418939697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1063124141314873664749909 3114621507758418939697)
              ·
                rfl

theorem cell23_491322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 10].length) (baseStart_491322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491322 prefixEnd_491322 := by exact prefixLift 491322
  have htrace : WordTrace (prefixWord ++ tailWord_491322) baseStart_491322 baseEnd_491322 := by
    simpa [prefixWord, tailWord_491322, baseEnd_491322] using wordTrace_append hprefix tailTrace_491322
  have hstable : (prefixWord ++ tailWord_491322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491322).length < 2 ^ (prefixWord ++ tailWord_491322).sum := by decide
  have hdescent : baseEnd_491322 < baseStart_491322 := by decide
  rcases family_descends (prefixWord ++ tailWord_491322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491326 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_491326 : Nat := 118140960795 + 491326 * 2 ^ 59
def prefixEnd_491326 : Nat := 4983230072969 + 3 ^ 40 * 491326 * 2
def baseEnd_491326 : Nat := 84095465350349972821813

theorem tailTrace_491326 : CollatzResearch.WordTrace tailWord_491326 prefixEnd_491326 84095465350349972821813 := by
  unfold tailWord_491326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240016427252161080668729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11946754278678192430233221 2240016427252161080668729)
  ·
    refine ⟨1680012320439120810501547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2240016427252161080668729 1680012320439120810501547)
    ·
      refine ⟨2520018480658681215752321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680012320439120810501547 2520018480658681215752321)
      ·
        refine ⟨1890013860494010911814241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520018480658681215752321 1890013860494010911814241)
        ·
          refine ⟨1417510395370508183860681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890013860494010911814241 1417510395370508183860681)
          ·
            refine ⟨1063132796527881137895511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417510395370508183860681 1063132796527881137895511)
            ·
              refine ⟨1594699194791821706843267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063132796527881137895511 1594699194791821706843267)
              ·
                refine ⟨2392048792187732560264901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594699194791821706843267 2392048792187732560264901)
                ·
                  refine ⟨448509148535199855049669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392048792187732560264901 448509148535199855049669)
                  ·
                    refine ⟨84095465350349972821813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448509148535199855049669 84095465350349972821813)
                    ·
                      rfl

theorem cell23_491326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_491326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491326 prefixEnd_491326 := by exact prefixLift 491326
  have htrace : WordTrace (prefixWord ++ tailWord_491326) baseStart_491326 baseEnd_491326 := by
    simpa [prefixWord, tailWord_491326, baseEnd_491326] using wordTrace_append hprefix tailTrace_491326
  have hstable : (prefixWord ++ tailWord_491326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491326).length < 2 ^ (prefixWord ++ tailWord_491326).sum := by decide
  have hdescent : baseEnd_491326 < baseStart_491326 := by decide
  rcases family_descends (prefixWord ++ tailWord_491326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491333 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_491333 : Nat := 118140960795 + 491333 * 2 ^ 59
def prefixEnd_491333 : Nat := 4983230072969 + 3 ^ 40 * 491333 * 2
def baseEnd_491333 : Nat := 252289990415631391077907

theorem tailTrace_491333 : CollatzResearch.WordTrace tailWord_491333 prefixEnd_491333 252289990415631391077907 := by
  unfold tailWord_491333
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920386728991928840854653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946924485994619227236435 17920386728991928840854653)
  ·
    refine ⟨6720145023371973315320495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17920386728991928840854653 6720145023371973315320495)
    ·
      refine ⟨10080217535057959972980743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720145023371973315320495 10080217535057959972980743)
      ·
        refine ⟨15120326302586939959471115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080217535057959972980743 15120326302586939959471115)
        ·
          refine ⟨22680489453880409939206673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15120326302586939959471115 22680489453880409939206673)
          ·
            refine ⟨17010367090410307454405005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22680489453880409939206673 17010367090410307454405005)
            ·
              refine ⟨6378887658903865295401877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17010367090410307454405005 6378887658903865295401877)
              ·
                refine ⟨299010359011118685721963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6378887658903865295401877 299010359011118685721963)
                ·
                  refine ⟨448515538516678028582945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299010359011118685721963 448515538516678028582945)
                  ·
                    refine ⟨336386653887508521437209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448515538516678028582945 336386653887508521437209)
                    ·
                      refine ⟨252289990415631391077907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336386653887508521437209 252289990415631391077907)
                      ·
                        rfl

theorem cell23_491333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_491333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491333 prefixEnd_491333 := by exact prefixLift 491333
  have htrace : WordTrace (prefixWord ++ tailWord_491333) baseStart_491333 baseEnd_491333 := by
    simpa [prefixWord, tailWord_491333, baseEnd_491333] using wordTrace_append hprefix tailTrace_491333
  have hstable : (prefixWord ++ tailWord_491333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491333).length < 2 ^ (prefixWord ++ tailWord_491333).sum := by decide
  have hdescent : baseEnd_491333 < baseStart_491333 := by decide
  rcases family_descends (prefixWord ++ tailWord_491333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491346 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_491346 : Nat := 118140960795 + 491346 * 2 ^ 59
def prefixEnd_491346 : Nat := 4983230072969 + 3 ^ 40 * 491346 * 2
def baseEnd_491346 : Nat := 252296665664139840215347

theorem tailTrace_491346 : CollatzResearch.WordTrace tailWord_491346 prefixEnd_491346 252296665664139840215347 := by
  unfold tailWord_491346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480215219486208015269473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11947240585296554707385261 4480215219486208015269473)
  ·
    refine ⟨3360161414614656011452105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4480215219486208015269473 3360161414614656011452105)
    ·
      refine ⟨2520121060960992008589079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3360161414614656011452105 2520121060960992008589079)
      ·
        refine ⟨3780181591441488012883619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520121060960992008589079 3780181591441488012883619)
        ·
          refine ⟨5670272387162232019325429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780181591441488012883619 5670272387162232019325429)
          ·
            refine ⟨531588036296459251811759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5670272387162232019325429 531588036296459251811759)
            ·
              refine ⟨797382054444688877717639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531588036296459251811759 797382054444688877717639)
              ·
                refine ⟨1196073081667033316576459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797382054444688877717639 1196073081667033316576459)
                ·
                  refine ⟨1794109622500549974864689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196073081667033316576459 1794109622500549974864689)
                  ·
                    refine ⟨1345582216875412481148517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794109622500549974864689 1345582216875412481148517)
                    ·
                      refine ⟨252296665664139840215347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1345582216875412481148517 252296665664139840215347)
                      ·
                        rfl

theorem cell23_491346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_491346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491346 prefixEnd_491346 := by exact prefixLift 491346
  have htrace : WordTrace (prefixWord ++ tailWord_491346) baseStart_491346 baseEnd_491346 := by
    simpa [prefixWord, tailWord_491346, baseEnd_491346] using wordTrace_append hprefix tailTrace_491346
  have hstable : (prefixWord ++ tailWord_491346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491346).length < 2 ^ (prefixWord ++ tailWord_491346).sum := by decide
  have hdescent : baseEnd_491346 < baseStart_491346 := by decide
  rcases family_descends (prefixWord ++ tailWord_491346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491392 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_491392 : Nat := 118140960795 + 491392 * 2 ^ 59
def prefixEnd_491392 : Nat := 4983230072969 + 3 ^ 40 * 491392 * 2
def baseEnd_491392 : Nat := 252320285774246660240135

theorem tailTrace_491392 : CollatzResearch.WordTrace tailWord_491392 prefixEnd_491392 252320285774246660240135 := by
  unfold tailWord_491392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961269317889090958626215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11948359090518787944834953 8961269317889090958626215)
  ·
    refine ⟨13441903976833636437939323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8961269317889090958626215 13441903976833636437939323)
    ·
      refine ⟨20162855965250454656908985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13441903976833636437939323 20162855965250454656908985)
      ·
        refine ⟨15122141973937840992681739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20162855965250454656908985 15122141973937840992681739)
        ·
          refine ⟨22683212960906761489022609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122141973937840992681739 22683212960906761489022609)
          ·
            refine ⟨17012409720680071116766957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22683212960906761489022609 17012409720680071116766957)
            ·
              refine ⟨6379653645255026668787609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17012409720680071116766957 6379653645255026668787609)
              ·
                refine ⟨4784740233941270001590707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379653645255026668787609 4784740233941270001590707)
                ·
                  refine ⟨7177110350911905002386061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784740233941270001590707 7177110350911905002386061)
                  ·
                    refine ⟨2691416381591964375894773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7177110350911905002386061 2691416381591964375894773)
                    ·
                      refine ⟨252320285774246660240135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2691416381591964375894773 252320285774246660240135)
                      ·
                        rfl

theorem cell23_491392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_491392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491392 prefixEnd_491392 := by exact prefixLift 491392
  have htrace : WordTrace (prefixWord ++ tailWord_491392) baseStart_491392 baseEnd_491392 := by
    simpa [prefixWord, tailWord_491392, baseEnd_491392] using wordTrace_append hprefix tailTrace_491392
  have hstable : (prefixWord ++ tailWord_491392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491392).length < 2 ^ (prefixWord ++ tailWord_491392).sum := by decide
  have hdescent : baseEnd_491392 < baseStart_491392 := by decide
  rcases family_descends (prefixWord ++ tailWord_491392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491410 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_491410 : Nat := 118140960795 + 491410 * 2 ^ 59
def prefixEnd_491410 : Nat := 4983230072969 + 3 ^ 40 * 491410 * 2
def baseEnd_491410 : Nat := 252329528426027589815053

theorem tailTrace_491410 : CollatzResearch.WordTrace tailWord_491410 prefixEnd_491410 252329528426027589815053 := by
  unfold tailWord_491410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480798787428242747851921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11948796766475313994271789 4480798787428242747851921)
  ·
    refine ⟨3360599090571182060888941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4480798787428242747851921 3360599090571182060888941)
    ·
      refine ⟨1260224658964193272833353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3360599090571182060888941 1260224658964193272833353)
      ·
        refine ⟨945168494223144954625015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1260224658964193272833353 945168494223144954625015)
        ·
          refine ⟨1417752741334717431937523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945168494223144954625015 1417752741334717431937523)
          ·
            refine ⟨2126629112002076147906285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417752741334717431937523 2126629112002076147906285)
            ·
              refine ⟨797485917000778555464857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126629112002076147906285 797485917000778555464857)
              ·
                refine ⟨598114437750583916598643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797485917000778555464857 598114437750583916598643)
                ·
                  refine ⟨897171656625875874897965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598114437750583916598643 897171656625875874897965)
                  ·
                    refine ⟨336439371234703453086737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 897171656625875874897965 336439371234703453086737)
                    ·
                      refine ⟨252329528426027589815053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336439371234703453086737 252329528426027589815053)
                      ·
                        rfl

theorem cell23_491410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_491410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491410 prefixEnd_491410 := by exact prefixLift 491410
  have htrace : WordTrace (prefixWord ++ tailWord_491410) baseStart_491410 baseEnd_491410 := by
    simpa [prefixWord, tailWord_491410, baseEnd_491410] using wordTrace_append hprefix tailTrace_491410
  have hstable : (prefixWord ++ tailWord_491410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491410).length < 2 ^ (prefixWord ++ tailWord_491410).sum := by decide
  have hdescent : baseEnd_491410 < baseStart_491410 := by decide
  rcases family_descends (prefixWord ++ tailWord_491410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491423 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 4, 2]
def baseStart_491423 : Nat := 118140960795 + 491423 * 2 ^ 59
def prefixEnd_491423 : Nat := 4983230072969 + 3 ^ 40 * 491423 * 2
def baseEnd_491423 : Nat := 252336203674536038952493

theorem tailTrace_491423 : CollatzResearch.WordTrace tailWord_491423 prefixEnd_491423 252336203674536038952493 := by
  unfold tailWord_491423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923669298665874211630923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11949112865777249474420615 17923669298665874211630923)
  ·
    refine ⟨26885503947998811317446385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17923669298665874211630923 26885503947998811317446385)
    ·
      refine ⟨20164127960999108488084789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26885503947998811317446385 20164127960999108488084789)
      ·
        refine ⟨1890386996343666420757949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20164127960999108488084789 1890386996343666420757949)
        ·
          refine ⟨708895123628874907784231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1890386996343666420757949 708895123628874907784231)
          ·
            refine ⟨1063342685443312361676347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708895123628874907784231 1063342685443312361676347)
            ·
              refine ⟨1595014028164968542514521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063342685443312361676347 1595014028164968542514521)
              ·
                refine ⟨1196260521123726406885891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595014028164968542514521 1196260521123726406885891)
                ·
                  refine ⟨1794390781685589610328837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196260521123726406885891 1794390781685589610328837)
                  ·
                    refine ⟨336448271566048051936657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794390781685589610328837 336448271566048051936657)
                    ·
                      refine ⟨252336203674536038952493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336448271566048051936657 252336203674536038952493)
                      ·
                        rfl

theorem cell23_491423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_491423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491423 prefixEnd_491423 := by exact prefixLift 491423
  have htrace : WordTrace (prefixWord ++ tailWord_491423) baseStart_491423 baseEnd_491423 := by
    simpa [prefixWord, tailWord_491423, baseEnd_491423] using wordTrace_append hprefix tailTrace_491423
  have hstable : (prefixWord ++ tailWord_491423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491423).length < 2 ^ (prefixWord ++ tailWord_491423).sum := by decide
  have hdescent : baseEnd_491423 < baseStart_491423 := by decide
  rcases family_descends (prefixWord ++ tailWord_491423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491439 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_491439 : Nat := 118140960795 + 491439 * 2 ^ 59
def prefixEnd_491439 : Nat := 4983230072969 + 3 ^ 40 * 491439 * 2
def baseEnd_491439 : Nat := 252344419365007976352419

theorem tailTrace_491439 : CollatzResearch.WordTrace tailWord_491439 prefixEnd_491439 252344419365007976352419 := by
  unfold tailWord_491439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924252866607908944213371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11949501911071939296142247 17924252866607908944213371)
  ·
    refine ⟨26886379299911863416320057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17924252866607908944213371 26886379299911863416320057)
    ·
      refine ⟨20164784474933897562240043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26886379299911863416320057 20164784474933897562240043)
      ·
        refine ⟨30247176712400846343360065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20164784474933897562240043 30247176712400846343360065)
        ·
          refine ⟨22685382534300634757520049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30247176712400846343360065 22685382534300634757520049)
          ·
            refine ⟨17014036900725476068140037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22685382534300634757520049 17014036900725476068140037)
            ·
              refine ⟨3190131918886026762776257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17014036900725476068140037 3190131918886026762776257)
              ·
                refine ⟨2392598939164520072082193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190131918886026762776257 2392598939164520072082193)
                ·
                  refine ⟨1794449204373390054061645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392598939164520072082193 1794449204373390054061645)
                  ·
                    refine ⟨672918451640021270273117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794449204373390054061645 672918451640021270273117)
                    ·
                      refine ⟨252344419365007976352419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 672918451640021270273117 252344419365007976352419)
                      ·
                        rfl

theorem cell23_491439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_491439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491439 prefixEnd_491439 := by exact prefixLift 491439
  have htrace : WordTrace (prefixWord ++ tailWord_491439) baseStart_491439 baseEnd_491439 := by
    simpa [prefixWord, tailWord_491439, baseEnd_491439] using wordTrace_append hprefix tailTrace_491439
  have hstable : (prefixWord ++ tailWord_491439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491439).length < 2 ^ (prefixWord ++ tailWord_491439).sum := by decide
  have hdescent : baseEnd_491439 < baseStart_491439 := by decide
  rcases family_descends (prefixWord ++ tailWord_491439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491479 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_491479 : Nat := 118140960795 + 491479 * 2 ^ 59
def prefixEnd_491479 : Nat := 4983230072969 + 3 ^ 40 * 491479 * 2
def baseEnd_491479 : Nat := 252364958591187819852235

theorem tailTrace_491479 : CollatzResearch.WordTrace tailWord_491479 prefixEnd_491479 252364958591187819852235 := by
  unfold tailWord_491479
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925711786462995775669491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11950474524308663850446327 17925711786462995775669491)
  ·
    refine ⟨26888567679694493663504237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17925711786462995775669491 26888567679694493663504237)
    ·
      refine ⟨10083212879885435123814089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26888567679694493663504237 10083212879885435123814089)
      ·
        refine ⟨7562409659914076342860567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10083212879885435123814089 7562409659914076342860567)
        ·
          refine ⟨11343614489871114514290851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7562409659914076342860567 11343614489871114514290851)
          ·
            refine ⟨17015421734806671771436277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343614489871114514290851 17015421734806671771436277)
            ·
              refine ⟨1595195787638125478572151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17015421734806671771436277 1595195787638125478572151)
              ·
                refine ⟨2392793681457188217858227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595195787638125478572151 2392793681457188217858227)
                ·
                  refine ⟨3589190522185782326787341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392793681457188217858227 3589190522185782326787341)
                  ·
                    refine ⟨1345946445819668372545253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3589190522185782326787341 1345946445819668372545253)
                    ·
                      refine ⟨252364958591187819852235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1345946445819668372545253 252364958591187819852235)
                      ·
                        rfl

theorem cell23_491479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_491479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491479 prefixEnd_491479 := by exact prefixLift 491479
  have htrace : WordTrace (prefixWord ++ tailWord_491479) baseStart_491479 baseEnd_491479 := by
    simpa [prefixWord, tailWord_491479, baseEnd_491479] using wordTrace_append hprefix tailTrace_491479
  have hstable : (prefixWord ++ tailWord_491479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491479).length < 2 ^ (prefixWord ++ tailWord_491479).sum := by decide
  have hdescent : baseEnd_491479 < baseStart_491479 := by decide
  rcases family_descends (prefixWord ++ tailWord_491479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491519 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 6]
def baseStart_491519 : Nat := 118140960795 + 491519 * 2 ^ 59
def prefixEnd_491519 : Nat := 4983230072969 + 3 ^ 40 * 491519 * 2
def baseEnd_491519 : Nat := 28042833090818629261339

theorem tailTrace_491519 : CollatzResearch.WordTrace tailWord_491519 prefixEnd_491519 28042833090818629261339 := by
  unfold tailWord_491519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927170706318082607125611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11951447137545388404750407 17927170706318082607125611)
  ·
    refine ⟨26890756059477123910688417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17927170706318082607125611 26890756059477123910688417)
    ·
      refine ⟨20168067044607842933016313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26890756059477123910688417 20168067044607842933016313)
      ·
        refine ⟨15126050283455882199762235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20168067044607842933016313 15126050283455882199762235)
        ·
          refine ⟨22689075425183823299643353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15126050283455882199762235 22689075425183823299643353)
          ·
            refine ⟨17016806568887867474732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22689075425183823299643353 17016806568887867474732515)
            ·
              refine ⟨25525209853331801212098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17016806568887867474732515 25525209853331801212098773)
              ·
                refine ⟨598247105937464090908565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25525209853331801212098773 598247105937464090908565)
                ·
                  refine ⟨28042833090818629261339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 598247105937464090908565 28042833090818629261339)
                  ·
                    rfl

theorem cell23_491519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 6].length) (baseStart_491519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491519 prefixEnd_491519 := by exact prefixLift 491519
  have htrace : WordTrace (prefixWord ++ tailWord_491519) baseStart_491519 baseEnd_491519 := by
    simpa [prefixWord, tailWord_491519, baseEnd_491519] using wordTrace_append hprefix tailTrace_491519
  have hstable : (prefixWord ++ tailWord_491519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491519).length < 2 ^ (prefixWord ++ tailWord_491519).sum := by decide
  have hdescent : baseEnd_491519 < baseStart_491519 := by decide
  rcases family_descends (prefixWord ++ tailWord_491519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491596 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_491596 : Nat := 118140960795 + 491596 * 2 ^ 59
def prefixEnd_491596 : Nat := 4983230072969 + 3 ^ 40 * 491596 * 2
def baseEnd_491596 : Nat := 84141678609254620696399

theorem tailTrace_491596 : CollatzResearch.WordTrace tailWord_491596 prefixEnd_491596 84141678609254620696399 := by
  unfold tailWord_491596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8964989563519562378839321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11953319418026083171785761 8964989563519562378839321)
  ·
    refine ⟨6723742172639671784129491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8964989563519562378839321 6723742172639671784129491)
    ·
      refine ⟨10085613258959507676194237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723742172639671784129491 10085613258959507676194237)
      ·
        refine ⟨3782104972109815378572839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10085613258959507676194237 3782104972109815378572839)
        ·
          refine ⟨5673157458164723067859259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782104972109815378572839 5673157458164723067859259)
          ·
            refine ⟨8509736187247084601788889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673157458164723067859259 8509736187247084601788889)
            ·
              refine ⟨6382302140435313451341667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509736187247084601788889 6382302140435313451341667)
              ·
                refine ⟨9573453210652970177012501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382302140435313451341667 9573453210652970177012501)
                ·
                  refine ⟨448755619249357977047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9573453210652970177012501 448755619249357977047461)
                  ·
                    refine ⟨84141678609254620696399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448755619249357977047461 84141678609254620696399)
                    ·
                      rfl

theorem cell23_491596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_491596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491596 prefixEnd_491596 := by exact prefixLift 491596
  have htrace : WordTrace (prefixWord ++ tailWord_491596) baseStart_491596 baseEnd_491596 := by
    simpa [prefixWord, tailWord_491596, baseEnd_491596] using wordTrace_append hprefix tailTrace_491596
  have hstable : (prefixWord ++ tailWord_491596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491596).length < 2 ^ (prefixWord ++ tailWord_491596).sum := by decide
  have hdescent : baseEnd_491596 < baseStart_491596 := by decide
  rcases family_descends (prefixWord ++ tailWord_491596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491597 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_491597 : Nat := 118140960795 + 491597 * 2 ^ 59
def prefixEnd_491597 : Nat := 4983230072969 + 3 ^ 40 * 491597 * 2
def baseEnd_491597 : Nat := 252425549308418358176693

theorem tailTrace_491597 : CollatzResearch.WordTrace tailWord_491597 prefixEnd_491597 252425549308418358176693 := by
  unfold tailWord_491597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930015600035501928465045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11953343733357001285643363 17930015600035501928465045)
  ·
    refine ⟨840469481251664152896799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17930015600035501928465045 840469481251664152896799)
    ·
      refine ⟨1260704221877496229345199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840469481251664152896799 1260704221877496229345199)
      ·
        refine ⟨1891056332816244344017799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260704221877496229345199 1891056332816244344017799)
        ·
          refine ⟨2836584499224366516026699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891056332816244344017799 2836584499224366516026699)
          ·
            refine ⟨4254876748836549774040049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836584499224366516026699 4254876748836549774040049)
            ·
              refine ⟨3191157561627412330530037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254876748836549774040049 3191157561627412330530037)
              ·
                refine ⟨299171021402569905987191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3191157561627412330530037 299171021402569905987191)
                ·
                  refine ⟨448756532103854858980787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299171021402569905987191 448756532103854858980787)
                  ·
                    refine ⟨673134798155782288471181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448756532103854858980787 673134798155782288471181)
                    ·
                      refine ⟨252425549308418358176693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673134798155782288471181 252425549308418358176693)
                      ·
                        rfl

theorem cell23_491597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_491597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491597 prefixEnd_491597 := by exact prefixLift 491597
  have htrace : WordTrace (prefixWord ++ tailWord_491597) baseStart_491597 baseEnd_491597 := by
    simpa [prefixWord, tailWord_491597, baseEnd_491597] using wordTrace_append hprefix tailTrace_491597
  have hstable : (prefixWord ++ tailWord_491597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491597).length < 2 ^ (prefixWord ++ tailWord_491597).sum := by decide
  have hdescent : baseEnd_491597 < baseStart_491597 := by decide
  rcases family_descends (prefixWord ++ tailWord_491597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491653 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_491653 : Nat := 118140960795 + 491653 * 2 ^ 59
def prefixEnd_491653 : Nat := 4983230072969 + 3 ^ 40 * 491653 * 2
def baseEnd_491653 : Nat := 252454304225070139076435

theorem tailTrace_491653 : CollatzResearch.WordTrace tailWord_491653 prefixEnd_491653 252454304225070139076435 := by
  unfold tailWord_491653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17932058087832623492503613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11954705391888415661669075 17932058087832623492503613)
  ·
    refine ⟨6724521782937233809688855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17932058087832623492503613 6724521782937233809688855)
    ·
      refine ⟨10086782674405850714533283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724521782937233809688855 10086782674405850714533283)
      ·
        refine ⟨15130174011608776071799925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10086782674405850714533283 15130174011608776071799925)
        ·
          refine ⟨1418453813588322756731243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15130174011608776071799925 1418453813588322756731243)
          ·
            refine ⟨2127680720382484135096865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418453813588322756731243 2127680720382484135096865)
            ·
              refine ⟨1595760540286863101322649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127680720382484135096865 1595760540286863101322649)
              ·
                refine ⟨1196820405215147325991987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595760540286863101322649 1196820405215147325991987)
                ·
                  refine ⟨1795230607822720988987981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196820405215147325991987 1795230607822720988987981)
                  ·
                    refine ⟨673211477933520370870493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795230607822720988987981 673211477933520370870493)
                    ·
                      refine ⟨252454304225070139076435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673211477933520370870493 252454304225070139076435)
                      ·
                        rfl

theorem cell23_491653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_491653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491653 prefixEnd_491653 := by exact prefixLift 491653
  have htrace : WordTrace (prefixWord ++ tailWord_491653) baseStart_491653 baseEnd_491653 := by
    simpa [prefixWord, tailWord_491653, baseEnd_491653] using wordTrace_append hprefix tailTrace_491653
  have hstable : (prefixWord ++ tailWord_491653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491653).length < 2 ^ (prefixWord ++ tailWord_491653).sum := by decide
  have hdescent : baseEnd_491653 < baseStart_491653 := by decide
  rcases family_descends (prefixWord ++ tailWord_491653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491687 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_491687 : Nat := 118140960795 + 491687 * 2 ^ 59
def prefixEnd_491687 : Nat := 4983230072969 + 3 ^ 40 * 491687 * 2
def baseEnd_491687 : Nat := 252471762567323006051279

theorem tailTrace_491687 : CollatzResearch.WordTrace tailWord_491687 prefixEnd_491687 252471762567323006051279 := by
  unfold tailWord_491687
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933298169709447299241315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11955532113139631532827543 17933298169709447299241315)
  ·
    refine ⟨26899947254564170948861973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17933298169709447299241315 26899947254564170948861973)
    ·
      refine ⟨1260935027557695513227905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26899947254564170948861973 1260935027557695513227905)
      ·
        refine ⟨945701270668271634920929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1260935027557695513227905 945701270668271634920929)
        ·
          refine ⟨709275953001203726190697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945701270668271634920929 709275953001203726190697)
          ·
            refine ⟨531956964750902794643023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709275953001203726190697 531956964750902794643023)
            ·
              refine ⟨797935447126354191964535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531956964750902794643023 797935447126354191964535)
              ·
                refine ⟨1196903170689531287946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797935447126354191964535 1196903170689531287946803)
                ·
                  refine ⟨1795354756034296931920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196903170689531287946803 1795354756034296931920205)
                  ·
                    refine ⟨673258033512861349470077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795354756034296931920205 673258033512861349470077)
                    ·
                      refine ⟨252471762567323006051279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673258033512861349470077 252471762567323006051279)
                      ·
                        rfl

theorem cell23_491687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_491687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491687 prefixEnd_491687 := by exact prefixLift 491687
  have htrace : WordTrace (prefixWord ++ tailWord_491687) baseStart_491687 baseEnd_491687 := by
    simpa [prefixWord, tailWord_491687, baseEnd_491687] using wordTrace_append hprefix tailTrace_491687
  have hstable : (prefixWord ++ tailWord_491687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491687).length < 2 ^ (prefixWord ++ tailWord_491687).sum := by decide
  have hdescent : baseEnd_491687 < baseStart_491687 := by decide
  rcases family_descends (prefixWord ++ tailWord_491687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491694 : List Nat := [4, 1, 4, 2, 2, 1, 2, 7]
def baseStart_491694 : Nat := 118140960795 + 491694 * 2 ^ 59
def prefixEnd_491694 : Nat := 4983230072969 + 3 ^ 40 * 491694 * 2
def baseEnd_491694 : Nat := 9350939145626091802361

theorem tailTrace_491694 : CollatzResearch.WordTrace tailWord_491694 prefixEnd_491694 9350939145626091802361 := by
  unfold tailWord_491694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241694185085510936843267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11955702320456058329830757 2241694185085510936843267)
  ·
    refine ⟨3362541277628266405264901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2241694185085510936843267 3362541277628266405264901)
    ·
      refine ⟨630476489555299950987169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3362541277628266405264901 630476489555299950987169)
      ·
        refine ⟨472857367166474963240377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630476489555299950987169 472857367166474963240377)
        ·
          refine ⟨354643025374856222430283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472857367166474963240377 354643025374856222430283)
          ·
            refine ⟨531964538062284333645425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354643025374856222430283 531964538062284333645425)
            ·
              refine ⟨398973403546713250234069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531964538062284333645425 398973403546713250234069)
              ·
                refine ⟨9350939145626091802361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398973403546713250234069 9350939145626091802361)
                ·
                  rfl

theorem cell23_491694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_491694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491694 prefixEnd_491694 := by exact prefixLift 491694
  have htrace : WordTrace (prefixWord ++ tailWord_491694) baseStart_491694 baseEnd_491694 := by
    simpa [prefixWord, tailWord_491694, baseEnd_491694] using wordTrace_append hprefix tailTrace_491694
  have hstable : (prefixWord ++ tailWord_491694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491694).length < 2 ^ (prefixWord ++ tailWord_491694).sum := by decide
  have hdescent : baseEnd_491694 < baseStart_491694 := by decide
  rcases family_descends (prefixWord ++ tailWord_491694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491706 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_491706 : Nat := 118140960795 + 491706 * 2 ^ 59
def prefixEnd_491706 : Nat := 4983230072969 + 3 ^ 40 * 491706 * 2
def baseEnd_491706 : Nat := 252481518699758431713691

theorem tailTrace_491706 : CollatzResearch.WordTrace tailWord_491706 prefixEnd_491706 252481518699758431713691 := by
  unfold tailWord_491706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483497789160153386045743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11955994104427075696121981 4483497789160153386045743)
  ·
    refine ⟨6725246683740230079068615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483497789160153386045743 6725246683740230079068615)
    ·
      refine ⟨10087870025610345118602923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725246683740230079068615 10087870025610345118602923)
      ·
        refine ⟨15131805038415517677904385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10087870025610345118602923 15131805038415517677904385)
        ·
          refine ⟨11348853778811638258428289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15131805038415517677904385 11348853778811638258428289)
          ·
            refine ⟨8511640334108728693821217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11348853778811638258428289 8511640334108728693821217)
            ·
              refine ⟨6383730250581546520365913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511640334108728693821217 6383730250581546520365913)
              ·
                refine ⟨4787797687936159890274435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383730250581546520365913 4787797687936159890274435)
                ·
                  refine ⟨7181696531904239835411653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787797687936159890274435 7181696531904239835411653)
                  ·
                    refine ⟨1346568099732044969139685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181696531904239835411653 1346568099732044969139685)
                    ·
                      refine ⟨252481518699758431713691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1346568099732044969139685 252481518699758431713691)
                      ·
                        rfl

theorem cell23_491706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_491706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491706 prefixEnd_491706 := by exact prefixLift 491706
  have htrace : WordTrace (prefixWord ++ tailWord_491706) baseStart_491706 baseEnd_491706 := by
    simpa [prefixWord, tailWord_491706, baseEnd_491706] using wordTrace_append hprefix tailTrace_491706
  have hstable : (prefixWord ++ tailWord_491706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491706).length < 2 ^ (prefixWord ++ tailWord_491706).sum := by decide
  have hdescent : baseEnd_491706 < baseStart_491706 := by decide
  rcases family_descends (prefixWord ++ tailWord_491706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491753 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 5, 2]
def baseStart_491753 : Nat := 118140960795 + 491753 * 2 ^ 59
def prefixEnd_491753 : Nat := 4983230072969 + 3 ^ 40 * 491753 * 2
def baseEnd_491753 : Nat := 252505652290519747825975

theorem tailTrace_491753 : CollatzResearch.WordTrace tailWord_491753 prefixEnd_491753 252505652290519747825975 := by
  unfold tailWord_491753
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935705387470340571143913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11957136924980227047429275 17935705387470340571143913)
  ·
    refine ⟨13451779040602755428357935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17935705387470340571143913 13451779040602755428357935)
    ·
      refine ⟨20177668560904133142536903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451779040602755428357935 20177668560904133142536903)
      ·
        refine ⟨30266502841356199713805355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177668560904133142536903 30266502841356199713805355)
        ·
          refine ⟨45399754262034299570708033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266502841356199713805355 45399754262034299570708033)
          ·
            refine ⟨34049815696525724678031025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45399754262034299570708033 34049815696525724678031025)
            ·
              refine ⟨25537361772394293508523269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34049815696525724678031025 25537361772394293508523269)
              ·
                refine ⟨4788255332323930032848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25537361772394293508523269 4788255332323930032848113)
                ·
                  refine ⟨3591191499242947524636085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788255332323930032848113 3591191499242947524636085)
                  ·
                    refine ⟨336674203054026330434633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3591191499242947524636085 336674203054026330434633)
                    ·
                      refine ⟨252505652290519747825975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336674203054026330434633 252505652290519747825975)
                      ·
                        rfl

theorem cell23_491753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5, 2].length) (baseStart_491753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491753 prefixEnd_491753 := by exact prefixLift 491753
  have htrace : WordTrace (prefixWord ++ tailWord_491753) baseStart_491753 baseEnd_491753 := by
    simpa [prefixWord, tailWord_491753, baseEnd_491753] using wordTrace_append hprefix tailTrace_491753
  have hstable : (prefixWord ++ tailWord_491753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491753).length < 2 ^ (prefixWord ++ tailWord_491753).sum := by decide
  have hdescent : baseEnd_491753 < baseStart_491753 := by decide
  rcases family_descends (prefixWord ++ tailWord_491753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491756 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_491756 : Nat := 118140960795 + 491756 * 2 ^ 59
def prefixEnd_491756 : Nat := 4983230072969 + 3 ^ 40 * 491756 * 2
def baseEnd_491756 : Nat := 252507192732483236088461

theorem tailTrace_491756 : CollatzResearch.WordTrace tailWord_491756 prefixEnd_491756 252507192732483236088461 := by
  unfold tailWord_491756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967907403229736041751561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11957209870972981389002081 8967907403229736041751561)
  ·
    refine ⟨6725930552422302031313671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8967907403229736041751561 6725930552422302031313671)
    ·
      refine ⟨10088895828633453046970507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725930552422302031313671 10088895828633453046970507)
      ·
        refine ⟨15133343742950179570455761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088895828633453046970507 15133343742950179570455761)
        ·
          refine ⟨11350007807212634677841821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15133343742950179570455761 11350007807212634677841821)
          ·
            refine ⟨4256252927704738004190683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11350007807212634677841821 4256252927704738004190683)
            ·
              refine ⟨6384379391557107006286025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256252927704738004190683 6384379391557107006286025)
              ·
                refine ⟨4788284543667830254714519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384379391557107006286025 4788284543667830254714519)
                ·
                  refine ⟨7182426815501745382071779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788284543667830254714519 7182426815501745382071779)
                  ·
                    refine ⟨10773640223252618073107669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7182426815501745382071779 10773640223252618073107669)
                    ·
                      refine ⟨252507192732483236088461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10773640223252618073107669 252507192732483236088461)
                      ·
                        rfl

theorem cell23_491756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_491756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491756 prefixEnd_491756 := by exact prefixLift 491756
  have htrace : WordTrace (prefixWord ++ tailWord_491756) baseStart_491756 baseEnd_491756 := by
    simpa [prefixWord, tailWord_491756, baseEnd_491756] using wordTrace_append hprefix tailTrace_491756
  have hstable : (prefixWord ++ tailWord_491756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491756).length < 2 ^ (prefixWord ++ tailWord_491756).sum := by decide
  have hdescent : baseEnd_491756 < baseStart_491756 := by decide
  rcases family_descends (prefixWord ++ tailWord_491756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491763 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 2, 5]
def baseStart_491763 : Nat := 118140960795 + 491763 * 2 ^ 59
def prefixEnd_491763 : Nat := 4983230072969 + 3 ^ 40 * 491763 * 2
def baseEnd_491763 : Nat := 84170262365688236233643

theorem tailTrace_491763 : CollatzResearch.WordTrace tailWord_491763 prefixEnd_491763 84170262365688236233643 := by
  unfold tailWord_491763
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936070117434112279007943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11957380078289408186005295 17936070117434112279007943)
  ·
    refine ⟨26904105176151168418511915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936070117434112279007943 26904105176151168418511915)
    ·
      refine ⟨40356157764226752627767873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26904105176151168418511915 40356157764226752627767873)
      ·
        refine ⟨30267118323170064470825905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40356157764226752627767873 30267118323170064470825905)
        ·
          refine ⟨22700338742377548353119429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30267118323170064470825905 22700338742377548353119429)
          ·
            refine ⟨4256313514195790316209893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22700338742377548353119429 4256313514195790316209893)
            ·
              refine ⟨798058783911710684289355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4256313514195790316209893 798058783911710684289355)
              ·
                refine ⟨1197088175867566026434033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798058783911710684289355 1197088175867566026434033)
                ·
                  refine ⟨897816131900674519825525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197088175867566026434033 897816131900674519825525)
                  ·
                    refine ⟨84170262365688236233643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 897816131900674519825525 84170262365688236233643)
                    ·
                      rfl

theorem cell23_491763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].length) (baseStart_491763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491763 prefixEnd_491763 := by exact prefixLift 491763
  have htrace : WordTrace (prefixWord ++ tailWord_491763) baseStart_491763 baseEnd_491763 := by
    simpa [prefixWord, tailWord_491763, baseEnd_491763] using wordTrace_append hprefix tailTrace_491763
  have hstable : (prefixWord ++ tailWord_491763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491763).length < 2 ^ (prefixWord ++ tailWord_491763).sum := by decide
  have hdescent : baseEnd_491763 < baseStart_491763 := by decide
  rcases family_descends (prefixWord ++ tailWord_491763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491800 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_491800 : Nat := 118140960795 + 491800 * 2 ^ 59
def prefixEnd_491800 : Nat := 4983230072969 + 3 ^ 40 * 491800 * 2
def baseEnd_491800 : Nat := 252529785881281063938259

theorem tailTrace_491800 : CollatzResearch.WordTrace tailWord_491800 prefixEnd_491800 252529785881281063938259 := by
  unfold tailWord_491800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8968709809150033799052427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11958279745533378398736569 8968709809150033799052427)
  ·
    refine ⟨13453064713725050698578641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8968709809150033799052427 13453064713725050698578641)
    ·
      refine ⟨10089798535293788023933981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13453064713725050698578641 10089798535293788023933981)
      ·
        refine ⟨3783674450735170508975243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10089798535293788023933981 3783674450735170508975243)
        ·
          refine ⟨5675511676102755763462865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783674450735170508975243 5675511676102755763462865)
          ·
            refine ⟨4256633757077066822597149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675511676102755763462865 4256633757077066822597149)
            ·
              refine ⟨1596237658903900058473931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256633757077066822597149 1596237658903900058473931)
              ·
                refine ⟨2394356488355850087710897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596237658903900058473931 2394356488355850087710897)
                ·
                  refine ⟨1795767366266887565783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394356488355850087710897 1795767366266887565783173)
                  ·
                    refine ⟨336706381175041418584345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795767366266887565783173 336706381175041418584345)
                    ·
                      refine ⟨252529785881281063938259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336706381175041418584345 252529785881281063938259)
                      ·
                        rfl

theorem cell23_491800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_491800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491800 prefixEnd_491800 := by exact prefixLift 491800
  have htrace : WordTrace (prefixWord ++ tailWord_491800) baseStart_491800 baseEnd_491800 := by
    simpa [prefixWord, tailWord_491800, baseEnd_491800] using wordTrace_append hprefix tailTrace_491800
  have hstable : (prefixWord ++ tailWord_491800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491800).length < 2 ^ (prefixWord ++ tailWord_491800).sum := by decide
  have hdescent : baseEnd_491800 < baseStart_491800 := by decide
  rcases family_descends (prefixWord ++ tailWord_491800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491803 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3]
def baseStart_491803 : Nat := 118140960795 + 491803 * 2 ^ 59
def prefixEnd_491803 : Nat := 4983230072969 + 3 ^ 40 * 491803 * 2
def baseEnd_491803 : Nat := 252531326323244552200745

theorem tailTrace_491803 : CollatzResearch.WordTrace tailWord_491803 prefixEnd_491803 252531326323244552200745 := by
  unfold tailWord_491803
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937529037289199110464063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11958352691526132740309375 17937529037289199110464063)
  ·
    refine ⟨26906293555933798665696095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17937529037289199110464063 26906293555933798665696095)
    ·
      refine ⟨40359440333900697998544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26906293555933798665696095 40359440333900697998544143)
      ·
        refine ⟨60539160500851046997816215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40359440333900697998544143 60539160500851046997816215)
        ·
          refine ⟨90808740751276570496724323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60539160500851046997816215 90808740751276570496724323)
          ·
            refine ⟨136213111126914855745086485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90808740751276570496724323 136213111126914855745086485)
            ·
              refine ⟨6384989584074133863050929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136213111126914855745086485 6384989584074133863050929)
              ·
                refine ⟨4788742188055600397288197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384989584074133863050929 4788742188055600397288197)
                ·
                  refine ⟨897889160260425074491537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4788742188055600397288197 897889160260425074491537)
                  ·
                    refine ⟨673416870195318805868653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897889160260425074491537 673416870195318805868653)
                    ·
                      refine ⟨252531326323244552200745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673416870195318805868653 252531326323244552200745)
                      ·
                        rfl

theorem cell23_491803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].length) (baseStart_491803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491803 prefixEnd_491803 := by exact prefixLift 491803
  have htrace : WordTrace (prefixWord ++ tailWord_491803) baseStart_491803 baseEnd_491803 := by
    simpa [prefixWord, tailWord_491803, baseEnd_491803] using wordTrace_append hprefix tailTrace_491803
  have hstable : (prefixWord ++ tailWord_491803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491803).length < 2 ^ (prefixWord ++ tailWord_491803).sum := by decide
  have hdescent : baseEnd_491803 < baseStart_491803 := by decide
  rcases family_descends (prefixWord ++ tailWord_491803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491810 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_491810 : Nat := 118140960795 + 491810 * 2 ^ 59
def prefixEnd_491810 : Nat := 4983230072969 + 3 ^ 40 * 491810 * 2
def baseEnd_491810 : Nat := 84178306895942008271071

theorem tailTrace_491810 : CollatzResearch.WordTrace tailWord_491810 prefixEnd_491810 84178306895942008271071 := by
  unfold tailWord_491810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484446087065959826492221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11958522898842559537312589 4484446087065959826492221)
  ·
    refine ⟨1681667282649734934934583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4484446087065959826492221 1681667282649734934934583)
    ·
      refine ⟨2522500923974602402401875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681667282649734934934583 2522500923974602402401875)
      ·
        refine ⟨3783751385961903603602813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522500923974602402401875 3783751385961903603602813)
        ·
          refine ⟨1418906769735713851351055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3783751385961903603602813 1418906769735713851351055)
          ·
            refine ⟨2128360154603570777026583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418906769735713851351055 2128360154603570777026583)
            ·
              refine ⟨3192540231905356165539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128360154603570777026583 3192540231905356165539875)
              ·
                refine ⟨4788810347858034248309813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192540231905356165539875 4788810347858034248309813)
                ·
                  refine ⟨448950970111690710779045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788810347858034248309813 448950970111690710779045)
                  ·
                    refine ⟨84178306895942008271071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448950970111690710779045 84178306895942008271071)
                    ·
                      rfl

theorem cell23_491810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_491810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491810 prefixEnd_491810 := by exact prefixLift 491810
  have htrace : WordTrace (prefixWord ++ tailWord_491810) baseStart_491810 baseEnd_491810 := by
    simpa [prefixWord, tailWord_491810, baseEnd_491810] using wordTrace_append hprefix tailTrace_491810
  have hstable : (prefixWord ++ tailWord_491810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491810).length < 2 ^ (prefixWord ++ tailWord_491810).sum := by decide
  have hdescent : baseEnd_491810 < baseStart_491810 := by decide
  rcases family_descends (prefixWord ++ tailWord_491810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491820 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_491820 : Nat := 118140960795 + 491820 * 2 ^ 59
def prefixEnd_491820 : Nat := 4983230072969 + 3 ^ 40 * 491820 * 2
def baseEnd_491820 : Nat := 252540055494370985688167

theorem tailTrace_491820 : CollatzResearch.WordTrace tailWord_491820 prefixEnd_491820 252540055494370985688167 := by
  unfold tailWord_491820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969074539113805506916457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11958766052151740675888609 8969074539113805506916457)
  ·
    refine ⟨6726805904335354130187343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8969074539113805506916457 6726805904335354130187343)
    ·
      refine ⟨10090208856503031195281015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6726805904335354130187343 10090208856503031195281015)
      ·
        refine ⟨15135313284754546792921523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090208856503031195281015 15135313284754546792921523)
        ·
          refine ⟨22702969927131820189382285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135313284754546792921523 22702969927131820189382285)
          ·
            refine ⟨8513613722674432571018357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22702969927131820189382285 8513613722674432571018357)
            ·
              refine ⟨798151286500728053532971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8513613722674432571018357 798151286500728053532971)
              ·
                refine ⟨1197226929751092080299457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798151286500728053532971 1197226929751092080299457)
                ·
                  refine ⟨897920197313319060224593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197226929751092080299457 897920197313319060224593)
                  ·
                    refine ⟨673440147984989295168445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897920197313319060224593 673440147984989295168445)
                    ·
                      refine ⟨252540055494370985688167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673440147984989295168445 252540055494370985688167)
                      ·
                        rfl

theorem cell23_491820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_491820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491820 prefixEnd_491820 := by exact prefixLift 491820
  have htrace : WordTrace (prefixWord ++ tailWord_491820) baseStart_491820 baseEnd_491820 := by
    simpa [prefixWord, tailWord_491820, baseEnd_491820] using wordTrace_append hprefix tailTrace_491820
  have hstable : (prefixWord ++ tailWord_491820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491820).length < 2 ^ (prefixWord ++ tailWord_491820).sum := by decide
  have hdescent : baseEnd_491820 < baseStart_491820 := by decide
  rcases family_descends (prefixWord ++ tailWord_491820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491827 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 1, 4]
def baseStart_491827 : Nat := 118140960795 + 491827 * 2 ^ 59
def prefixEnd_491827 : Nat := 4983230072969 + 3 ^ 40 * 491827 * 2
def baseEnd_491827 : Nat := 84181216619650819433545

theorem tailTrace_491827 : CollatzResearch.WordTrace tailWord_491827 prefixEnd_491827 84181216619650819433545 := by
  unfold tailWord_491827
  simp only [CollatzResearch.WordTrace]
  refine ⟨17938404389202251209337735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11958936259468167472891823 17938404389202251209337735)
  ·
    refine ⟨26907606583803376814006603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17938404389202251209337735 26907606583803376814006603)
    ·
      refine ⟨40361409875705065221009905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26907606583803376814006603 40361409875705065221009905)
      ·
        refine ⟨30271057406778798915757429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40361409875705065221009905 30271057406778798915757429)
        ·
          refine ⟨2837911631885512398352259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30271057406778798915757429 2837911631885512398352259)
          ·
            refine ⟨4256867447828268597528389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837911631885512398352259 4256867447828268597528389)
            ·
              refine ⟨798162646467800362036573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4256867447828268597528389 798162646467800362036573)
              ·
                refine ⟨299310992425425135763715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798162646467800362036573 299310992425425135763715)
                ·
                  refine ⟨448966488638137703645573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299310992425425135763715 448966488638137703645573)
                  ·
                    refine ⟨84181216619650819433545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448966488638137703645573 84181216619650819433545)
                    ·
                      rfl

theorem cell23_491827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 4].length) (baseStart_491827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491827 prefixEnd_491827 := by exact prefixLift 491827
  have htrace : WordTrace (prefixWord ++ tailWord_491827) baseStart_491827 baseEnd_491827 := by
    simpa [prefixWord, tailWord_491827, baseEnd_491827] using wordTrace_append hprefix tailTrace_491827
  have hstable : (prefixWord ++ tailWord_491827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491827).length < 2 ^ (prefixWord ++ tailWord_491827).sum := by decide
  have hdescent : baseEnd_491827 < baseStart_491827 := by decide
  rcases family_descends (prefixWord ++ tailWord_491827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491844 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_491844 : Nat := 118140960795 + 491844 * 2 ^ 59
def prefixEnd_491844 : Nat := 4983230072969 + 3 ^ 40 * 491844 * 2
def baseEnd_491844 : Nat := 84184126343359630596019

theorem tailTrace_491844 : CollatzResearch.WordTrace tailWord_491844 prefixEnd_491844 84184126343359630596019 := by
  unfold tailWord_491844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969512215070331556353293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11959349620093775408471057 8969512215070331556353293)
  ·
    refine ⟨3363567080651374333632485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8969512215070331556353293 3363567080651374333632485)
    ·
      refine ⟨630668827622132687556091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3363567080651374333632485 630668827622132687556091)
      ·
        refine ⟨946003241433199031334137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630668827622132687556091 946003241433199031334137)
        ·
          refine ⟨709502431074899273500603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946003241433199031334137 709502431074899273500603)
          ·
            refine ⟨1064253646612348910250905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709502431074899273500603 1064253646612348910250905)
            ·
              refine ⟨798190234959261682688179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064253646612348910250905 798190234959261682688179)
              ·
                refine ⟨1197285352438892524032269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798190234959261682688179 1197285352438892524032269)
                ·
                  refine ⟨448982007164584696512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197285352438892524032269 448982007164584696512101)
                  ·
                    refine ⟨84184126343359630596019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448982007164584696512101 84184126343359630596019)
                    ·
                      rfl

theorem cell23_491844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_491844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491844 prefixEnd_491844 := by exact prefixLift 491844
  have htrace : WordTrace (prefixWord ++ tailWord_491844) baseStart_491844 baseEnd_491844 := by
    simpa [prefixWord, tailWord_491844, baseEnd_491844] using wordTrace_append hprefix tailTrace_491844
  have hstable : (prefixWord ++ tailWord_491844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491844).length < 2 ^ (prefixWord ++ tailWord_491844).sum := by decide
  have hdescent : baseEnd_491844 < baseStart_491844 := by decide
  rcases family_descends (prefixWord ++ tailWord_491844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491901 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_491901 : Nat := 118140960795 + 491901 * 2 ^ 59
def prefixEnd_491901 : Nat := 4983230072969 + 3 ^ 40 * 491901 * 2
def baseEnd_491901 : Nat := 252581647427385168775295

theorem tailTrace_491901 : CollatzResearch.WordTrace tailWord_491901 prefixEnd_491901 252581647427385168775295 := by
  unfold tailWord_491901
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941103390934161847531557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11960735593956107898354371 17941103390934161847531557)
  ·
    refine ⟨3363956885800155346412167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17941103390934161847531557 3363956885800155346412167)
    ·
      refine ⟨5045935328700233019618251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363956885800155346412167 5045935328700233019618251)
      ·
        refine ⟨7568902993050349529427377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045935328700233019618251 7568902993050349529427377)
        ·
          refine ⟨5676677244787762147070533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7568902993050349529427377 5676677244787762147070533)
          ·
            refine ⟨1064376983397705402575725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5676677244787762147070533 1064376983397705402575725)
            ·
              refine ⟨399141368774139525965897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1064376983397705402575725 399141368774139525965897)
              ·
                refine ⟨299356026580604644474423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399141368774139525965897 299356026580604644474423)
                ·
                  refine ⟨449034039870906966711635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299356026580604644474423 449034039870906966711635)
                  ·
                    refine ⟨673551059806360450067453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449034039870906966711635 673551059806360450067453)
                    ·
                      refine ⟨252581647427385168775295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673551059806360450067453 252581647427385168775295)
                      ·
                        rfl

theorem cell23_491901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_491901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491901 prefixEnd_491901 := by exact prefixLift 491901
  have htrace : WordTrace (prefixWord ++ tailWord_491901) baseStart_491901 baseEnd_491901 := by
    simpa [prefixWord, tailWord_491901, baseEnd_491901] using wordTrace_append hprefix tailTrace_491901
  have hstable : (prefixWord ++ tailWord_491901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491901).length < 2 ^ (prefixWord ++ tailWord_491901).sum := by decide
  have hdescent : baseEnd_491901 < baseStart_491901 := by decide
  rcases family_descends (prefixWord ++ tailWord_491901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491903 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_491903 : Nat := 118140960795 + 491903 * 2 ^ 59
def prefixEnd_491903 : Nat := 4983230072969 + 3 ^ 40 * 491903 * 2
def baseEnd_491903 : Nat := 252582674388694160950285

theorem tailTrace_491903 : CollatzResearch.WordTrace tailWord_491903 prefixEnd_491903 252582674388694160950285 := by
  unfold tailWord_491903
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941176336926916189104363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11960784224617944126069575 17941176336926916189104363)
  ·
    refine ⟨26911764505390374283656545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17941176336926916189104363 26911764505390374283656545)
    ·
      refine ⟨20183823379042780712742409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26911764505390374283656545 20183823379042780712742409)
      ·
        refine ⟨15137867534282085534556807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183823379042780712742409 15137867534282085534556807)
        ·
          refine ⟨22706801301423128301835211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137867534282085534556807 22706801301423128301835211)
          ·
            refine ⟨34060201952134692452752817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22706801301423128301835211 34060201952134692452752817)
            ·
              refine ⟨25545151464101019339564613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34060201952134692452752817 25545151464101019339564613)
              ·
                refine ⟨4789715899518941126168365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25545151464101019339564613 4789715899518941126168365)
                ·
                  refine ⟨1796143462319602922313137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4789715899518941126168365 1796143462319602922313137)
                  ·
                    refine ⟨1347107596739702191734853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796143462319602922313137 1347107596739702191734853)
                    ·
                      refine ⟨252582674388694160950285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1347107596739702191734853 252582674388694160950285)
                      ·
                        rfl

theorem cell23_491903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_491903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491903 prefixEnd_491903 := by exact prefixLift 491903
  have htrace : WordTrace (prefixWord ++ tailWord_491903) baseStart_491903 baseEnd_491903 := by
    simpa [prefixWord, tailWord_491903, baseEnd_491903] using wordTrace_append hprefix tailTrace_491903
  have hstable : (prefixWord ++ tailWord_491903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491903).length < 2 ^ (prefixWord ++ tailWord_491903).sum := by decide
  have hdescent : baseEnd_491903 < baseStart_491903 := by decide
  rcases family_descends (prefixWord ++ tailWord_491903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491913 : List Nat := [1, 2, 1, 1, 6, 1, 1, 10]
def baseStart_491913 : Nat := 118140960795 + 491913 * 2 ^ 59
def prefixEnd_491913 : Nat := 4983230072969 + 3 ^ 40 * 491913 * 2
def baseEnd_491913 : Nat := 9355104044268115623157

theorem tailTrace_491913 : CollatzResearch.WordTrace tailWord_491913 prefixEnd_491913 9355104044268115623157 := by
  unfold tailWord_491913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941541066890687896968393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11961027377927125264645595 17941541066890687896968393)
  ·
    refine ⟨13456155800168015922726295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17941541066890687896968393 13456155800168015922726295)
    ·
      refine ⟨20184233700252023884089443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13456155800168015922726295 20184233700252023884089443)
      ·
        refine ⟨30276350550378035826134165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20184233700252023884089443 30276350550378035826134165)
        ·
          refine ⟨1419203932048970429350039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30276350550378035826134165 1419203932048970429350039)
          ·
            refine ⟨2128805898073455644025059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419203932048970429350039 2128805898073455644025059)
            ·
              refine ⟨3193208847110183466037589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128805898073455644025059 3193208847110183466037589)
              ·
                refine ⟨9355104044268115623157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3193208847110183466037589 9355104044268115623157)
                ·
                  rfl

theorem cell23_491913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 10].length) (baseStart_491913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491913 prefixEnd_491913 := by exact prefixLift 491913
  have htrace : WordTrace (prefixWord ++ tailWord_491913) baseStart_491913 baseEnd_491913 := by
    simpa [prefixWord, tailWord_491913, baseEnd_491913] using wordTrace_append hprefix tailTrace_491913
  have hstable : (prefixWord ++ tailWord_491913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491913).length < 2 ^ (prefixWord ++ tailWord_491913).sum := by decide
  have hdescent : baseEnd_491913 < baseStart_491913 := by decide
  rcases family_descends (prefixWord ++ tailWord_491913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491927 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_491927 : Nat := 118140960795 + 491927 * 2 ^ 59
def prefixEnd_491927 : Nat := 4983230072969 + 3 ^ 40 * 491927 * 2
def baseEnd_491927 : Nat := 252594997924402067050175

theorem tailTrace_491927 : CollatzResearch.WordTrace tailWord_491927 prefixEnd_491927 252594997924402067050175 := by
  unfold tailWord_491927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942051688839968287978035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11961367792559978858652023 17942051688839968287978035)
  ·
    refine ⟨26913077533259952431967053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17942051688839968287978035 26913077533259952431967053)
    ·
      refine ⟨10092404074972482161987645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26913077533259952431967053 10092404074972482161987645)
      ·
        refine ⟨3784651528114680810745367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10092404074972482161987645 3784651528114680810745367)
        ·
          refine ⟨5676977292172021216118051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784651528114680810745367 5676977292172021216118051)
          ·
            refine ⟨8515465938258031824177077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676977292172021216118051 8515465938258031824177077)
            ·
              refine ⟨798324931711690483516601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8515465938258031824177077 798324931711690483516601)
              ·
                refine ⟨598743698783767862637451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798324931711690483516601 598743698783767862637451)
                ·
                  refine ⟨898115548175651793956177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598743698783767862637451 898115548175651793956177)
                  ·
                    refine ⟨673586661131738845467133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898115548175651793956177 673586661131738845467133)
                    ·
                      refine ⟨252594997924402067050175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673586661131738845467133 252594997924402067050175)
                      ·
                        rfl

theorem cell23_491927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_491927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491927 prefixEnd_491927 := by exact prefixLift 491927
  have htrace : WordTrace (prefixWord ++ tailWord_491927) baseStart_491927 baseEnd_491927 := by
    simpa [prefixWord, tailWord_491927, baseEnd_491927] using wordTrace_append hprefix tailTrace_491927
  have hstable : (prefixWord ++ tailWord_491927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491927).length < 2 ^ (prefixWord ++ tailWord_491927).sum := by decide
  have hdescent : baseEnd_491927 < baseStart_491927 := by decide
  rcases family_descends (prefixWord ++ tailWord_491927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491940 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_491940 : Nat := 118140960795 + 491940 * 2 ^ 59
def prefixEnd_491940 : Nat := 4983230072969 + 3 ^ 40 * 491940 * 2
def baseEnd_491940 : Nat := 252601673172910516187615

theorem tailTrace_491940 : CollatzResearch.WordTrace tailWord_491940 prefixEnd_491940 252601673172910516187615 := by
  unfold tailWord_491940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971262918896435754100637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11961683891861914338800849 8971262918896435754100637)
  ·
    refine ⟨3364223594586163407787739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8971262918896435754100637 3364223594586163407787739)
    ·
      refine ⟨5046335391879245111681609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364223594586163407787739 5046335391879245111681609)
      ·
        refine ⟨3784751543909433833761207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5046335391879245111681609 3784751543909433833761207)
        ·
          refine ⟨5677127315864150750641811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784751543909433833761207 5677127315864150750641811)
          ·
            refine ⟨8515690973796226125962717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677127315864150750641811 8515690973796226125962717)
            ·
              refine ⟨3193384115173584797236019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8515690973796226125962717 3193384115173584797236019)
              ·
                refine ⟨4790076172760377195854029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193384115173584797236019 4790076172760377195854029)
                ·
                  refine ⟨1796278564785141448445261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4790076172760377195854029 1796278564785141448445261)
                  ·
                    refine ⟨673604461794428043166973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796278564785141448445261 673604461794428043166973)
                    ·
                      refine ⟨252601673172910516187615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673604461794428043166973 252601673172910516187615)
                      ·
                        rfl

theorem cell23_491940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_491940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491940 prefixEnd_491940 := by exact prefixLift 491940
  have htrace : WordTrace (prefixWord ++ tailWord_491940) baseStart_491940 baseEnd_491940 := by
    simpa [prefixWord, tailWord_491940, baseEnd_491940] using wordTrace_append hprefix tailTrace_491940
  have hstable : (prefixWord ++ tailWord_491940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491940).length < 2 ^ (prefixWord ++ tailWord_491940).sum := by decide
  have hdescent : baseEnd_491940 < baseStart_491940 := by decide
  rcases family_descends (prefixWord ++ tailWord_491940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491944 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_491944 : Nat := 118140960795 + 491944 * 2 ^ 59
def prefixEnd_491944 : Nat := 4983230072969 + 3 ^ 40 * 491944 * 2
def baseEnd_491944 : Nat := 252603727095528500537597

theorem tailTrace_491944 : CollatzResearch.WordTrace tailWord_491944 prefixEnd_491944 252603727095528500537597 := by
  unfold tailWord_491944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971335864889190095673443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11961781153185586794231257 8971335864889190095673443)
  ·
    refine ⟨13457003797333785143510165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971335864889190095673443 13457003797333785143510165)
    ·
      refine ⟨630797053000021178602039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13457003797333785143510165 630797053000021178602039)
      ·
        refine ⟨946195579500031767903059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630797053000021178602039 946195579500031767903059)
        ·
          refine ⟨1419293369250047651854589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946195579500031767903059 1419293369250047651854589)
          ·
            refine ⟨532235013468767869445471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419293369250047651854589 532235013468767869445471)
            ·
              refine ⟨798352520203151804168207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532235013468767869445471 798352520203151804168207)
              ·
                refine ⟨1197528780304727706252311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798352520203151804168207 1197528780304727706252311)
                ·
                  refine ⟨1796293170457091559378467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197528780304727706252311 1796293170457091559378467)
                  ·
                    refine ⟨2694439755685637339067701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796293170457091559378467 2694439755685637339067701)
                    ·
                      refine ⟨252603727095528500537597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2694439755685637339067701 252603727095528500537597)
                      ·
                        rfl

theorem cell23_491944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_491944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_491944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_491944 prefixEnd_491944 := by exact prefixLift 491944
  have htrace : WordTrace (prefixWord ++ tailWord_491944) baseStart_491944 baseEnd_491944 := by
    simpa [prefixWord, tailWord_491944, baseEnd_491944] using wordTrace_append hprefix tailTrace_491944
  have hstable : (prefixWord ++ tailWord_491944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491944).length < 2 ^ (prefixWord ++ tailWord_491944).sum := by decide
  have hdescent : baseEnd_491944 < baseStart_491944 := by decide
  rcases family_descends (prefixWord ++ tailWord_491944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492031 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 2, 2, 2]
def baseStart_492031 : Nat := 118140960795 + 492031 * 2 ^ 59
def prefixEnd_492031 : Nat := 4983230072969 + 3 ^ 40 * 492031 * 2
def baseEnd_492031 : Nat := 252648399912469660149697

theorem tailTrace_492031 : CollatzResearch.WordTrace tailWord_492031 prefixEnd_492031 252648399912469660149697 := by
  unfold tailWord_492031
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945844880463194049763947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11963896586975462699842631 17945844880463194049763947)
  ·
    refine ⟨26918767320694791074645921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17945844880463194049763947 26918767320694791074645921)
    ·
      refine ⟨20189075490521093305984441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26918767320694791074645921 20189075490521093305984441)
      ·
        refine ⟨15141806617890819979488331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20189075490521093305984441 15141806617890819979488331)
        ·
          refine ⟨22712709926836229969232497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15141806617890819979488331 22712709926836229969232497)
          ·
            refine ⟨17034532445127172476924373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22712709926836229969232497 17034532445127172476924373)
            ·
              refine ⟨399246854182668104927915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17034532445127172476924373 399246854182668104927915)
              ·
                refine ⟨598870281274002157391873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399246854182668104927915 598870281274002157391873)
                ·
                  refine ⟨449152710955501618043905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598870281274002157391873 449152710955501618043905)
                  ·
                    refine ⟨336864533216626213532929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449152710955501618043905 336864533216626213532929)
                    ·
                      refine ⟨252648399912469660149697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336864533216626213532929 252648399912469660149697)
                      ·
                        rfl

theorem cell23_492031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_492031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492031 prefixEnd_492031 := by exact prefixLift 492031
  have htrace : WordTrace (prefixWord ++ tailWord_492031) baseStart_492031 baseEnd_492031 := by
    simpa [prefixWord, tailWord_492031, baseEnd_492031] using wordTrace_append hprefix tailTrace_492031
  have hstable : (prefixWord ++ tailWord_492031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492031).length < 2 ^ (prefixWord ++ tailWord_492031).sum := by decide
  have hdescent : baseEnd_492031 < baseStart_492031 := by decide
  rcases family_descends (prefixWord ++ tailWord_492031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492067 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 2, 5]
def baseStart_492067 : Nat := 118140960795 + 492067 * 2 ^ 59
def prefixEnd_492067 : Nat := 4983230072969 + 3 ^ 40 * 492067 * 2
def baseEnd_492067 : Nat := 84222295072010506433177

theorem tailTrace_492067 : CollatzResearch.WordTrace tailWord_492067 prefixEnd_492067 84222295072010506433177 := by
  unfold tailWord_492067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947157908332772198074455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964771938888514798716303 17947157908332772198074455)
  ·
    refine ⟨26920736862499158297111683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17947157908332772198074455 26920736862499158297111683)
    ·
      refine ⟨40381105293748737445667525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26920736862499158297111683 40381105293748737445667525)
      ·
        refine ⟨7571457242577888271062661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40381105293748737445667525 7571457242577888271062661)
        ·
          refine ⟨1419648232983354050824249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7571457242577888271062661 1419648232983354050824249)
          ·
            refine ⟨1064736174737515538118187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419648232983354050824249 1064736174737515538118187)
            ·
              refine ⟨1597104262106273307177281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064736174737515538118187 1597104262106273307177281)
              ·
                refine ⟨1197828196579704980382961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597104262106273307177281 1197828196579704980382961)
                ·
                  refine ⟨898371147434778735287221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197828196579704980382961 898371147434778735287221)
                  ·
                    refine ⟨84222295072010506433177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 898371147434778735287221 84222295072010506433177)
                    ·
                      rfl

theorem cell23_492067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].length) (baseStart_492067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492067 prefixEnd_492067 := by exact prefixLift 492067
  have htrace : WordTrace (prefixWord ++ tailWord_492067) baseStart_492067 baseEnd_492067 := by
    simpa [prefixWord, tailWord_492067, baseEnd_492067] using wordTrace_append hprefix tailTrace_492067
  have hstable : (prefixWord ++ tailWord_492067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492067).length < 2 ^ (prefixWord ++ tailWord_492067).sum := by decide
  have hdescent : baseEnd_492067 < baseStart_492067 := by decide
  rcases family_descends (prefixWord ++ tailWord_492067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492071 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 7]
def baseStart_492071 : Nat := 118140960795 + 492071 * 2 ^ 59
def prefixEnd_492071 : Nat := 4983230072969 + 3 ^ 40 * 492071 * 2
def baseEnd_492071 : Nat := 28074326570961055961057

theorem tailTrace_492071 : CollatzResearch.WordTrace tailWord_492071 prefixEnd_492071 28074326570961055961057 := by
  unfold tailWord_492071
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947303800318280881220067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964869200212187254146711 17947303800318280881220067)
  ·
    refine ⟨26920955700477421321830101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17947303800318280881220067 26920955700477421321830101)
    ·
      refine ⟨630959899229939562230393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26920955700477421321830101 630959899229939562230393)
      ·
        refine ⟨473219924422454671672795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630959899229939562230393 473219924422454671672795)
        ·
          refine ⟨709829886633682007509193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473219924422454671672795 709829886633682007509193)
          ·
            refine ⟨532372414975261505631895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709829886633682007509193 532372414975261505631895)
            ·
              refine ⟨798558622462892258447843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532372414975261505631895 798558622462892258447843)
              ·
                refine ⟨1197837933694338387671765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798558622462892258447843 1197837933694338387671765)
                ·
                  refine ⟨28074326570961055961057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1197837933694338387671765 28074326570961055961057)
                  ·
                    rfl

theorem cell23_492071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 7].length) (baseStart_492071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492071 prefixEnd_492071 := by exact prefixLift 492071
  have htrace : WordTrace (prefixWord ++ tailWord_492071) baseStart_492071 baseEnd_492071 := by
    simpa [prefixWord, tailWord_492071, baseEnd_492071] using wordTrace_append hprefix tailTrace_492071
  have hstable : (prefixWord ++ tailWord_492071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492071).length < 2 ^ (prefixWord ++ tailWord_492071).sum := by decide
  have hdescent : baseEnd_492071 < baseStart_492071 := by decide
  rcases family_descends (prefixWord ++ tailWord_492071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492087 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_492087 : Nat := 118140960795 + 492087 * 2 ^ 59
def prefixEnd_492087 : Nat := 4983230072969 + 3 ^ 40 * 492087 * 2
def baseEnd_492087 : Nat := 252677154829121441049439

theorem tailTrace_492087 : CollatzResearch.WordTrace tailWord_492087 prefixEnd_492087 252677154829121441049439 := by
  unfold tailWord_492087
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947887368260315613802515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965258245506877075868343 17947887368260315613802515)
  ·
    refine ⟨26921831052390473420703773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17947887368260315613802515 26921831052390473420703773)
    ·
      refine ⟨10095686644646427532763915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26921831052390473420703773 10095686644646427532763915)
      ·
        refine ⟨15143529966969641299145873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095686644646427532763915 15143529966969641299145873)
        ·
          refine ⟨11357647475227230974359405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15143529966969641299145873 11357647475227230974359405)
          ·
            refine ⟨4259117803210211615384777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11357647475227230974359405 4259117803210211615384777)
            ·
              refine ⟨3194338352407658711538583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259117803210211615384777 3194338352407658711538583)
              ·
                refine ⟨4791507528611488067307875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194338352407658711538583 4791507528611488067307875)
                ·
                  refine ⟨7187261292917232100961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791507528611488067307875 7187261292917232100961813)
                  ·
                    refine ⟨336902873105495254732585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7187261292917232100961813 336902873105495254732585)
                    ·
                      refine ⟨252677154829121441049439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336902873105495254732585 252677154829121441049439)
                      ·
                        rfl

theorem cell23_492087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_492087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492087 prefixEnd_492087 := by exact prefixLift 492087
  have htrace : WordTrace (prefixWord ++ tailWord_492087) baseStart_492087 baseEnd_492087 := by
    simpa [prefixWord, tailWord_492087, baseEnd_492087] using wordTrace_append hprefix tailTrace_492087
  have hstable : (prefixWord ++ tailWord_492087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492087).length < 2 ^ (prefixWord ++ tailWord_492087).sum := by decide
  have hdescent : baseEnd_492087 < baseStart_492087 := by decide
  rcases family_descends (prefixWord ++ tailWord_492087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492107 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3]
def baseStart_492107 : Nat := 118140960795 + 492107 * 2 ^ 59
def prefixEnd_492107 : Nat := 4983230072969 + 3 ^ 40 * 492107 * 2
def baseEnd_492107 : Nat := 252687424442211362799347

theorem tailTrace_492107 : CollatzResearch.WordTrace tailWord_492107 prefixEnd_492107 252687424442211362799347 := by
  unfold tailWord_492107
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948616828187859029530575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965744552125239353020383 17948616828187859029530575)
  ·
    refine ⟨26922925242281788544295863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948616828187859029530575 26922925242281788544295863)
    ·
      refine ⟨40384387863422682816443795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922925242281788544295863 40384387863422682816443795)
      ·
        refine ⟨60576581795134024224665693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40384387863422682816443795 60576581795134024224665693)
        ·
          refine ⟨22716218173175259084249635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60576581795134024224665693 22716218173175259084249635)
          ·
            refine ⟨34074327259762888626374453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22716218173175259084249635 34074327259762888626374453)
            ·
              refine ⟨3194468180602770808722605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34074327259762888626374453 3194468180602770808722605)
              ·
                refine ⟨1197925567726039053270977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194468180602770808722605 1197925567726039053270977)
                ·
                  refine ⟨898444175794529289953233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197925567726039053270977 898444175794529289953233)
                  ·
                    refine ⟨673833131845896967464925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898444175794529289953233 673833131845896967464925)
                    ·
                      refine ⟨252687424442211362799347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673833131845896967464925 252687424442211362799347)
                      ·
                        rfl

theorem cell23_492107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].length) (baseStart_492107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492107 prefixEnd_492107 := by exact prefixLift 492107
  have htrace : WordTrace (prefixWord ++ tailWord_492107) baseStart_492107 baseEnd_492107 := by
    simpa [prefixWord, tailWord_492107, baseEnd_492107] using wordTrace_append hprefix tailTrace_492107
  have hstable : (prefixWord ++ tailWord_492107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492107).length < 2 ^ (prefixWord ++ tailWord_492107).sum := by decide
  have hdescent : baseEnd_492107 < baseStart_492107 := by decide
  rcases family_descends (prefixWord ++ tailWord_492107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492110 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_492110 : Nat := 118140960795 + 492110 * 2 ^ 59
def prefixEnd_492110 : Nat := 4983230072969 + 3 ^ 40 * 492110 * 2
def baseEnd_492110 : Nat := 28076551653797205673537

theorem tailTrace_492110 : CollatzResearch.WordTrace tailWord_492110 prefixEnd_492110 28076551653797205673537 := by
  unfold tailWord_492110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243590780897123817736223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11965817498117993694593189 2243590780897123817736223)
  ·
    refine ⟨3365386171345685726604335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2243590780897123817736223 3365386171345685726604335)
    ·
      refine ⟨5048079257018528589906503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365386171345685726604335 5048079257018528589906503)
      ·
        refine ⟨7572118885527792884859755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048079257018528589906503 7572118885527792884859755)
        ·
          refine ⟨11358178328291689327289633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572118885527792884859755 11358178328291689327289633)
          ·
            refine ⟨8518633746218766995467225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358178328291689327289633 8518633746218766995467225)
            ·
              refine ⟨6388975309664075246600419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518633746218766995467225 6388975309664075246600419)
              ·
                refine ⟨9583462964496112869900629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388975309664075246600419 9583462964496112869900629)
                ·
                  refine ⟨28076551653797205673537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9583462964496112869900629 28076551653797205673537)
                  ·
                    rfl

theorem cell23_492110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_492110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492110 prefixEnd_492110 := by exact prefixLift 492110
  have htrace : WordTrace (prefixWord ++ tailWord_492110) baseStart_492110 baseEnd_492110 := by
    simpa [prefixWord, tailWord_492110, baseEnd_492110] using wordTrace_append hprefix tailTrace_492110
  have hstable : (prefixWord ++ tailWord_492110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492110).length < 2 ^ (prefixWord ++ tailWord_492110).sum := by decide
  have hdescent : baseEnd_492110 < baseStart_492110 := by decide
  rcases family_descends (prefixWord ++ tailWord_492110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492174 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_492174 : Nat := 118140960795 + 492174 * 2 ^ 59
def prefixEnd_492174 : Nat := 4983230072969 + 3 ^ 40 * 492174 * 2
def baseEnd_492174 : Nat := 84240609215354200220513

theorem tailTrace_492174 : CollatzResearch.WordTrace tailWord_492174 prefixEnd_492174 84240609215354200220513 := by
  unfold tailWord_492174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243882564868141184027447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11967373679296752981479717 2243882564868141184027447)
  ·
    refine ⟨3365823847302211776041171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2243882564868141184027447 3365823847302211776041171)
    ·
      refine ⟨5048735770953317664061757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365823847302211776041171 5048735770953317664061757)
      ·
        refine ⟨1893275914107494124023159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5048735770953317664061757 1893275914107494124023159)
        ·
          refine ⟨2839913871161241186034739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893275914107494124023159 2839913871161241186034739)
          ·
            refine ⟨4259870806741861779052109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839913871161241186034739 4259870806741861779052109)
            ·
              refine ⟨1597451552528198167144541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259870806741861779052109 1597451552528198167144541)
              ·
                refine ⟨599044332198074312679203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597451552528198167144541 599044332198074312679203)
                ·
                  refine ⟨898566498297111469018805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599044332198074312679203 898566498297111469018805)
                  ·
                    refine ⟨84240609215354200220513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 898566498297111469018805 84240609215354200220513)
                    ·
                      rfl

theorem cell23_492174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_492174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492174 prefixEnd_492174 := by exact prefixLift 492174
  have htrace : WordTrace (prefixWord ++ tailWord_492174) baseStart_492174 baseEnd_492174 := by
    simpa [prefixWord, tailWord_492174, baseEnd_492174] using wordTrace_append hprefix tailTrace_492174
  have hstable : (prefixWord ++ tailWord_492174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492174).length < 2 ^ (prefixWord ++ tailWord_492174).sum := by decide
  have hdescent : baseEnd_492174 < baseStart_492174 := by decide
  rcases family_descends (prefixWord ++ tailWord_492174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492188 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_492188 : Nat := 118140960795 + 492188 * 2 ^ 59
def prefixEnd_492188 : Nat := 4983230072969 + 3 ^ 40 * 492188 * 2
def baseEnd_492188 : Nat := 252729016375225545886475

theorem tailTrace_492188 : CollatzResearch.WordTrace tailWord_492188 prefixEnd_492188 252729016375225545886475 := by
  unfold tailWord_492188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975785570447204931614609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11967714093929606575486145 8975785570447204931614609)
  ·
    refine ⟨6731839177835403698710957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8975785570447204931614609 6731839177835403698710957)
    ·
      refine ⟨2524439691688276387016609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6731839177835403698710957 2524439691688276387016609)
      ·
        refine ⟨1893329768766207290262457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524439691688276387016609 1893329768766207290262457)
        ·
          refine ⟨1419997326574655467696843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893329768766207290262457 1419997326574655467696843)
          ·
            refine ⟨2129995989861983201545265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419997326574655467696843 2129995989861983201545265)
            ·
              refine ⟨1597496992396487401158949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129995989861983201545265 1597496992396487401158949)
              ·
                refine ⟨299530686074341387717303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1597496992396487401158949 299530686074341387717303)
                ·
                  refine ⟨449296029111512081575955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299530686074341387717303 449296029111512081575955)
                  ·
                    refine ⟨673944043667268122363933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449296029111512081575955 673944043667268122363933)
                    ·
                      refine ⟨252729016375225545886475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 673944043667268122363933 252729016375225545886475)
                      ·
                        rfl

theorem cell23_492188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_492188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492188 prefixEnd_492188 := by exact prefixLift 492188
  have htrace : WordTrace (prefixWord ++ tailWord_492188) baseStart_492188 baseEnd_492188 := by
    simpa [prefixWord, tailWord_492188, baseEnd_492188] using wordTrace_append hprefix tailTrace_492188
  have hstable : (prefixWord ++ tailWord_492188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492188).length < 2 ^ (prefixWord ++ tailWord_492188).sum := by decide
  have hdescent : baseEnd_492188 < baseStart_492188 := by decide
  rcases family_descends (prefixWord ++ tailWord_492188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492207 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_492207 : Nat := 118140960795 + 492207 * 2 ^ 59
def prefixEnd_492207 : Nat := 4983230072969 + 3 ^ 40 * 492207 * 2
def baseEnd_492207 : Nat := 252738772507660971548887

theorem tailTrace_492207 : CollatzResearch.WordTrace tailWord_492207 prefixEnd_492207 252738772507660971548887 := by
  unfold tailWord_492207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952264127825576108170875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11968176085217050738780583 17952264127825576108170875)
  ·
    refine ⟨26928396191738364162256313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17952264127825576108170875 26928396191738364162256313)
    ·
      refine ⟨20196297143803773121692235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26928396191738364162256313 20196297143803773121692235)
      ·
        refine ⟨30294445715705659682538353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196297143803773121692235 30294445715705659682538353)
        ·
          refine ⟨22720834286779244761903765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30294445715705659682538353 22720834286779244761903765)
          ·
            refine ⟨1065039107192777098214239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22720834286779244761903765 1065039107192777098214239)
            ·
              refine ⟨1597558660789165647321359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065039107192777098214239 1597558660789165647321359)
              ·
                refine ⟨2396337991183748470982039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597558660789165647321359 2396337991183748470982039)
                ·
                  refine ⟨3594506986775622706473059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396337991183748470982039 3594506986775622706473059)
                  ·
                    refine ⟨5391760480163434059709589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3594506986775622706473059 5391760480163434059709589)
                    ·
                      refine ⟨252738772507660971548887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5391760480163434059709589 252738772507660971548887)
                      ·
                        rfl

theorem cell23_492207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_492207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492207 prefixEnd_492207 := by exact prefixLift 492207
  have htrace : WordTrace (prefixWord ++ tailWord_492207) baseStart_492207 baseEnd_492207 := by
    simpa [prefixWord, tailWord_492207, baseEnd_492207] using wordTrace_append hprefix tailTrace_492207
  have hstable : (prefixWord ++ tailWord_492207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492207).length < 2 ^ (prefixWord ++ tailWord_492207).sum := by decide
  have hdescent : baseEnd_492207 < baseStart_492207 := by decide
  rcases family_descends (prefixWord ++ tailWord_492207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492211 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 3, 2, 2]
def baseStart_492211 : Nat := 118140960795 + 492211 * 2 ^ 59
def prefixEnd_492211 : Nat := 4983230072969 + 3 ^ 40 * 492211 * 2
def baseEnd_492211 : Nat := 252740826430278955898869

theorem tailTrace_492211 : CollatzResearch.WordTrace tailWord_492211 prefixEnd_492211 252740826430278955898869 := by
  unfold tailWord_492211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952410019811084791316487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11968273346540723194210991 17952410019811084791316487)
  ·
    refine ⟨26928615029716627186974731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17952410019811084791316487 26928615029716627186974731)
    ·
      refine ⟨40392922544574940780462097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26928615029716627186974731 40392922544574940780462097)
      ·
        refine ⟨30294691908431205585346573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40392922544574940780462097 30294691908431205585346573)
        ·
          refine ⟨11360509465661702094504965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30294691908431205585346573 11360509465661702094504965)
          ·
            refine ⟨2130095524811569142719681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11360509465661702094504965 2130095524811569142719681)
            ·
              refine ⟨1597571643608676857039761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130095524811569142719681 1597571643608676857039761)
              ·
                refine ⟨1198178732706507642779821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597571643608676857039761 1198178732706507642779821)
                ·
                  refine ⟨449317024764940366042433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198178732706507642779821 449317024764940366042433)
                  ·
                    refine ⟨336987768573705274531825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449317024764940366042433 336987768573705274531825)
                    ·
                      refine ⟨252740826430278955898869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 336987768573705274531825 252740826430278955898869)
                      ·
                        rfl

theorem cell23_492211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2, 2].length) (baseStart_492211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492211 prefixEnd_492211 := by exact prefixLift 492211
  have htrace : WordTrace (prefixWord ++ tailWord_492211) baseStart_492211 baseEnd_492211 := by
    simpa [prefixWord, tailWord_492211, baseEnd_492211] using wordTrace_append hprefix tailTrace_492211
  have hstable : (prefixWord ++ tailWord_492211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492211).length < 2 ^ (prefixWord ++ tailWord_492211).sum := by decide
  have hdescent : baseEnd_492211 < baseStart_492211 := by decide
  rcases family_descends (prefixWord ++ tailWord_492211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492271 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 3, 3, 2]
def baseStart_492271 : Nat := 118140960795 + 492271 * 2 ^ 59
def prefixEnd_492271 : Nat := 4983230072969 + 3 ^ 40 * 492271 * 2
def baseEnd_492271 : Nat := 252771635269548721148593

theorem tailTrace_492271 : CollatzResearch.WordTrace tailWord_492271 prefixEnd_492271 252771635269548721148593 := by
  unfold tailWord_492271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954598399593715038500667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11969732266395810025667111 17954598399593715038500667)
  ·
    refine ⟨26931897599390572557751001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17954598399593715038500667 26931897599390572557751001)
    ·
      refine ⟨20198923199542929418313251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26931897599390572557751001 20198923199542929418313251)
      ·
        refine ⟨30298384799314394127469877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20198923199542929418313251 30298384799314394127469877)
        ·
          refine ⟨2840473574935724449450301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30298384799314394127469877 2840473574935724449450301)
          ·
            refine ⟨1065177590600896668543863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2840473574935724449450301 1065177590600896668543863)
            ·
              refine ⟨1597766385901345002815795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065177590600896668543863 1597766385901345002815795)
              ·
                refine ⟨2396649578852017504223693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597766385901345002815795 2396649578852017504223693)
                ·
                  refine ⟨898743592069506564083885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2396649578852017504223693 898743592069506564083885)
                  ·
                    refine ⟨337028847026064961531457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898743592069506564083885 337028847026064961531457)
                    ·
                      refine ⟨252771635269548721148593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337028847026064961531457 252771635269548721148593)
                      ·
                        rfl

theorem cell23_492271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3, 2].length) (baseStart_492271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492271 prefixEnd_492271 := by exact prefixLift 492271
  have htrace : WordTrace (prefixWord ++ tailWord_492271) baseStart_492271 baseEnd_492271 := by
    simpa [prefixWord, tailWord_492271, baseEnd_492271] using wordTrace_append hprefix tailTrace_492271
  have hstable : (prefixWord ++ tailWord_492271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492271).length < 2 ^ (prefixWord ++ tailWord_492271).sum := by decide
  have hdescent : baseEnd_492271 < baseStart_492271 := by decide
  rcases family_descends (prefixWord ++ tailWord_492271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492307 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 7]
def baseStart_492307 : Nat := 118140960795 + 492307 * 2 ^ 59
def prefixEnd_492307 : Nat := 4983230072969 + 3 ^ 40 * 492307 * 2
def baseEnd_492307 : Nat := 28087791174790064477603

theorem tailTrace_492307 : CollatzResearch.WordTrace tailWord_492307 prefixEnd_492307 28087791174790064477603 := by
  unfold tailWord_492307
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955911427463293186811175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11970607618308862124540783 17955911427463293186811175)
  ·
    refine ⟨26933867141194939780216763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955911427463293186811175 26933867141194939780216763)
    ·
      refine ⟨40400800711792409670325145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933867141194939780216763 40400800711792409670325145)
      ·
        refine ⟨30300600533844307252743859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40400800711792409670325145 30300600533844307252743859)
        ·
          refine ⟨45450900800766460879115789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30300600533844307252743859 45450900800766460879115789)
          ·
            refine ⟨17044087800287422829668421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45450900800766460879115789 17044087800287422829668421)
            ·
              refine ⟨3195766462553891780562829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17044087800287422829668421 3195766462553891780562829)
              ·
                refine ⟨1198412423457709417711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195766462553891780562829 1198412423457709417711061)
                ·
                  refine ⟨28087791174790064477603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1198412423457709417711061 28087791174790064477603)
                  ·
                    rfl

theorem cell23_492307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 7].length) (baseStart_492307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492307 prefixEnd_492307 := by exact prefixLift 492307
  have htrace : WordTrace (prefixWord ++ tailWord_492307) baseStart_492307 baseEnd_492307 := by
    simpa [prefixWord, tailWord_492307, baseEnd_492307] using wordTrace_append hprefix tailTrace_492307
  have hstable : (prefixWord ++ tailWord_492307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492307).length < 2 ^ (prefixWord ++ tailWord_492307).sum := by decide
  have hdescent : baseEnd_492307 < baseStart_492307 := by decide
  rcases family_descends (prefixWord ++ tailWord_492307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492314 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_492314 : Nat := 118140960795 + 492314 * 2 ^ 59
def prefixEnd_492314 : Nat := 4983230072969 + 3 ^ 40 * 492314 * 2
def baseEnd_492314 : Nat := 252793714937692052910895

theorem tailTrace_492314 : CollatzResearch.WordTrace tailWord_492314 prefixEnd_492314 252793714937692052910895 := by
  unfold tailWord_492314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489041684609483345578999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11970777825625288921543997 4489041684609483345578999)
  ·
    refine ⟨6733562526914225018368499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4489041684609483345578999 6733562526914225018368499)
    ·
      refine ⟨10100343790371337527552749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6733562526914225018368499 10100343790371337527552749)
      ·
        refine ⟨3787628921389251572832281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10100343790371337527552749 3787628921389251572832281)
        ·
          refine ⟨2840721691041938679624211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787628921389251572832281 2840721691041938679624211)
          ·
            refine ⟨4261082536562908019436317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840721691041938679624211 4261082536562908019436317)
            ·
              refine ⟨1597905951211090507288619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4261082536562908019436317 1597905951211090507288619)
              ·
                refine ⟨2396858926816635760932929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597905951211090507288619 2396858926816635760932929)
                ·
                  refine ⟨1797644195112476820699697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396858926816635760932929 1797644195112476820699697)
                  ·
                    refine ⟨1348233146334357615524773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797644195112476820699697 1348233146334357615524773)
                    ·
                      refine ⟨252793714937692052910895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1348233146334357615524773 252793714937692052910895)
                      ·
                        rfl

theorem cell23_492314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_492314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492314 prefixEnd_492314 := by exact prefixLift 492314
  have htrace : WordTrace (prefixWord ++ tailWord_492314) baseStart_492314 baseEnd_492314 := by
    simpa [prefixWord, tailWord_492314, baseEnd_492314] using wordTrace_append hprefix tailTrace_492314
  have hstable : (prefixWord ++ tailWord_492314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492314).length < 2 ^ (prefixWord ++ tailWord_492314).sum := by decide
  have hdescent : baseEnd_492314 < baseStart_492314 := by decide
  rcases family_descends (prefixWord ++ tailWord_492314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492341 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 5]
def baseStart_492341 : Nat := 118140960795 + 492341 * 2 ^ 59
def prefixEnd_492341 : Nat := 4983230072969 + 3 ^ 40 * 492341 * 2
def baseEnd_492341 : Nat := 28089730990595938585919

theorem tailTrace_492341 : CollatzResearch.WordTrace tailWord_492341 prefixEnd_492341 28089730990595938585919 := by
  unfold tailWord_492341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957151509340116993548877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971434339560077995699251 17957151509340116993548877)
  ·
    refine ⟨6733931816002543872580829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17957151509340116993548877 6733931816002543872580829)
    ·
      refine ⟨2525224431000953952217811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6733931816002543872580829 2525224431000953952217811)
      ·
        refine ⟨3787836646501430928326717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525224431000953952217811 3787836646501430928326717)
        ·
          refine ⟨1420438742438036598122519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3787836646501430928326717 1420438742438036598122519)
          ·
            refine ⟨2130658113657054897183779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420438742438036598122519 2130658113657054897183779)
            ·
              refine ⟨3195987170485582345775669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130658113657054897183779 3195987170485582345775669)
              ·
                refine ⟨299623797233023344916469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3195987170485582345775669 299623797233023344916469)
                ·
                  refine ⟨28089730990595938585919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299623797233023344916469 28089730990595938585919)
                  ·
                    rfl

theorem cell23_492341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_492341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492341 prefixEnd_492341 := by exact prefixLift 492341
  have htrace : WordTrace (prefixWord ++ tailWord_492341) baseStart_492341 baseEnd_492341 := by
    simpa [prefixWord, tailWord_492341, baseEnd_492341] using wordTrace_append hprefix tailTrace_492341
  have hstable : (prefixWord ++ tailWord_492341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492341).length < 2 ^ (prefixWord ++ tailWord_492341).sum := by decide
  have hdescent : baseEnd_492341 < baseStart_492341 := by decide
  rcases family_descends (prefixWord ++ tailWord_492341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492441 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_492441 : Nat := 118140960795 + 492441 * 2 ^ 59
def prefixEnd_492441 : Nat := 4983230072969 + 3 ^ 40 * 492441 * 2
def baseEnd_492441 : Nat := 252858926980813056022811

theorem tailTrace_492441 : CollatzResearch.WordTrace tailWord_492441 prefixEnd_492441 252858926980813056022811 := by
  unfold tailWord_492441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960798808977834072189177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11973865872651889381459451 17960798808977834072189177)
  ·
    refine ⟨13470599106733375554141883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17960798808977834072189177 13470599106733375554141883)
    ·
      refine ⟨20205898660100063331212825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13470599106733375554141883 20205898660100063331212825)
      ·
        refine ⟨15154423995075047498409619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20205898660100063331212825 15154423995075047498409619)
        ·
          refine ⟨22731635992612571247614429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154423995075047498409619 22731635992612571247614429)
          ·
            refine ⟨8524363497229714217855411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22731635992612571247614429 8524363497229714217855411)
            ·
              refine ⟨12786545245844571326783117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524363497229714217855411 12786545245844571326783117)
              ·
                refine ⟨4794954467191714247543669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12786545245844571326783117 4794954467191714247543669)
                ·
                  refine ⟨449526981299223210707219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794954467191714247543669 449526981299223210707219)
                  ·
                    refine ⟨674290471948834816060829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449526981299223210707219 674290471948834816060829)
                    ·
                      refine ⟨252858926980813056022811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 674290471948834816060829 252858926980813056022811)
                      ·
                        rfl

theorem cell23_492441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_492441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492441 prefixEnd_492441 := by exact prefixLift 492441
  have htrace : WordTrace (prefixWord ++ tailWord_492441) baseStart_492441 baseEnd_492441 := by
    simpa [prefixWord, tailWord_492441, baseEnd_492441] using wordTrace_append hprefix tailTrace_492441
  have hstable : (prefixWord ++ tailWord_492441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492441).length < 2 ^ (prefixWord ++ tailWord_492441).sum := by decide
  have hdescent : baseEnd_492441 < baseStart_492441 := by decide
  rcases family_descends (prefixWord ++ tailWord_492441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492451 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 5, 2]
def baseStart_492451 : Nat := 118140960795 + 492451 * 2 ^ 59
def prefixEnd_492451 : Nat := 4983230072969 + 3 ^ 40 * 492451 * 2
def baseEnd_492451 : Nat := 252864061787358016897765

theorem tailTrace_492451 : CollatzResearch.WordTrace tailWord_492451 prefixEnd_492451 252864061787358016897765 := by
  unfold tailWord_492451
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961163538941605780053207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974109025961070520035471 17961163538941605780053207)
  ·
    refine ⟨26941745308412408670079811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17961163538941605780053207 26941745308412408670079811)
    ·
      refine ⟨40412617962618613005119717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941745308412408670079811 40412617962618613005119717)
      ·
        refine ⟨7577365867990989938459947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40412617962618613005119717 7577365867990989938459947)
        ·
          refine ⟨11366048801986484907689921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577365867990989938459947 11366048801986484907689921)
          ·
            refine ⟨8524536601489863680767441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11366048801986484907689921 8524536601489863680767441)
            ·
              refine ⟨6393402451117397760575581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8524536601489863680767441 6393402451117397760575581)
              ·
                refine ⟨2397525919169024160215843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6393402451117397760575581 2397525919169024160215843)
                ·
                  refine ⟨3596288878753536240323765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397525919169024160215843 3596288878753536240323765)
                  ·
                    refine ⟨337152082383144022530353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3596288878753536240323765 337152082383144022530353)
                    ·
                      refine ⟨252864061787358016897765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337152082383144022530353 252864061787358016897765)
                      ·
                        rfl

theorem cell23_492451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_492451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492451 prefixEnd_492451 := by exact prefixLift 492451
  have htrace : WordTrace (prefixWord ++ tailWord_492451) baseStart_492451 baseEnd_492451 := by
    simpa [prefixWord, tailWord_492451, baseEnd_492451] using wordTrace_append hprefix tailTrace_492451
  have hstable : (prefixWord ++ tailWord_492451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492451).length < 2 ^ (prefixWord ++ tailWord_492451).sum := by decide
  have hdescent : baseEnd_492451 < baseStart_492451 := by decide
  rcases family_descends (prefixWord ++ tailWord_492451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492474 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_492474 : Nat := 118140960795 + 492474 * 2 ^ 59
def prefixEnd_492474 : Nat := 4983230072969 + 3 ^ 40 * 492474 * 2
def baseEnd_492474 : Nat := 84291957280803808970053

theorem tailTrace_492474 : CollatzResearch.WordTrace tailWord_492474 prefixEnd_492474 84291957280803808970053 := by
  unfold tailWord_492474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490500604464570177035119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11974668278572187138760317 4490500604464570177035119)
  ·
    refine ⟨6735750906696855265552679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490500604464570177035119 6735750906696855265552679)
    ·
      refine ⟨10103626360045282898329019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735750906696855265552679 10103626360045282898329019)
      ·
        refine ⟨15155439540067924347493529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103626360045282898329019 15155439540067924347493529)
        ·
          refine ⟨11366579655050943260620147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155439540067924347493529 11366579655050943260620147)
          ·
            refine ⟨17049869482576414890930221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366579655050943260620147 17049869482576414890930221)
            ·
              refine ⟨6393701055966155584098833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17049869482576414890930221 6393701055966155584098833)
              ·
                refine ⟨4795275791974616688074125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393701055966155584098833 4795275791974616688074125)
                ·
                  refine ⟨1798228421990481258027797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4795275791974616688074125 1798228421990481258027797)
                  ·
                    refine ⟨84291957280803808970053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1798228421990481258027797 84291957280803808970053)
                    ·
                      rfl

theorem cell23_492474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_492474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492474 prefixEnd_492474 := by exact prefixLift 492474
  have htrace : WordTrace (prefixWord ++ tailWord_492474) baseStart_492474 baseEnd_492474 := by
    simpa [prefixWord, tailWord_492474, baseEnd_492474] using wordTrace_append hprefix tailTrace_492474
  have hstable : (prefixWord ++ tailWord_492474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492474).length < 2 ^ (prefixWord ++ tailWord_492474).sum := by decide
  have hdescent : baseEnd_492474 < baseStart_492474 := by decide
  rcases family_descends (prefixWord ++ tailWord_492474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492491 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 6]
def baseStart_492491 : Nat := 118140960795 + 492491 * 2 ^ 59
def prefixEnd_492491 : Nat := 4983230072969 + 3 ^ 40 * 492491 * 2
def baseEnd_492491 : Nat := 84294867004512620132527

theorem tailTrace_492491 : CollatzResearch.WordTrace tailWord_492491 prefixEnd_492491 84294867004512620132527 := by
  unfold tailWord_492491
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962622458796692611509327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11975081639197795074339551 17962622458796692611509327)
  ·
    refine ⟨26943933688195038917263991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17962622458796692611509327 26943933688195038917263991)
    ·
      refine ⟨40415900532292558375895987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26943933688195038917263991 40415900532292558375895987)
      ·
        refine ⟨60623850798438837563843981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40415900532292558375895987 60623850798438837563843981)
        ·
          refine ⟨22733944049414564086441493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60623850798438837563843981 22733944049414564086441493)
          ·
            refine ⟨1065653627316307691551945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22733944049414564086441493 1065653627316307691551945)
            ·
              refine ⟨799240220487230768663959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065653627316307691551945 799240220487230768663959)
              ·
                refine ⟨1198860330730846152995939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799240220487230768663959 1198860330730846152995939)
                ·
                  refine ⟨1798290496096269229493909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198860330730846152995939 1798290496096269229493909)
                  ·
                    refine ⟨84294867004512620132527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1798290496096269229493909 84294867004512620132527)
                    ·
                      rfl

theorem cell23_492491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].length) (baseStart_492491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492491 prefixEnd_492491 := by exact prefixLift 492491
  have htrace : WordTrace (prefixWord ++ tailWord_492491) baseStart_492491 baseEnd_492491 := by
    simpa [prefixWord, tailWord_492491, baseEnd_492491] using wordTrace_append hprefix tailTrace_492491
  have hstable : (prefixWord ++ tailWord_492491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492491).length < 2 ^ (prefixWord ++ tailWord_492491).sum := by decide
  have hdescent : baseEnd_492491 < baseStart_492491 := by decide
  rcases family_descends (prefixWord ++ tailWord_492491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492498 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_492498 : Nat := 118140960795 + 492498 * 2 ^ 59
def prefixEnd_492498 : Nat := 4983230072969 + 3 ^ 40 * 492498 * 2
def baseEnd_492498 : Nat := 252888195378119333010049

theorem tailTrace_492498 : CollatzResearch.WordTrace tailWord_492498 prefixEnd_492498 252888195378119333010049 := by
  unfold tailWord_492498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490719442442833201753537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11975251846514221871342765 4490719442442833201753537)
  ·
    refine ⟨3368039581832124901315153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4490719442442833201753537 3368039581832124901315153)
    ·
      refine ⟨2526029686374093675986365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3368039581832124901315153 2526029686374093675986365)
      ·
        refine ⟨947261132390285128494887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2526029686374093675986365 947261132390285128494887)
        ·
          refine ⟨1420891698585427692742331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947261132390285128494887 1420891698585427692742331)
          ·
            refine ⟨2131337547878141539113497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420891698585427692742331 2131337547878141539113497)
            ·
              refine ⟨1598503160908606154335123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131337547878141539113497 1598503160908606154335123)
              ·
                refine ⟨2397754741362909231502685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598503160908606154335123 2397754741362909231502685)
                ·
                  refine ⟨899158028011090961813507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2397754741362909231502685 899158028011090961813507)
                  ·
                    refine ⟨1348737042016636442720261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 899158028011090961813507 1348737042016636442720261)
                    ·
                      refine ⟨252888195378119333010049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1348737042016636442720261 252888195378119333010049)
                      ·
                        rfl

theorem cell23_492498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_492498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492498 prefixEnd_492498 := by exact prefixLift 492498
  have htrace : WordTrace (prefixWord ++ tailWord_492498) baseStart_492498 baseEnd_492498 := by
    simpa [prefixWord, tailWord_492498, baseEnd_492498] using wordTrace_append hprefix tailTrace_492498
  have hstable : (prefixWord ++ tailWord_492498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492498).length < 2 ^ (prefixWord ++ tailWord_492498).sum := by decide
  have hdescent : baseEnd_492498 < baseStart_492498 := by decide
  rcases family_descends (prefixWord ++ tailWord_492498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492502 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_492502 : Nat := 118140960795 + 492502 * 2 ^ 59
def prefixEnd_492502 : Nat := 4983230072969 + 3 ^ 40 * 492502 * 2
def baseEnd_492502 : Nat := 252890249300737317360031

theorem tailTrace_492502 : CollatzResearch.WordTrace tailWord_492502 prefixEnd_492502 252890249300737317360031 := by
  unfold tailWord_492502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122688978859802593134985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11975349107837894326773173 1122688978859802593134985)
  ·
    refine ⟨842016734144851944851239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1122688978859802593134985 842016734144851944851239)
    ·
      refine ⟨1263025101217277917276859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842016734144851944851239 1263025101217277917276859)
      ·
        refine ⟨1894537651825916875915289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263025101217277917276859 1894537651825916875915289)
        ·
          refine ⟨1420903238869437656936467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894537651825916875915289 1420903238869437656936467)
          ·
            refine ⟨2131354858304156485404701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420903238869437656936467 2131354858304156485404701)
            ·
              refine ⟨799258071864058682026763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2131354858304156485404701 799258071864058682026763)
              ·
                refine ⟨1198887107796088023040145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799258071864058682026763 1198887107796088023040145)
                ·
                  refine ⟨899165330847066017280109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198887107796088023040145 899165330847066017280109)
                  ·
                    refine ⟨337186999067649756480041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899165330847066017280109 337186999067649756480041)
                    ·
                      refine ⟨252890249300737317360031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337186999067649756480041 252890249300737317360031)
                      ·
                        rfl

theorem cell23_492502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_492502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492502 prefixEnd_492502 := by exact prefixLift 492502
  have htrace : WordTrace (prefixWord ++ tailWord_492502) baseStart_492502 baseEnd_492502 := by
    simpa [prefixWord, tailWord_492502, baseEnd_492502] using wordTrace_append hprefix tailTrace_492502
  have hstable : (prefixWord ++ tailWord_492502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492502).length < 2 ^ (prefixWord ++ tailWord_492502).sum := by decide
  have hdescent : baseEnd_492502 < baseStart_492502 := by decide
  rcases family_descends (prefixWord ++ tailWord_492502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492524 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_492524 : Nat := 118140960795 + 492524 * 2 ^ 59
def prefixEnd_492524 : Nat := 4983230072969 + 3 ^ 40 * 492524 * 2
def baseEnd_492524 : Nat := 252901545875136231284929

theorem tailTrace_492524 : CollatzResearch.WordTrace tailWord_492524 prefixEnd_492524 252901545875136231284929 := by
  unfold tailWord_492524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981913033838569623730313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11975884045118092831640417 8981913033838569623730313)
  ·
    refine ⟨6736434775378927217797735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8981913033838569623730313 6736434775378927217797735)
    ·
      refine ⟨10104652163068390826696603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736434775378927217797735 10104652163068390826696603)
      ·
        refine ⟨15156978244602586240044905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104652163068390826696603 15156978244602586240044905)
        ·
          refine ⟨11367733683451939680033679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15156978244602586240044905 11367733683451939680033679)
          ·
            refine ⟨17051600525177909520050519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367733683451939680033679 17051600525177909520050519)
            ·
              refine ⟨25577400787766864280075779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051600525177909520050519 25577400787766864280075779)
              ·
                refine ⟨38366101181650296420113669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25577400787766864280075779 38366101181650296420113669)
                ·
                  refine ⟨7193643971559430578771313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38366101181650296420113669 7193643971559430578771313)
                  ·
                    refine ⟨5395232978669572934078485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7193643971559430578771313 5395232978669572934078485)
                    ·
                      refine ⟨252901545875136231284929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5395232978669572934078485 252901545875136231284929)
                      ·
                        rfl

theorem cell23_492524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_492524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492524 prefixEnd_492524 := by exact prefixLift 492524
  have htrace : WordTrace (prefixWord ++ tailWord_492524) baseStart_492524 baseEnd_492524 := by
    simpa [prefixWord, tailWord_492524, baseEnd_492524] using wordTrace_append hprefix tailTrace_492524
  have hstable : (prefixWord ++ tailWord_492524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492524).length < 2 ^ (prefixWord ++ tailWord_492524).sum := by decide
  have hdescent : baseEnd_492524 < baseStart_492524 := by decide
  rcases family_descends (prefixWord ++ tailWord_492524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492542 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_492542 : Nat := 118140960795 + 492542 * 2 ^ 59
def prefixEnd_492542 : Nat := 4983230072969 + 3 ^ 40 * 492542 * 2
def baseEnd_492542 : Nat := 84303596175639053619949

theorem tailTrace_492542 : CollatzResearch.WordTrace tailWord_492542 prefixEnd_492542 84303596175639053619949 := by
  unfold tailWord_492542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245560322701491040201985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11976321721074618881077253 2245560322701491040201985)
  ·
    refine ⟨1684170242026118280151489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2245560322701491040201985 1684170242026118280151489)
    ·
      refine ⟨1263127681519588710113617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1684170242026118280151489 1263127681519588710113617)
      ·
        refine ⟨947345761139691532585213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263127681519588710113617 947345761139691532585213)
        ·
          refine ⟨355254660427384324719455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947345761139691532585213 355254660427384324719455)
          ·
            refine ⟨532881990641076487079183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355254660427384324719455 532881990641076487079183)
            ·
              refine ⟨799322985961614730618775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532881990641076487079183 799322985961614730618775)
              ·
                refine ⟨1198984478942422095928163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799322985961614730618775 1198984478942422095928163)
                ·
                  refine ⟨1798476718413633143892245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198984478942422095928163 1798476718413633143892245)
                  ·
                    refine ⟨84303596175639053619949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1798476718413633143892245 84303596175639053619949)
                    ·
                      rfl

theorem cell23_492542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_492542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492542 prefixEnd_492542 := by exact prefixLift 492542
  have htrace : WordTrace (prefixWord ++ tailWord_492542) baseStart_492542 baseEnd_492542 := by
    simpa [prefixWord, tailWord_492542, baseEnd_492542] using wordTrace_append hprefix tailTrace_492542
  have hstable : (prefixWord ++ tailWord_492542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492542).length < 2 ^ (prefixWord ++ tailWord_492542).sum := by decide
  have hdescent : baseEnd_492542 < baseStart_492542 := by decide
  rcases family_descends (prefixWord ++ tailWord_492542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492575 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 1, 3, 2]
def baseStart_492575 : Nat := 118140960795 + 492575 * 2 ^ 59
def prefixEnd_492575 : Nat := 4983230072969 + 3 ^ 40 * 492575 * 2
def baseEnd_492575 : Nat := 252927733388515531747195

theorem tailTrace_492575 : CollatzResearch.WordTrace tailWord_492575 prefixEnd_492575 252927733388515531747195 := by
  unfold tailWord_492575
  simp only [CollatzResearch.WordTrace]
  refine ⟨17965686190492374957567179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11977124126994916638378119 17965686190492374957567179)
  ·
    refine ⟨26948529285738562436350769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17965686190492374957567179 26948529285738562436350769)
    ·
      refine ⟨20211396964303921827263077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26948529285738562436350769 20211396964303921827263077)
      ·
        refine ⟨3789636930806985342611827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20211396964303921827263077 3789636930806985342611827)
        ·
          refine ⟨5684455396210478013917741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789636930806985342611827 5684455396210478013917741)
          ·
            refine ⟨2131670773578929255219153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5684455396210478013917741 2131670773578929255219153)
            ·
              refine ⟨1598753080184196941414365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131670773578929255219153 1598753080184196941414365)
              ·
                refine ⟨599532405069073853030387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598753080184196941414365 599532405069073853030387)
                ·
                  refine ⟨899298607603610779545581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599532405069073853030387 899298607603610779545581)
                  ·
                    refine ⟨337236977851354042329593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899298607603610779545581 337236977851354042329593)
                    ·
                      refine ⟨252927733388515531747195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337236977851354042329593 252927733388515531747195)
                      ·
                        rfl

theorem cell23_492575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_492575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492575 prefixEnd_492575 := by exact prefixLift 492575
  have htrace : WordTrace (prefixWord ++ tailWord_492575) baseStart_492575 baseEnd_492575 := by
    simpa [prefixWord, tailWord_492575, baseEnd_492575] using wordTrace_append hprefix tailTrace_492575
  have hstable : (prefixWord ++ tailWord_492575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492575).length < 2 ^ (prefixWord ++ tailWord_492575).sum := by decide
  have hdescent : baseEnd_492575 < baseStart_492575 := by decide
  rcases family_descends (prefixWord ++ tailWord_492575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492609 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_492609 : Nat := 118140960795 + 492609 * 2 ^ 59
def prefixEnd_492609 : Nat := 4983230072969 + 3 ^ 40 * 492609 * 2
def baseEnd_492609 : Nat := 252945191730768398722039

theorem tailTrace_492609 : CollatzResearch.WordTrace tailWord_492609 prefixEnd_492609 252945191730768398722039 := by
  unfold tailWord_492609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966926272369198764304881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11977950848246132509536587 17966926272369198764304881)
  ·
    refine ⟨13475194704276899073228661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17966926272369198764304881 13475194704276899073228661)
    ·
      refine ⟨1263299503525959288115187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13475194704276899073228661 1263299503525959288115187)
      ·
        refine ⟨1894949255288938932172781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263299503525959288115187 1894949255288938932172781)
        ·
          refine ⟨710605970733352099564793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894949255288938932172781 710605970733352099564793)
          ·
            refine ⟨532954478050014074673595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710605970733352099564793 532954478050014074673595)
            ·
              refine ⟨799431717075021112010393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532954478050014074673595 799431717075021112010393)
              ·
                refine ⟨599573787806265834007795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799431717075021112010393 599573787806265834007795)
                ·
                  refine ⟨899360681709398751011693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599573787806265834007795 899360681709398751011693)
                  ·
                    refine ⟨337260255641024531629385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899360681709398751011693 337260255641024531629385)
                    ·
                      refine ⟨252945191730768398722039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337260255641024531629385 252945191730768398722039)
                      ·
                        rfl

theorem cell23_492609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_492609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492609 prefixEnd_492609 := by exact prefixLift 492609
  have htrace : WordTrace (prefixWord ++ tailWord_492609) baseStart_492609 baseEnd_492609 := by
    simpa [prefixWord, tailWord_492609, baseEnd_492609] using wordTrace_append hprefix tailTrace_492609
  have hstable : (prefixWord ++ tailWord_492609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492609).length < 2 ^ (prefixWord ++ tailWord_492609).sum := by decide
  have hdescent : baseEnd_492609 < baseStart_492609 := by decide
  rcases family_descends (prefixWord ++ tailWord_492609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492691 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_492691 : Nat := 118140960795 + 492691 * 2 ^ 59
def prefixEnd_492691 : Nat := 4983230072969 + 3 ^ 40 * 492691 * 2
def baseEnd_492691 : Nat := 252987297144437077896661

theorem tailTrace_492691 : CollatzResearch.WordTrace tailWord_492691 prefixEnd_492691 252987297144437077896661 := by
  unfold tailWord_492691
  simp only [CollatzResearch.WordTrace]
  refine ⟨17969917058072126768789927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11979944705381417845859951 17969917058072126768789927)
  ·
    refine ⟨26954875587108190153184891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17969917058072126768789927 26954875587108190153184891)
    ·
      refine ⟨40432313380662285229777337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26954875587108190153184891 40432313380662285229777337)
      ·
        refine ⟨30324235035496713922333003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40432313380662285229777337 30324235035496713922333003)
        ·
          refine ⟨45486352553245070883499505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30324235035496713922333003 45486352553245070883499505)
          ·
            refine ⟨34114764414933803162624629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45486352553245070883499505 34114764414933803162624629)
            ·
              refine ⟨3198259163900044046496059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34114764414933803162624629 3198259163900044046496059)
              ·
                refine ⟨4797388745850066069744089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198259163900044046496059 4797388745850066069744089)
                ·
                  refine ⟨3598041559387549552308067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797388745850066069744089 3598041559387549552308067)
                  ·
                    refine ⟨5397062339081324328462101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598041559387549552308067 5397062339081324328462101)
                    ·
                      refine ⟨252987297144437077896661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5397062339081324328462101 252987297144437077896661)
                      ·
                        rfl

theorem cell23_492691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_492691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492691 prefixEnd_492691 := by exact prefixLift 492691
  have htrace : WordTrace (prefixWord ++ tailWord_492691) baseStart_492691 baseEnd_492691 := by
    simpa [prefixWord, tailWord_492691, baseEnd_492691] using wordTrace_append hprefix tailTrace_492691
  have hstable : (prefixWord ++ tailWord_492691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492691).length < 2 ^ (prefixWord ++ tailWord_492691).sum := by decide
  have hdescent : baseEnd_492691 < baseStart_492691 := by decide
  rcases family_descends (prefixWord ++ tailWord_492691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492695 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_492695 : Nat := 118140960795 + 492695 * 2 ^ 59
def prefixEnd_492695 : Nat := 4983230072969 + 3 ^ 40 * 492695 * 2
def baseEnd_492695 : Nat := 252989351067055062246643

theorem tailTrace_492695 : CollatzResearch.WordTrace tailWord_492695 prefixEnd_492695 252989351067055062246643 := by
  unfold tailWord_492695
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970062950057635451935539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11980041966705090301290359 17970062950057635451935539)
  ·
    refine ⟨26955094425086453177903309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17970062950057635451935539 26955094425086453177903309)
    ·
      refine ⟨10108160409407419941713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26955094425086453177903309 10108160409407419941713741)
      ·
        refine ⟨3790560153527782478142653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10108160409407419941713741 3790560153527782478142653)
        ·
          refine ⟨1421460057572918429303495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3790560153527782478142653 1421460057572918429303495)
          ·
            refine ⟨2132190086359377643955243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421460057572918429303495 2132190086359377643955243)
            ·
              refine ⟨3198285129539066465932865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132190086359377643955243 3198285129539066465932865)
              ·
                refine ⟨2398713847154299849449649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198285129539066465932865 2398713847154299849449649)
                ·
                  refine ⟨1799035385365724887087237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398713847154299849449649 1799035385365724887087237)
                  ·
                    refine ⟨337319134756073416328857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799035385365724887087237 337319134756073416328857)
                    ·
                      refine ⟨252989351067055062246643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337319134756073416328857 252989351067055062246643)
                      ·
                        rfl

theorem cell23_492695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_492695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492695 prefixEnd_492695 := by exact prefixLift 492695
  have htrace : WordTrace (prefixWord ++ tailWord_492695) baseStart_492695 baseEnd_492695 := by
    simpa [prefixWord, tailWord_492695, baseEnd_492695] using wordTrace_append hprefix tailTrace_492695
  have hstable : (prefixWord ++ tailWord_492695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492695).length < 2 ^ (prefixWord ++ tailWord_492695).sum := by decide
  have hdescent : baseEnd_492695 < baseStart_492695 := by decide
  rcases family_descends (prefixWord ++ tailWord_492695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492705 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_492705 : Nat := 118140960795 + 492705 * 2 ^ 59
def prefixEnd_492705 : Nat := 4983230072969 + 3 ^ 40 * 492705 * 2
def baseEnd_492705 : Nat := 84331495291200007707199

theorem tailTrace_492705 : CollatzResearch.WordTrace tailWord_492705 prefixEnd_492705 84331495291200007707199 := by
  unfold tailWord_492705
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970427680021407159799569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11980285120014271439866379 17970427680021407159799569)
  ·
    refine ⟨13477820760016055369849677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17970427680021407159799569 13477820760016055369849677)
    ·
      refine ⟨5054182785006020763693629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13477820760016055369849677 5054182785006020763693629)
      ·
        refine ⟨1895318544377257786385111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5054182785006020763693629 1895318544377257786385111)
        ·
          refine ⟨2842977816565886679577667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895318544377257786385111 2842977816565886679577667)
          ·
            refine ⟨4264466724848830019366501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842977816565886679577667 4264466724848830019366501)
            ·
              refine ⟨799587510909155628631219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4264466724848830019366501 799587510909155628631219)
              ·
                refine ⟨1199381266363733442946829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799587510909155628631219 1199381266363733442946829)
                ·
                  refine ⟨449767974886400041105061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199381266363733442946829 449767974886400041105061)
                  ·
                    refine ⟨84331495291200007707199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449767974886400041105061 84331495291200007707199)
                    ·
                      rfl

theorem cell23_492705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_492705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492705 prefixEnd_492705 := by exact prefixLift 492705
  have htrace : WordTrace (prefixWord ++ tailWord_492705) baseStart_492705 baseEnd_492705 := by
    simpa [prefixWord, tailWord_492705, baseEnd_492705] using wordTrace_append hprefix tailTrace_492705
  have hstable : (prefixWord ++ tailWord_492705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492705).length < 2 ^ (prefixWord ++ tailWord_492705).sum := by decide
  have hdescent : baseEnd_492705 < baseStart_492705 := by decide
  rcases family_descends (prefixWord ++ tailWord_492705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 2, 3, 2]
def baseStart_492755 : Nat := 118140960795 + 492755 * 2 ^ 59
def prefixEnd_492755 : Nat := 4983230072969 + 3 ^ 40 * 492755 * 2
def baseEnd_492755 : Nat := 253020159906324827496367

theorem tailTrace_492755 : CollatzResearch.WordTrace tailWord_492755 prefixEnd_492755 253020159906324827496367 := by
  unfold tailWord_492755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972251329840265699119719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11981500886560177132746479 17972251329840265699119719)
  ·
    refine ⟨26958376994760398548679579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17972251329840265699119719 26958376994760398548679579)
    ·
      refine ⟨40437565492140597823019369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26958376994760398548679579 40437565492140597823019369)
      ·
        refine ⟨30328174119105448367264527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40437565492140597823019369 30328174119105448367264527)
        ·
          refine ⟨45492261178658172550896791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30328174119105448367264527 45492261178658172550896791)
          ·
            refine ⟨68238391767987258826345187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45492261178658172550896791 68238391767987258826345187)
            ·
              refine ⟨102357587651980888239517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68238391767987258826345187 102357587651980888239517781)
              ·
                refine ⟨1199502980296651034056849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 102357587651980888239517781 1199502980296651034056849)
                ·
                  refine ⟨899627235222488275542637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199502980296651034056849 899627235222488275542637)
                  ·
                    refine ⟨337360213208433103328489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899627235222488275542637 337360213208433103328489)
                    ·
                      refine ⟨253020159906324827496367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337360213208433103328489 253020159906324827496367)
                      ·
                        rfl

theorem cell23_492755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3, 2].length) (baseStart_492755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492755 prefixEnd_492755 := by exact prefixLift 492755
  have htrace : WordTrace (prefixWord ++ tailWord_492755) baseStart_492755 baseEnd_492755 := by
    simpa [prefixWord, tailWord_492755, baseEnd_492755] using wordTrace_append hprefix tailTrace_492755
  have hstable : (prefixWord ++ tailWord_492755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492755).length < 2 ^ (prefixWord ++ tailWord_492755).sum := by decide
  have hdescent : baseEnd_492755 < baseStart_492755 := by decide
  rcases family_descends (prefixWord ++ tailWord_492755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492756 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_492756 : Nat := 118140960795 + 492756 * 2 ^ 59
def prefixEnd_492756 : Nat := 4983230072969 + 3 ^ 40 * 492756 * 2
def baseEnd_492756 : Nat := 84340224462326441194621

theorem tailTrace_492756 : CollatzResearch.WordTrace tailWord_492756 prefixEnd_492756 84340224462326441194621 := by
  unfold tailWord_492756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986143901418321434953061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11981525201891095246604081 8986143901418321434953061)
  ·
    refine ⟨1684901981515935269053699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8986143901418321434953061 1684901981515935269053699)
    ·
      refine ⟨2527352972273902903580549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684901981515935269053699 2527352972273902903580549)
      ·
        refine ⟨473878682301356794421353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2527352972273902903580549 473878682301356794421353)
        ·
          refine ⟨355409011726017595816015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473878682301356794421353 355409011726017595816015)
          ·
            refine ⟨533113517589026393724023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355409011726017595816015 533113517589026393724023)
            ·
              refine ⟨799670276383539590586035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533113517589026393724023 799670276383539590586035)
              ·
                refine ⟨1199505414575309385879053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799670276383539590586035 1199505414575309385879053)
                ·
                  refine ⟨449814530465741019704645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199505414575309385879053 449814530465741019704645)
                  ·
                    refine ⟨84340224462326441194621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449814530465741019704645 84340224462326441194621)
                    ·
                      rfl

theorem cell23_492756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_492756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492756 prefixEnd_492756 := by exact prefixLift 492756
  have htrace : WordTrace (prefixWord ++ tailWord_492756) baseStart_492756 baseEnd_492756 := by
    simpa [prefixWord, tailWord_492756, baseEnd_492756] using wordTrace_append hprefix tailTrace_492756
  have hstable : (prefixWord ++ tailWord_492756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492756).length < 2 ^ (prefixWord ++ tailWord_492756).sum := by decide
  have hdescent : baseEnd_492756 < baseStart_492756 := by decide
  rcases family_descends (prefixWord ++ tailWord_492756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492808 : List Nat := [2, 1, 3, 2, 4, 11]
def baseStart_492808 : Nat := 118140960795 + 492808 * 2 ^ 59
def prefixEnd_492808 : Nat := 4983230072969 + 3 ^ 40 * 492808 * 2
def baseEnd_492808 : Nat := 1041347219674951111661

theorem tailTrace_492808 : CollatzResearch.WordTrace tailWord_492808 prefixEnd_492808 1041347219674951111661 := by
  unfold tailWord_492808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987092199324127875399539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11982789599098837167199385 8987092199324127875399539)
  ·
    refine ⟨13480638298986191813099309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987092199324127875399539 13480638298986191813099309)
    ·
      refine ⟨5055239362119821929912241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13480638298986191813099309 5055239362119821929912241)
      ·
        refine ⟨3791429521589866447434181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5055239362119821929912241 3791429521589866447434181)
        ·
          refine ⟨710893035298099958893909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3791429521589866447434181 710893035298099958893909)
          ·
            refine ⟨1041347219674951111661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 710893035298099958893909 1041347219674951111661)
            ·
              rfl

theorem cell23_492808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 11].length) (baseStart_492808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492808 prefixEnd_492808 := by exact prefixLift 492808
  have htrace : WordTrace (prefixWord ++ tailWord_492808) baseStart_492808 baseEnd_492808 := by
    simpa [prefixWord, tailWord_492808, baseEnd_492808] using wordTrace_append hprefix tailTrace_492808
  have hstable : (prefixWord ++ tailWord_492808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492808).length < 2 ^ (prefixWord ++ tailWord_492808).sum := by decide
  have hdescent : baseEnd_492808 < baseStart_492808 := by decide
  rcases family_descends (prefixWord ++ tailWord_492808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492812 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_492812 : Nat := 118140960795 + 492812 * 2 ^ 59
def prefixEnd_492812 : Nat := 4983230072969 + 3 ^ 40 * 492812 * 2
def baseEnd_492812 : Nat := 84349809434543701494535

theorem tailTrace_492812 : CollatzResearch.WordTrace tailWord_492812 prefixEnd_492812 84349809434543701494535 := by
  unfold tailWord_492812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987165145316882216972345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11982886860422509622629793 8987165145316882216972345)
  ·
    refine ⟨6740373858987661662729259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8987165145316882216972345 6740373858987661662729259)
    ·
      refine ⟨10110560788481492494093889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740373858987661662729259 10110560788481492494093889)
      ·
        refine ⟨7582920591361119370570417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10110560788481492494093889 7582920591361119370570417)
        ·
          refine ⟨5687190443520839527927813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7582920591361119370570417 5687190443520839527927813)
          ·
            refine ⟨1066348208160157411486465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5687190443520839527927813 1066348208160157411486465)
            ·
              refine ⟨799761156120118058614849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066348208160157411486465 799761156120118058614849)
              ·
                refine ⟨599820867090088543961137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799761156120118058614849 599820867090088543961137)
                ·
                  refine ⟨449865650317566407970853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599820867090088543961137 449865650317566407970853)
                  ·
                    refine ⟨84349809434543701494535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449865650317566407970853 84349809434543701494535)
                    ·
                      rfl

theorem cell23_492812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_492812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492812 prefixEnd_492812 := by exact prefixLift 492812
  have htrace : WordTrace (prefixWord ++ tailWord_492812) baseStart_492812 baseEnd_492812 := by
    simpa [prefixWord, tailWord_492812, baseEnd_492812] using wordTrace_append hprefix tailTrace_492812
  have hstable : (prefixWord ++ tailWord_492812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492812).length < 2 ^ (prefixWord ++ tailWord_492812).sum := by decide
  have hdescent : baseEnd_492812 < baseStart_492812 := by decide
  rcases family_descends (prefixWord ++ tailWord_492812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
