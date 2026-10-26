import V185TrunkScan21Chunk017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_217355 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_217355 : Nat := 118140960795 + 217355 * 2 ^ 59
def prefixEnd_217355 : Nat := 4983230072969 + 3 ^ 40 * 217355 * 2
def baseEnd_217355 : Nat := 49603372292489925005737

theorem tailTrace_217355 : CollatzResearch.WordTrace tailWord_217355 prefixEnd_217355 49603372292489925005737 := by
  unfold tailWord_217355
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927588127567431123733519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285058751711620749155679 7927588127567431123733519)
  ·
    refine ⟨11891382191351146685600279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927588127567431123733519 11891382191351146685600279)
    ·
      refine ⟨17837073287026720028400419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11891382191351146685600279 17837073287026720028400419)
      ·
        refine ⟨26755609930540080042600629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17837073287026720028400419 26755609930540080042600629)
        ·
          refine ⟨2508338430988132503993809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26755609930540080042600629 2508338430988132503993809)
          ·
            refine ⟨1881253823241099377995357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508338430988132503993809 1881253823241099377995357)
            ·
              refine ⟨705470183715412266748259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1881253823241099377995357 705470183715412266748259)
              ·
                refine ⟨1058205275573118400122389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705470183715412266748259 1058205275573118400122389)
                ·
                  refine ⟨49603372292489925005737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1058205275573118400122389 49603372292489925005737)
                  ·
                    rfl

theorem cell21_217355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_217355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217355 prefixEnd_217355 := by exact prefixLift 217355
  have htrace : WordTrace (prefixWord ++ tailWord_217355) baseStart_217355 baseEnd_217355 := by
    simpa [prefixWord, tailWord_217355, baseEnd_217355] using wordTrace_append hprefix tailTrace_217355
  have hstable : (prefixWord ++ tailWord_217355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217355).length < 2 ^ (prefixWord ++ tailWord_217355).sum := by decide
  have hdescent : baseEnd_217355 < baseStart_217355 := by decide
  rcases family_descends (prefixWord ++ tailWord_217355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217358 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_217358 : Nat := 118140960795 + 217358 * 2 ^ 59
def prefixEnd_217358 : Nat := 4983230072969 + 3 ^ 40 * 217358 * 2
def baseEnd_217358 : Nat := 49604056933362586455731

theorem tailTrace_217358 : CollatzResearch.WordTrace tailWord_217358 prefixEnd_217358 49604056933362586455731 := by
  unfold tailWord_217358
  simp only [CollatzResearch.WordTrace]
  refine ⟨990962193319570329511591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5285131697704375090728485 990962193319570329511591)
  ·
    refine ⟨1486443289979355494267387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990962193319570329511591 1486443289979355494267387)
    ·
      refine ⟨2229664934969033241401081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486443289979355494267387 2229664934969033241401081)
      ·
        refine ⟨1672248701226774931050811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229664934969033241401081 1672248701226774931050811)
        ·
          refine ⟨2508373051840162396576217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672248701226774931050811 2508373051840162396576217)
          ·
            refine ⟨1881279788880121797432163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508373051840162396576217 1881279788880121797432163)
            ·
              refine ⟨2821919683320182696148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881279788880121797432163 2821919683320182696148245)
              ·
                refine ⟨132277485155633563881949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2821919683320182696148245 132277485155633563881949)
                ·
                  refine ⟨49604056933362586455731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132277485155633563881949 49604056933362586455731)
                  ·
                    rfl

theorem cell21_217358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_217358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217358 prefixEnd_217358 := by exact prefixLift 217358
  have htrace : WordTrace (prefixWord ++ tailWord_217358) baseStart_217358 baseEnd_217358 := by
    simpa [prefixWord, tailWord_217358, baseEnd_217358] using wordTrace_append hprefix tailTrace_217358
  have hstable : (prefixWord ++ tailWord_217358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217358).length < 2 ^ (prefixWord ++ tailWord_217358).sum := by decide
  have hdescent : baseEnd_217358 < baseStart_217358 := by decide
  rcases family_descends (prefixWord ++ tailWord_217358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217400 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_217400 : Nat := 118140960795 + 217400 * 2 ^ 59
def prefixEnd_217400 : Nat := 4983230072969 + 3 ^ 40 * 217400 * 2
def baseEnd_217400 : Nat := 49613641905579846755645

theorem tailTrace_217400 : CollatzResearch.WordTrace tailWord_217400 prefixEnd_217400 49613641905579846755645 := by
  unfold tailWord_217400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964614706202201904560827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5286152941602935872747769 3964614706202201904560827)
  ·
    refine ⟨5946922059303302856841241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3964614706202201904560827 5946922059303302856841241)
    ·
      refine ⟨4460191544477477142630931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5946922059303302856841241 4460191544477477142630931)
      ·
        refine ⟨6690287316716215713946397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460191544477477142630931 6690287316716215713946397)
        ·
          refine ⟨2508857743768580892729899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6690287316716215713946397 2508857743768580892729899)
          ·
            refine ⟨3763286615652871339094849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508857743768580892729899 3763286615652871339094849)
            ·
              refine ⟨2822464961739653504321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763286615652871339094849 2822464961739653504321137)
              ·
                refine ⟨2116848721304740128240853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822464961739653504321137 2116848721304740128240853)
                ·
                  refine ⟨49613641905579846755645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2116848721304740128240853 49613641905579846755645)
                  ·
                    rfl

theorem cell21_217400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_217400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217400 prefixEnd_217400 := by exact prefixLift 217400
  have htrace : WordTrace (prefixWord ++ tailWord_217400) baseStart_217400 baseEnd_217400 := by
    simpa [prefixWord, tailWord_217400, baseEnd_217400] using wordTrace_append hprefix tailTrace_217400
  have hstable : (prefixWord ++ tailWord_217400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217400).length < 2 ^ (prefixWord ++ tailWord_217400).sum := by decide
  have hdescent : baseEnd_217400 < baseStart_217400 := by decide
  rcases family_descends (prefixWord ++ tailWord_217400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217583 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_217583 : Nat := 118140960795 + 217583 * 2 ^ 59
def prefixEnd_217583 : Nat := 4983230072969 + 3 ^ 40 * 217583 * 2
def baseEnd_217583 : Nat := 49655404998812195205271

theorem tailTrace_217583 : CollatzResearch.WordTrace tailWord_217583 prefixEnd_217583 49655404998812195205271 := by
  unfold tailWord_217583
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935903970741426063033403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5290602647160950708688935 7935903970741426063033403)
  ·
    refine ⟨11903855956112139094550105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7935903970741426063033403 11903855956112139094550105)
    ·
      refine ⟨8927891967084104320912579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11903855956112139094550105 8927891967084104320912579)
      ·
        refine ⟨13391837950626156481368869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927891967084104320912579 13391837950626156481368869)
        ·
          refine ⟨2510969615742404340256663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13391837950626156481368869 2510969615742404340256663)
          ·
            refine ⟨3766454423613606510384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510969615742404340256663 3766454423613606510384995)
            ·
              refine ⟨5649681635420409765577493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766454423613606510384995 5649681635420409765577493)
              ·
                refine ⟨264828826660331707761445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5649681635420409765577493 264828826660331707761445)
                ·
                  refine ⟨49655404998812195205271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264828826660331707761445 49655404998812195205271)
                  ·
                    rfl

theorem cell21_217583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_217583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217583 prefixEnd_217583 := by exact prefixLift 217583
  have htrace : WordTrace (prefixWord ++ tailWord_217583) baseStart_217583 baseEnd_217583 := by
    simpa [prefixWord, tailWord_217583, baseEnd_217583] using wordTrace_append hprefix tailTrace_217583
  have hstable : (prefixWord ++ tailWord_217583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217583).length < 2 ^ (prefixWord ++ tailWord_217583).sum := by decide
  have hdescent : baseEnd_217583 < baseStart_217583 := by decide
  rcases family_descends (prefixWord ++ tailWord_217583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217614 : List Nat := [4, 1, 1, 2, 3, 1, 2, 7]
def baseStart_217614 : Nat := 118140960795 + 217614 * 2 ^ 59
def prefixEnd_217614 : Nat := 4983230072969 + 3 ^ 40 * 217614 * 2
def baseEnd_217614 : Nat := 16554159873721010062847

theorem tailTrace_217614 : CollatzResearch.WordTrace tailWord_217614 prefixEnd_217614 16554159873721010062847 := by
  unfold tailWord_217614
  simp only [CollatzResearch.WordTrace]
  refine ⟨992129329203639794676487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5291356422419412238274597 992129329203639794676487)
  ·
    refine ⟨1488193993805459692014731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992129329203639794676487 1488193993805459692014731)
    ·
      refine ⟨2232290990708189538022097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488193993805459692014731 2232290990708189538022097)
      ·
        refine ⟨1674218243031142153516573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232290990708189538022097 1674218243031142153516573)
        ·
          refine ⟨627831841136678307568715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1674218243031142153516573 627831841136678307568715)
          ·
            refine ⟨941747761705017461353073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627831841136678307568715 941747761705017461353073)
            ·
              refine ⟨706310821278763096014805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941747761705017461353073 706310821278763096014805)
              ·
                refine ⟨16554159873721010062847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 706310821278763096014805 16554159873721010062847)
                ·
                  rfl

theorem cell21_217614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_217614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217614 prefixEnd_217614 := by exact prefixLift 217614
  have htrace : WordTrace (prefixWord ++ tailWord_217614) baseStart_217614 baseEnd_217614 := by
    simpa [prefixWord, tailWord_217614, baseEnd_217614] using wordTrace_append hprefix tailTrace_217614
  have hstable : (prefixWord ++ tailWord_217614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217614).length < 2 ^ (prefixWord ++ tailWord_217614).sum := by decide
  have hdescent : baseEnd_217614 < baseStart_217614 := by decide
  rcases family_descends (prefixWord ++ tailWord_217614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217730 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_217730 : Nat := 118140960795 + 217730 * 2 ^ 59
def prefixEnd_217730 : Nat := 4983230072969 + 3 ^ 40 * 217730 * 2
def baseEnd_217730 : Nat := 49688952401572606254971

theorem tailTrace_217730 : CollatzResearch.WordTrace tailWord_217730 prefixEnd_217730 49688952401572606254971 := by
  unfold tailWord_217730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985316375302217542158661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5294177000805913445756429 1985316375302217542158661)
  ·
    refine ⟨372246820369165789154749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1985316375302217542158661 372246820369165789154749)
    ·
      refine ⟨139592557638437170933031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372246820369165789154749 139592557638437170933031)
      ·
        refine ⟨209388836457655756399547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139592557638437170933031 209388836457655756399547)
        ·
          refine ⟨314083254686483634599321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209388836457655756399547 314083254686483634599321)
          ·
            refine ⟨235562441014862725949491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314083254686483634599321 235562441014862725949491)
            ·
              refine ⟨353343661522294088924237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235562441014862725949491 353343661522294088924237)
              ·
                refine ⟨132503873070860283346589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353343661522294088924237 132503873070860283346589)
                ·
                  refine ⟨49688952401572606254971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132503873070860283346589 49688952401572606254971)
                  ·
                    rfl

theorem cell21_217730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_217730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217730 prefixEnd_217730 := by exact prefixLift 217730
  have htrace : WordTrace (prefixWord ++ tailWord_217730) baseStart_217730 baseEnd_217730 := by
    simpa [prefixWord, tailWord_217730, baseEnd_217730] using wordTrace_append hprefix tailTrace_217730
  have hstable : (prefixWord ++ tailWord_217730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217730).length < 2 ^ (prefixWord ++ tailWord_217730).sum := by decide
  have hdescent : baseEnd_217730 < baseStart_217730 := by decide
  rcases family_descends (prefixWord ++ tailWord_217730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217873 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 3]
def baseStart_217873 : Nat := 118140960795 + 217873 * 2 ^ 59
def prefixEnd_217873 : Nat := 4983230072969 + 3 ^ 40 * 217873 * 2
def baseEnd_217873 : Nat := 49721586949836135371345

theorem tailTrace_217873 : CollatzResearch.WordTrace tailWord_217873 prefixEnd_217873 49721586949836135371345 := by
  unfold tailWord_217873
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946481139690805591090273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5297654093127203727393515 7946481139690805591090273)
  ·
    refine ⟨5959860854768104193317705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7946481139690805591090273 5959860854768104193317705)
    ·
      refine ⟨4469895641076078144988279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959860854768104193317705 4469895641076078144988279)
      ·
        refine ⟨6704843461614117217482419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469895641076078144988279 6704843461614117217482419)
        ·
          refine ⟨10057265192421175826223629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704843461614117217482419 10057265192421175826223629)
          ·
            refine ⟨3771474447157940934833861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10057265192421175826223629 3771474447157940934833861)
            ·
              refine ⟨707151458842113925281349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3771474447157940934833861 707151458842113925281349)
              ·
                refine ⟨132590898532896360990253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707151458842113925281349 132590898532896360990253)
                ·
                  refine ⟨49721586949836135371345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132590898532896360990253 49721586949836135371345)
                  ·
                    rfl

theorem cell21_217873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_217873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217873 prefixEnd_217873 := by exact prefixLift 217873
  have htrace : WordTrace (prefixWord ++ tailWord_217873) baseStart_217873 baseEnd_217873 := by
    simpa [prefixWord, tailWord_217873, baseEnd_217873] using wordTrace_append hprefix tailTrace_217873
  have hstable : (prefixWord ++ tailWord_217873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217873).length < 2 ^ (prefixWord ++ tailWord_217873).sum := by decide
  have hdescent : baseEnd_217873 < baseStart_217873 := by decide
  rcases family_descends (prefixWord ++ tailWord_217873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217924 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_217924 : Nat := 118140960795 + 217924 * 2 ^ 59
def prefixEnd_217924 : Nat := 4983230072969 + 3 ^ 40 * 217924 * 2
def baseEnd_217924 : Nat := 49733225844671380021241

theorem tailTrace_217924 : CollatzResearch.WordTrace tailWord_217924 prefixEnd_217924 49733225844671380021241 := by
  unfold tailWord_217924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974170631253020650598413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5298894175004027534131217 3974170631253020650598413)
  ·
    refine ⟨1490313986719882743974405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3974170631253020650598413 1490313986719882743974405)
    ·
      refine ⟨279433872509978014495201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1490313986719882743974405 279433872509978014495201)
      ·
        refine ⟨209575404382483510871401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279433872509978014495201 209575404382483510871401)
        ·
          refine ⟨157181553286862633153551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209575404382483510871401 157181553286862633153551)
          ·
            refine ⟨235772329930293949730327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157181553286862633153551 235772329930293949730327)
            ·
              refine ⟨353658494895440924595491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235772329930293949730327 353658494895440924595491)
              ·
                refine ⟨530487742343161386893237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353658494895440924595491 530487742343161386893237)
                ·
                  refine ⟨49733225844671380021241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530487742343161386893237 49733225844671380021241)
                  ·
                    rfl

theorem cell21_217924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_217924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217924 prefixEnd_217924 := by exact prefixLift 217924
  have htrace : WordTrace (prefixWord ++ tailWord_217924) baseStart_217924 baseEnd_217924 := by
    simpa [prefixWord, tailWord_217924, baseEnd_217924] using wordTrace_append hprefix tailTrace_217924
  have hstable : (prefixWord ++ tailWord_217924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217924).length < 2 ^ (prefixWord ++ tailWord_217924).sum := by decide
  have hdescent : baseEnd_217924 < baseStart_217924 := by decide
  rcases family_descends (prefixWord ++ tailWord_217924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217994 : List Nat := [3, 1, 2, 4, 1, 1, 3, 6]
def baseStart_217994 : Nat := 118140960795 + 217994 * 2 ^ 59
def prefixEnd_217994 : Nat := 4983230072969 + 3 ^ 40 * 217994 * 2
def baseEnd_217994 : Nat := 16583066932788937951477

theorem tailTrace_217994 : CollatzResearch.WordTrace tailWord_217994 prefixEnd_217994 16583066932788937951477 := by
  unfold tailWord_217994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987723593063110814061259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5300596248168295504163357 1987723593063110814061259)
  ·
    refine ⟨2981585389594666221091889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987723593063110814061259 2981585389594666221091889)
    ·
      refine ⟨2236189042195999665818917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981585389594666221091889 2236189042195999665818917)
      ·
        refine ⟨419285445411749937341047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2236189042195999665818917 419285445411749937341047)
        ·
          refine ⟨628928168117624906011571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419285445411749937341047 628928168117624906011571)
          ·
            refine ⟨943392252176437359017357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628928168117624906011571 943392252176437359017357)
            ·
              refine ⟨353772094566164009631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943392252176437359017357 353772094566164009631509)
              ·
                refine ⟨16583066932788937951477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353772094566164009631509 16583066932788937951477)
                ·
                  rfl

theorem cell21_217994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_217994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217994 prefixEnd_217994 := by exact prefixLift 217994
  have htrace : WordTrace (prefixWord ++ tailWord_217994) baseStart_217994 baseEnd_217994 := by
    simpa [prefixWord, tailWord_217994, baseEnd_217994] using wordTrace_append hprefix tailTrace_217994
  have hstable : (prefixWord ++ tailWord_217994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217994).length < 2 ^ (prefixWord ++ tailWord_217994).sum := by decide
  have hdescent : baseEnd_217994 < baseStart_217994 := by decide
  rcases family_descends (prefixWord ++ tailWord_217994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218025 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 3]
def baseStart_218025 : Nat := 118140960795 + 218025 * 2 ^ 59
def prefixEnd_218025 : Nat := 4983230072969 + 3 ^ 40 * 218025 * 2
def baseEnd_218025 : Nat := 49756275420717648837701

theorem tailTrace_218025 : CollatzResearch.WordTrace tailWord_218025 prefixEnd_218025 49756275420717648837701 := by
  unfold tailWord_218025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952025035140135550623529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5301350023426757033749019 7952025035140135550623529)
  ·
    refine ⟨5964018776355101662967647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7952025035140135550623529 5964018776355101662967647)
    ·
      refine ⟨8946028164532652494451471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964018776355101662967647 8946028164532652494451471)
      ·
        refine ⟨13419042246798978741677207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8946028164532652494451471 13419042246798978741677207)
        ·
          refine ⟨20128563370198468112515811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13419042246798978741677207 20128563370198468112515811)
          ·
            refine ⟨30192845055297702168773717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20128563370198468112515811 30192845055297702168773717)
            ·
              refine ⟨353822402991769947290317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 30192845055297702168773717 353822402991769947290317)
              ·
                refine ⟨132683401121913730233869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353822402991769947290317 132683401121913730233869)
                ·
                  refine ⟨49756275420717648837701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132683401121913730233869 49756275420717648837701)
                  ·
                    rfl

theorem cell21_218025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_218025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218025 prefixEnd_218025 := by exact prefixLift 218025
  have htrace : WordTrace (prefixWord ++ tailWord_218025) baseStart_218025 baseEnd_218025 := by
    simpa [prefixWord, tailWord_218025, baseEnd_218025] using wordTrace_append hprefix tailTrace_218025
  have hstable : (prefixWord ++ tailWord_218025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218025).length < 2 ^ (prefixWord ++ tailWord_218025).sum := by decide
  have hdescent : baseEnd_218025 < baseStart_218025 := by decide
  rcases family_descends (prefixWord ++ tailWord_218025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218039 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_218039 : Nat := 118140960795 + 218039 * 2 ^ 59
def prefixEnd_218039 : Nat := 4983230072969 + 3 ^ 40 * 218039 * 2
def baseEnd_218039 : Nat := 49759470411456735604339

theorem tailTrace_218039 : CollatzResearch.WordTrace tailWord_218039 prefixEnd_218039 49759470411456735604339 := by
  unfold tailWord_218039
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952535657089415941633171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5301690438059610627755447 7952535657089415941633171)
  ·
    refine ⟨11928803485634123912449757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7952535657089415941633171 11928803485634123912449757)
    ·
      refine ⟨4473301307112796467168659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11928803485634123912449757 4473301307112796467168659)
      ·
        refine ⟨6709951960669194700752989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473301307112796467168659 6709951960669194700752989)
        ·
          refine ⟨2516231985250948012782371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6709951960669194700752989 2516231985250948012782371)
          ·
            refine ⟨3774347977876422019173557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516231985250948012782371 3774347977876422019173557)
            ·
              refine ⟨353845122925914564297521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3774347977876422019173557 353845122925914564297521)
              ·
                refine ⟨265383842194435923223141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353845122925914564297521 265383842194435923223141)
                ·
                  refine ⟨49759470411456735604339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265383842194435923223141 49759470411456735604339)
                  ·
                    rfl

theorem cell21_218039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_218039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218039 prefixEnd_218039 := by exact prefixLift 218039
  have htrace : WordTrace (prefixWord ++ tailWord_218039) baseStart_218039 baseEnd_218039 := by
    simpa [prefixWord, tailWord_218039, baseEnd_218039] using wordTrace_append hprefix tailTrace_218039
  have hstable : (prefixWord ++ tailWord_218039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218039).length < 2 ^ (prefixWord ++ tailWord_218039).sum := by decide
  have hdescent : baseEnd_218039 < baseStart_218039 := by decide
  rcases family_descends (prefixWord ++ tailWord_218039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218177 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_218177 : Nat := 118140960795 + 218177 * 2 ^ 59
def prefixEnd_218177 : Nat := 4983230072969 + 3 ^ 40 * 218177 * 2
def baseEnd_218177 : Nat := 49790963891599162304057

theorem tailTrace_218177 : CollatzResearch.WordTrace tailWord_218177 prefixEnd_218177 49790963891599162304057 := by
  unfold tailWord_218177
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957568930589465510156785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305045953726310340104523 7957568930589465510156785)
  ·
    refine ⟨5968176697942099132617589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7957568930589465510156785 5968176697942099132617589)
    ·
      refine ⟨559516565432071793682899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5968176697942099132617589 559516565432071793682899)
      ·
        refine ⟨839274848148107690524349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559516565432071793682899 839274848148107690524349)
        ·
          refine ⟨314728068055540383946631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839274848148107690524349 314728068055540383946631)
          ·
            refine ⟨472092102083310575919947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314728068055540383946631 472092102083310575919947)
            ·
              refine ⟨708138153124965863879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472092102083310575919947 708138153124965863879921)
              ·
                refine ⟨531103614843724397909941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708138153124965863879921 531103614843724397909941)
                ·
                  refine ⟨49790963891599162304057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 531103614843724397909941 49790963891599162304057)
                  ·
                    rfl

theorem cell21_218177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_218177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218177 prefixEnd_218177 := by exact prefixLift 218177
  have htrace : WordTrace (prefixWord ++ tailWord_218177) baseStart_218177 baseEnd_218177 := by
    simpa [prefixWord, tailWord_218177, baseEnd_218177] using wordTrace_append hprefix tailTrace_218177
  have hstable : (prefixWord ++ tailWord_218177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218177).length < 2 ^ (prefixWord ++ tailWord_218177).sum := by decide
  have hdescent : baseEnd_218177 < baseStart_218177 := by decide
  rcases family_descends (prefixWord ++ tailWord_218177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218194 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_218194 : Nat := 118140960795 + 218194 * 2 ^ 59
def prefixEnd_218194 : Nat := 4983230072969 + 3 ^ 40 * 218194 * 2
def baseEnd_218194 : Nat := 49794843523210910520689

theorem tailTrace_218194 : CollatzResearch.WordTrace tailWord_218194 prefixEnd_218194 49794843523210910520689 := by
  unfold tailWord_218194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989547242881969353381409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5305459314351918275683757 1989547242881969353381409)
  ·
    refine ⟨1492160432161477015036057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989547242881969353381409 1492160432161477015036057)
    ·
      refine ⟨1119120324121107761277043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492160432161477015036057 1119120324121107761277043)
      ·
        refine ⟨1678680486181661641915565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119120324121107761277043 1678680486181661641915565)
        ·
          refine ⟨629505182318123115718337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1678680486181661641915565 629505182318123115718337)
          ·
            refine ⟨472128886738592336788753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629505182318123115718337 472128886738592336788753)
            ·
              refine ⟨354096665053944252591565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472128886738592336788753 354096665053944252591565)
              ·
                refine ⟨132786249395229094721837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354096665053944252591565 132786249395229094721837)
                ·
                  refine ⟨49794843523210910520689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132786249395229094721837 49794843523210910520689)
                  ·
                    rfl

theorem cell21_218194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_218194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218194 prefixEnd_218194 := by exact prefixLift 218194
  have htrace : WordTrace (prefixWord ++ tailWord_218194) baseStart_218194 baseEnd_218194 := by
    simpa [prefixWord, tailWord_218194, baseEnd_218194] using wordTrace_append hprefix tailTrace_218194
  have hstable : (prefixWord ++ tailWord_218194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218194).length < 2 ^ (prefixWord ++ tailWord_218194).sum := by decide
  have hdescent : baseEnd_218194 < baseStart_218194 := by decide
  rcases family_descends (prefixWord ++ tailWord_218194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218250 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_218250 : Nat := 118140960795 + 218250 * 2 ^ 59
def prefixEnd_218250 : Nat := 4983230072969 + 3 ^ 40 * 218250 * 2
def baseEnd_218250 : Nat := 49807623486167257587241

theorem tailTrace_218250 : CollatzResearch.WordTrace tailWord_218250 prefixEnd_218250 49807623486167257587241 := by
  unfold tailWord_218250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990057864831249744391051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5306820972883332651709469 1990057864831249744391051)
  ·
    refine ⟨2985086797246874616586577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1990057864831249744391051 2985086797246874616586577)
    ·
      refine ⟨2238815097935155962439933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2985086797246874616586577 2238815097935155962439933)
      ·
        refine ⟨839555661725683485914975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2238815097935155962439933 839555661725683485914975)
        ·
          refine ⟨1259333492588525228872463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839555661725683485914975 1259333492588525228872463)
          ·
            refine ⟨1889000238882787843308695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259333492588525228872463 1889000238882787843308695)
            ·
              refine ⟨2833500358324181764963043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889000238882787843308695 2833500358324181764963043)
              ·
                refine ⟨4250250537486272647444565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833500358324181764963043 4250250537486272647444565)
                ·
                  refine ⟨49807623486167257587241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4250250537486272647444565 49807623486167257587241)
                  ·
                    rfl

theorem cell21_218250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_218250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218250 prefixEnd_218250 := by exact prefixLift 218250
  have htrace : WordTrace (prefixWord ++ tailWord_218250) baseStart_218250 baseEnd_218250 := by
    simpa [prefixWord, tailWord_218250, baseEnd_218250] using wordTrace_append hprefix tailTrace_218250
  have hstable : (prefixWord ++ tailWord_218250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218250).length < 2 ^ (prefixWord ++ tailWord_218250).sum := by decide
  have hdescent : baseEnd_218250 < baseStart_218250 := by decide
  rcases family_descends (prefixWord ++ tailWord_218250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218270 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_218270 : Nat := 118140960795 + 218270 * 2 ^ 59
def prefixEnd_218270 : Nat := 4983230072969 + 3 ^ 40 * 218270 * 2
def baseEnd_218270 : Nat := 49812187758651667253867

theorem tailTrace_218270 : CollatzResearch.WordTrace tailWord_218270 prefixEnd_218270 49812187758651667253867 := by
  unfold tailWord_218270
  simp only [CollatzResearch.WordTrace]
  refine ⟨995120114906567799161533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5307307279501694928861509 995120114906567799161533)
  ·
    refine ⟨373170043089962924685575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 995120114906567799161533 373170043089962924685575)
    ·
      refine ⟨559755064634944387028363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373170043089962924685575 559755064634944387028363)
      ·
        refine ⟨839632596952416580542545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559755064634944387028363 839632596952416580542545)
        ·
          refine ⟨629724447714312435406909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839632596952416580542545 629724447714312435406909)
          ·
            refine ⟨236146667892867163277591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 629724447714312435406909 236146667892867163277591)
            ·
              refine ⟨354220001839300744916387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236146667892867163277591 354220001839300744916387)
              ·
                refine ⟨531330002758951117374581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354220001839300744916387 531330002758951117374581)
                ·
                  refine ⟨49812187758651667253867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 531330002758951117374581 49812187758651667253867)
                  ·
                    rfl

theorem cell21_218270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_218270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218270 prefixEnd_218270 := by exact prefixLift 218270
  have htrace : WordTrace (prefixWord ++ tailWord_218270) baseStart_218270 baseEnd_218270 := by
    simpa [prefixWord, tailWord_218270, baseEnd_218270] using wordTrace_append hprefix tailTrace_218270
  have hstable : (prefixWord ++ tailWord_218270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218270).length < 2 ^ (prefixWord ++ tailWord_218270).sum := by decide
  have hdescent : baseEnd_218270 < baseStart_218270 := by decide
  rcases family_descends (prefixWord ++ tailWord_218270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218295 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_218295 : Nat := 118140960795 + 218295 * 2 ^ 59
def prefixEnd_218295 : Nat := 4983230072969 + 3 ^ 40 * 218295 * 2
def baseEnd_218295 : Nat := 49817893099257179337149

theorem tailTrace_218295 : CollatzResearch.WordTrace tailWord_218295 prefixEnd_218295 49817893099257179337149 := by
  unfold tailWord_218295
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961872744161971662952339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307915162774647775301559 7961872744161971662952339)
  ·
    refine ⟨11942809116242957494428509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961872744161971662952339 11942809116242957494428509)
    ·
      refine ⟨4478553418591109060410691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11942809116242957494428509 4478553418591109060410691)
      ·
        refine ⟨6717830127886663590616037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478553418591109060410691 6717830127886663590616037)
        ·
          refine ⟨1259593148978749423240507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6717830127886663590616037 1259593148978749423240507)
          ·
            refine ⟨1889389723468124134860761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259593148978749423240507 1889389723468124134860761)
            ·
              refine ⟨1417042292601093101145571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889389723468124134860761 1417042292601093101145571)
              ·
                refine ⟨2125563438901639651718357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417042292601093101145571 2125563438901639651718357)
                ·
                  refine ⟨49817893099257179337149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2125563438901639651718357 49817893099257179337149)
                  ·
                    rfl

theorem cell21_218295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_218295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218295 prefixEnd_218295 := by exact prefixLift 218295
  have htrace : WordTrace (prefixWord ++ tailWord_218295) baseStart_218295 baseEnd_218295 := by
    simpa [prefixWord, tailWord_218295, baseEnd_218295] using wordTrace_append hprefix tailTrace_218295
  have hstable : (prefixWord ++ tailWord_218295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218295).length < 2 ^ (prefixWord ++ tailWord_218295).sum := by decide
  have hdescent : baseEnd_218295 < baseStart_218295 := by decide
  rcases family_descends (prefixWord ++ tailWord_218295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218416 : List Nat := [2, 1, 1, 1, 2, 2, 5, 7]
def baseStart_218416 : Nat := 118140960795 + 218416 * 2 ^ 59
def prefixEnd_218416 : Nat := 4983230072969 + 3 ^ 40 * 218416 * 2
def baseEnd_218416 : Nat := 16615168982595952606745

theorem tailTrace_218416 : CollatzResearch.WordTrace tailWord_218416 prefixEnd_218416 16615168982595952606745 := by
  unfold tailWord_218416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983142988361804664053551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5310857317815739552071401 3983142988361804664053551)
  ·
    refine ⟨5974714482542706996080327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3983142988361804664053551 5974714482542706996080327)
    ·
      refine ⟨8962071723814060494120491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974714482542706996080327 8962071723814060494120491)
      ·
        refine ⟨13443107585721090741180737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962071723814060494120491 13443107585721090741180737)
        ·
          refine ⟨10082330689290818055885553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13443107585721090741180737 10082330689290818055885553)
          ·
            refine ⟨7561748016968113541914165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082330689290818055885553 7561748016968113541914165)
            ·
              refine ⟨708913876590760644554453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7561748016968113541914165 708913876590760644554453)
              ·
                refine ⟨16615168982595952606745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 708913876590760644554453 16615168982595952606745)
                ·
                  rfl

theorem cell21_218416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_218416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218416 prefixEnd_218416 := by exact prefixLift 218416
  have htrace : WordTrace (prefixWord ++ tailWord_218416) baseStart_218416 baseEnd_218416 := by
    simpa [prefixWord, tailWord_218416, baseEnd_218416] using wordTrace_append hprefix tailTrace_218416
  have hstable : (prefixWord ++ tailWord_218416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218416).length < 2 ^ (prefixWord ++ tailWord_218416).sum := by decide
  have hdescent : baseEnd_218416 < baseStart_218416 := by decide
  rcases family_descends (prefixWord ++ tailWord_218416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218433 : List Nat := [1, 2, 5, 2, 1, 1, 9]
def baseStart_218433 : Nat := 118140960795 + 218433 * 2 ^ 59
def prefixEnd_218433 : Nat := 4983230072969 + 3 ^ 40 * 218433 * 2
def baseEnd_218433 : Nat := 5538820731044400670763

theorem tailTrace_218433 : CollatzResearch.WordTrace tailWord_218433 prefixEnd_218433 5538820731044400670763 := by
  unfold tailWord_218433
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966906017662021231475953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5311270678441347487650635 7966906017662021231475953)
  ·
    refine ⟨5975179513246515923606965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7966906017662021231475953 5975179513246515923606965)
    ·
      refine ⟨560173079366860867838153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5975179513246515923606965 560173079366860867838153)
      ·
        refine ⟨420129809525145650878615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560173079366860867838153 420129809525145650878615)
        ·
          refine ⟨630194714287718476317923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420129809525145650878615 630194714287718476317923)
          ·
            refine ⟨945292071431577714476885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630194714287718476317923 945292071431577714476885)
            ·
              refine ⟨5538820731044400670763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 945292071431577714476885 5538820731044400670763)
              ·
                rfl

theorem cell21_218433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 9].length) (baseStart_218433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218433 prefixEnd_218433 := by exact prefixLift 218433
  have htrace : WordTrace (prefixWord ++ tailWord_218433) baseStart_218433 baseEnd_218433 := by
    simpa [prefixWord, tailWord_218433, baseEnd_218433] using wordTrace_append hprefix tailTrace_218433
  have hstable : (prefixWord ++ tailWord_218433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218433).length < 2 ^ (prefixWord ++ tailWord_218433).sum := by decide
  have hdescent : baseEnd_218433 < baseStart_218433 := by decide
  rcases family_descends (prefixWord ++ tailWord_218433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218540 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_218540 : Nat := 118140960795 + 218540 * 2 ^ 59
def prefixEnd_218540 : Nat := 4983230072969 + 3 ^ 40 * 218540 * 2
def baseEnd_218540 : Nat := 49873805437191197753315

theorem tailTrace_218540 : CollatzResearch.WordTrace tailWord_218540 prefixEnd_218540 49873805437191197753315 := by
  unfold tailWord_218540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985404314137189252810537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5313872418849585670414049 3985404314137189252810537)
  ·
    refine ⟨2989053235602891939607903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3985404314137189252810537 2989053235602891939607903)
    ·
      refine ⟨4483579853404337909411855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989053235602891939607903 4483579853404337909411855)
      ·
        refine ⟨6725369780106506864117783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483579853404337909411855 6725369780106506864117783)
        ·
          refine ⟨10088054670159760296176675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725369780106506864117783 10088054670159760296176675)
          ·
            refine ⟨15132082005239640444265013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088054670159760296176675 15132082005239640444265013)
            ·
              refine ⟨1418632687991216291649845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15132082005239640444265013 1418632687991216291649845)
              ·
                refine ⟨132996814499176527342173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1418632687991216291649845 132996814499176527342173)
                ·
                  refine ⟨49873805437191197753315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132996814499176527342173 49873805437191197753315)
                  ·
                    rfl

theorem cell21_218540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_218540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218540 prefixEnd_218540 := by exact prefixLift 218540
  have htrace : WordTrace (prefixWord ++ tailWord_218540) baseStart_218540 baseEnd_218540 := by
    simpa [prefixWord, tailWord_218540, baseEnd_218540] using wordTrace_append hprefix tailTrace_218540
  have hstable : (prefixWord ++ tailWord_218540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218540).length < 2 ^ (prefixWord ++ tailWord_218540).sum := by decide
  have hdescent : baseEnd_218540 < baseStart_218540 := by decide
  rcases family_descends (prefixWord ++ tailWord_218540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218568 : List Nat := [2, 1, 3, 1, 3, 1, 2, 8]
def baseStart_218568 : Nat := 118140960795 + 218568 * 2 ^ 59
def prefixEnd_218568 : Nat := 4983230072969 + 3 ^ 40 * 218568 * 2
def baseEnd_218568 : Nat := 16626731806223123762197

theorem tailTrace_218568 : CollatzResearch.WordTrace tailWord_218568 prefixEnd_218568 16626731806223123762197 := by
  unfold tailWord_218568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985914936086469643820179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5314553248115292858426905 3985914936086469643820179)
  ·
    refine ⟨5978872404129704465730269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985914936086469643820179 5978872404129704465730269)
    ·
      refine ⟨2242077151548639174648851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5978872404129704465730269 2242077151548639174648851)
      ·
        refine ⟨3363115727322958761973277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242077151548639174648851 3363115727322958761973277)
        ·
          refine ⟨1261168397746109535739979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363115727322958761973277 1261168397746109535739979)
          ·
            refine ⟨1891752596619164303609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261168397746109535739979 1891752596619164303609969)
            ·
              refine ⟨1418814447464373227707477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891752596619164303609969 1418814447464373227707477)
              ·
                refine ⟨16626731806223123762197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1418814447464373227707477 16626731806223123762197)
                ·
                  rfl

theorem cell21_218568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_218568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218568 prefixEnd_218568 := by exact prefixLift 218568
  have htrace : WordTrace (prefixWord ++ tailWord_218568) baseStart_218568 baseEnd_218568 := by
    simpa [prefixWord, tailWord_218568, baseEnd_218568] using wordTrace_append hprefix tailTrace_218568
  have hstable : (prefixWord ++ tailWord_218568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218568).length < 2 ^ (prefixWord ++ tailWord_218568).sum := by decide
  have hdescent : baseEnd_218568 < baseStart_218568 := by decide
  rcases family_descends (prefixWord ++ tailWord_218568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218585 : List Nat := [1, 2, 1, 2, 4, 2, 4, 5]
def baseStart_218585 : Nat := 118140960795 + 218585 * 2 ^ 59
def prefixEnd_218585 : Nat := 4983230072969 + 3 ^ 40 * 218585 * 2
def baseEnd_218585 : Nat := 16628025016760373167741

theorem tailTrace_218585 : CollatzResearch.WordTrace tailWord_218585 prefixEnd_218585 16628025016760373167741 := by
  unfold tailWord_218585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972449913111351191009209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5314966608740900794006139 7972449913111351191009209)
  ·
    refine ⟨5979337434833513393256907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7972449913111351191009209 5979337434833513393256907)
    ·
      refine ⟨8969006152250270089885361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979337434833513393256907 8969006152250270089885361)
      ·
        refine ⟨6726754614187702567414021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8969006152250270089885361 6726754614187702567414021)
        ·
          refine ⟨1261266490160194231390129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6726754614187702567414021 1261266490160194231390129)
          ·
            refine ⟨945949867620145673542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261266490160194231390129 945949867620145673542597)
            ·
              refine ⟨177365600178777313789237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 945949867620145673542597 177365600178777313789237)
              ·
                refine ⟨16628025016760373167741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177365600178777313789237 16628025016760373167741)
                ·
                  rfl

theorem cell21_218585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].length) (baseStart_218585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218585 prefixEnd_218585 := by exact prefixLift 218585
  have htrace : WordTrace (prefixWord ++ tailWord_218585) baseStart_218585 baseEnd_218585 := by
    simpa [prefixWord, tailWord_218585, baseEnd_218585] using wordTrace_append hprefix tailTrace_218585
  have hstable : (prefixWord ++ tailWord_218585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218585).length < 2 ^ (prefixWord ++ tailWord_218585).sum := by decide
  have hdescent : baseEnd_218585 < baseStart_218585 := by decide
  rcases family_descends (prefixWord ++ tailWord_218585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218602 : List Nat := [3, 1, 3, 1, 5, 1, 7]
def baseStart_218602 : Nat := 118140960795 + 218602 * 2 ^ 59
def prefixEnd_218602 : Nat := 4983230072969 + 3 ^ 40 * 218602 * 2
def baseEnd_218602 : Nat := 5543106075765874191095

theorem tailTrace_218602 : CollatzResearch.WordTrace tailWord_218602 prefixEnd_218602 5543106075765874191095 := by
  unfold tailWord_218602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993267488512440773594515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5315379969366508729585373 1993267488512440773594515)
  ·
    refine ⟨2989901232768661160391773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993267488512440773594515 2989901232768661160391773)
    ·
      refine ⟨1121212962288247935146915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2989901232768661160391773 1121212962288247935146915)
      ·
        refine ⟨1681819443432371902720373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121212962288247935146915 1681819443432371902720373)
        ·
          refine ⟨157670572821784865880035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1681819443432371902720373 157670572821784865880035)
          ·
            refine ⟨236505859232677298820053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157670572821784865880035 236505859232677298820053)
            ·
              refine ⟨5543106075765874191095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 236505859232677298820053 5543106075765874191095)
              ·
                rfl

theorem cell21_218602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 7].length) (baseStart_218602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218602 prefixEnd_218602 := by exact prefixLift 218602
  have htrace : WordTrace (prefixWord ++ tailWord_218602) baseStart_218602 baseEnd_218602 := by
    simpa [prefixWord, tailWord_218602, baseEnd_218602] using wordTrace_append hprefix tailTrace_218602
  have hstable : (prefixWord ++ tailWord_218602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218602).length < 2 ^ (prefixWord ++ tailWord_218602).sum := by decide
  have hdescent : baseEnd_218602 < baseStart_218602 := by decide
  rcases family_descends (prefixWord ++ tailWord_218602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218616 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_218616 : Nat := 118140960795 + 218616 * 2 ^ 59
def prefixEnd_218616 : Nat := 4983230072969 + 3 ^ 40 * 218616 * 2
def baseEnd_218616 : Nat := 49891149672631954486493

theorem tailTrace_218616 : CollatzResearch.WordTrace tailWord_218616 prefixEnd_218616 49891149672631954486493 := by
  unfold tailWord_218616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986790287999521742693851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5315720383999362323591801 3986790287999521742693851)
  ·
    refine ⟨5980185431999282614040777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3986790287999521742693851 5980185431999282614040777)
    ·
      refine ⟨4485139073999461960530583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5980185431999282614040777 4485139073999461960530583)
      ·
        refine ⟨6727708610999192940795875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485139073999461960530583 6727708610999192940795875)
        ·
          refine ⟨10091562916498789411193813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727708610999192940795875 10091562916498789411193813)
          ·
            refine ⟨236521005855440376824855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10091562916498789411193813 236521005855440376824855)
            ·
              refine ⟨354781508783160565237283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236521005855440376824855 354781508783160565237283)
              ·
                refine ⟨532172263174740847855925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354781508783160565237283 532172263174740847855925)
                ·
                  refine ⟨49891149672631954486493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532172263174740847855925 49891149672631954486493)
                  ·
                    rfl

theorem cell21_218616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_218616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218616 prefixEnd_218616 := by exact prefixLift 218616
  have htrace : WordTrace (prefixWord ++ tailWord_218616) baseStart_218616 baseEnd_218616 := by
    simpa [prefixWord, tailWord_218616, baseEnd_218616] using wordTrace_append hprefix tailTrace_218616
  have hstable : (prefixWord ++ tailWord_218616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218616).length < 2 ^ (prefixWord ++ tailWord_218616).sum := by decide
  have hdescent : baseEnd_218616 < baseStart_218616 := by decide
  rcases family_descends (prefixWord ++ tailWord_218616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218622 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_218622 : Nat := 118140960795 + 218622 * 2 ^ 59
def prefixEnd_218622 : Nat := 4983230072969 + 3 ^ 40 * 218622 * 2
def baseEnd_218622 : Nat := 49892518954377277386481

theorem tailTrace_218622 : CollatzResearch.WordTrace tailWord_218622 prefixEnd_218622 49892518954377277386481 := by
  unfold tailWord_218622
  simp only [CollatzResearch.WordTrace]
  refine ⟨996724926747163313763265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5315866275984871006737413 996724926747163313763265)
  ·
    refine ⟨747543695060372485322449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 996724926747163313763265 747543695060372485322449)
    ·
      refine ⟨560657771295279363991837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747543695060372485322449 560657771295279363991837)
      ·
        refine ⟨210246664235729761496939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560657771295279363991837 210246664235729761496939)
        ·
          refine ⟨315369996353594642245409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210246664235729761496939 315369996353594642245409)
          ·
            refine ⟨236527497265195981684057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315369996353594642245409 236527497265195981684057)
            ·
              refine ⟨177395622948896986263043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236527497265195981684057 177395622948896986263043)
              ·
                refine ⟨266093434423345479394565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177395622948896986263043 266093434423345479394565)
                ·
                  refine ⟨49892518954377277386481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266093434423345479394565 49892518954377277386481)
                  ·
                    rfl

theorem cell21_218622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_218622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218622 prefixEnd_218622 := by exact prefixLift 218622
  have htrace : WordTrace (prefixWord ++ tailWord_218622) baseStart_218622 baseEnd_218622 := by
    simpa [prefixWord, tailWord_218622, baseEnd_218622] using wordTrace_append hprefix tailTrace_218622
  have hstable : (prefixWord ++ tailWord_218622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218622).length < 2 ^ (prefixWord ++ tailWord_218622).sum := by decide
  have hdescent : baseEnd_218622 < baseStart_218622 := by decide
  rcases family_descends (prefixWord ++ tailWord_218622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218664 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_218664 : Nat := 118140960795 + 218664 * 2 ^ 59
def prefixEnd_218664 : Nat := 4983230072969 + 3 ^ 40 * 218664 * 2
def baseEnd_218664 : Nat := 49902103926594537686395

theorem tailTrace_218664 : CollatzResearch.WordTrace tailWord_218664 prefixEnd_218664 49902103926594537686395 := by
  unfold tailWord_218664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987665639912573841567523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5316887519883431788756697 3987665639912573841567523)
  ·
    refine ⟨5981498459868860762351285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987665639912573841567523 5981498459868860762351285)
    ·
      refine ⟨560765480612705696470433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5981498459868860762351285 560765480612705696470433)
      ·
        refine ⟨420574110459529272352825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560765480612705696470433 420574110459529272352825)
        ·
          refine ⟨315430582844646954264619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420574110459529272352825 315430582844646954264619)
          ·
            refine ⟨473145874266970431396929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315430582844646954264619 473145874266970431396929)
            ·
              refine ⟨354859405700227823547697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473145874266970431396929 354859405700227823547697)
              ·
                refine ⟨266144554275170867660773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354859405700227823547697 266144554275170867660773)
                ·
                  refine ⟨49902103926594537686395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266144554275170867660773 49902103926594537686395)
                  ·
                    rfl

theorem cell21_218664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_218664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218664 prefixEnd_218664 := by exact prefixLift 218664
  have htrace : WordTrace (prefixWord ++ tailWord_218664) baseStart_218664 baseEnd_218664 := by
    simpa [prefixWord, tailWord_218664, baseEnd_218664] using wordTrace_append hprefix tailTrace_218664
  have hstable : (prefixWord ++ tailWord_218664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218664).length < 2 ^ (prefixWord ++ tailWord_218664).sum := by decide
  have hdescent : baseEnd_218664 < baseStart_218664 := by decide
  rcases family_descends (prefixWord ++ tailWord_218664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218723 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_218723 : Nat := 118140960795 + 218723 * 2 ^ 59
def prefixEnd_218723 : Nat := 4983230072969 + 3 ^ 40 * 218723 * 2
def baseEnd_218723 : Nat := 49915568530423546202941

theorem tailTrace_218723 : CollatzResearch.WordTrace tailWord_218723 prefixEnd_218723 49915568530423546202941 := by
  unfold tailWord_218723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977483186611400759532823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5318322124407600506355215 7977483186611400759532823)
  ·
    refine ⟨11966224779917101139299235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7977483186611400759532823 11966224779917101139299235)
    ·
      refine ⟨17949337169875651708948853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11966224779917101139299235 17949337169875651708948853)
      ·
        refine ⟨1682750359675842347713955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17949337169875651708948853 1682750359675842347713955)
        ·
          refine ⟨2524125539513763521570933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682750359675842347713955 2524125539513763521570933)
          ·
            refine ⟨236636769329415330147275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2524125539513763521570933 236636769329415330147275)
            ·
              refine ⟨354955153994122995220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236636769329415330147275 354955153994122995220913)
              ·
                refine ⟨266216365495592246415685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354955153994122995220913 266216365495592246415685)
                ·
                  refine ⟨49915568530423546202941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266216365495592246415685 49915568530423546202941)
                  ·
                    rfl

theorem cell21_218723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_218723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218723 prefixEnd_218723 := by exact prefixLift 218723
  have htrace : WordTrace (prefixWord ++ tailWord_218723) baseStart_218723 baseEnd_218723 := by
    simpa [prefixWord, tailWord_218723, baseEnd_218723] using wordTrace_append hprefix tailTrace_218723
  have hstable : (prefixWord ++ tailWord_218723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218723).length < 2 ^ (prefixWord ++ tailWord_218723).sum := by decide
  have hdescent : baseEnd_218723 < baseStart_218723 := by decide
  rcases family_descends (prefixWord ++ tailWord_218723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218858 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_218858 : Nat := 118140960795 + 218858 * 2 ^ 59
def prefixEnd_218858 : Nat := 4983230072969 + 3 ^ 40 * 218858 * 2
def baseEnd_218858 : Nat := 49946377369693311452665

theorem tailTrace_218858 : CollatzResearch.WordTrace tailWord_218858 prefixEnd_218858 49946377369693311452665 := by
  unfold tailWord_218858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995601760280579703924307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5321604694081545877131485 1995601760280579703924307)
  ·
    refine ⟨2993402640420869555886461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995601760280579703924307 2993402640420869555886461)
    ·
      refine ⟨1122525990157826083457423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2993402640420869555886461 1122525990157826083457423)
      ·
        refine ⟨1683788985236739125186135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122525990157826083457423 1683788985236739125186135)
        ·
          refine ⟨2525683477855108687779203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683788985236739125186135 2525683477855108687779203)
          ·
            refine ⟨3788525216782663031668805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525683477855108687779203 3788525216782663031668805)
            ·
              refine ⟨710348478146749318437901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3788525216782663031668805 710348478146749318437901)
              ·
                refine ⟨266380679305030994414213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710348478146749318437901 266380679305030994414213)
                ·
                  refine ⟨49946377369693311452665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266380679305030994414213 49946377369693311452665)
                  ·
                    rfl

theorem cell21_218858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_218858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218858 prefixEnd_218858 := by exact prefixLift 218858
  have htrace : WordTrace (prefixWord ++ tailWord_218858) baseStart_218858 baseEnd_218858 := by
    simpa [prefixWord, tailWord_218858, baseEnd_218858] using wordTrace_append hprefix tailTrace_218858
  have hstable : (prefixWord ++ tailWord_218858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218858).length < 2 ^ (prefixWord ++ tailWord_218858).sum := by decide
  have hdescent : baseEnd_218858 < baseStart_218858 := by decide
  rcases family_descends (prefixWord ++ tailWord_218858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218878 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_218878 : Nat := 118140960795 + 218878 * 2 ^ 59
def prefixEnd_218878 : Nat := 4983230072969 + 3 ^ 40 * 218878 * 2
def baseEnd_218878 : Nat := 49950941642177721119291

theorem tailTrace_218878 : CollatzResearch.WordTrace tailWord_218878 prefixEnd_218878 49950941642177721119291 := by
  unfold tailWord_218878
  simp only [CollatzResearch.WordTrace]
  refine ⟨997892062631232778928161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5322091000699908154283525 997892062631232778928161)
  ·
    refine ⟨748419046973424584196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 997892062631232778928161 748419046973424584196121)
    ·
      refine ⟨561314285230068438147091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748419046973424584196121 561314285230068438147091)
      ·
        refine ⟨841971427845102657220637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561314285230068438147091 841971427845102657220637)
        ·
          refine ⟨315739285441913496457739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841971427845102657220637 315739285441913496457739)
          ·
            refine ⟨473608928162870244686609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315739285441913496457739 473608928162870244686609)
            ·
              refine ⟨355206696122152683514957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473608928162870244686609 355206696122152683514957)
              ·
                refine ⟨133202511045807256318109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355206696122152683514957 133202511045807256318109)
                ·
                  refine ⟨49950941642177721119291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133202511045807256318109 49950941642177721119291)
                  ·
                    rfl

theorem cell21_218878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_218878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218878 prefixEnd_218878 := by exact prefixLift 218878
  have htrace : WordTrace (prefixWord ++ tailWord_218878) baseStart_218878 baseEnd_218878 := by
    simpa [prefixWord, tailWord_218878, baseEnd_218878] using wordTrace_append hprefix tailTrace_218878
  have hstable : (prefixWord ++ tailWord_218878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218878).length < 2 ^ (prefixWord ++ tailWord_218878).sum := by decide
  have hdescent : baseEnd_218878 < baseStart_218878 := by decide
  rcases family_descends (prefixWord ++ tailWord_218878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218903 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_218903 : Nat := 118140960795 + 218903 * 2 ^ 59
def prefixEnd_218903 : Nat := 4983230072969 + 3 ^ 40 * 218903 * 2
def baseEnd_218903 : Nat := 49956646982783233202573

theorem tailTrace_218903 : CollatzResearch.WordTrace tailWord_218903 prefixEnd_218903 49956646982783233202573 := by
  unfold tailWord_218903
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984048325959291501085363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5322698883972861000723575 7984048325959291501085363)
  ·
    refine ⟨11976072488938937251628045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7984048325959291501085363 11976072488938937251628045)
    ·
      refine ⟨4491027183352101469360517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11976072488938937251628045 4491027183352101469360517)
      ·
        refine ⟨842067596878519025505097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4491027183352101469360517 842067596878519025505097)
        ·
          refine ⟨631550697658889269128823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842067596878519025505097 631550697658889269128823)
          ·
            refine ⟨947326046488333903693235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631550697658889269128823 947326046488333903693235)
            ·
              refine ⟨1420989069732500855539853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947326046488333903693235 1420989069732500855539853)
              ·
                refine ⟨532870901149687820827445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420989069732500855539853 532870901149687820827445)
                ·
                  refine ⟨49956646982783233202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532870901149687820827445 49956646982783233202573)
                  ·
                    rfl

theorem cell21_218903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_218903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_218903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_218903 prefixEnd_218903 := by exact prefixLift 218903
  have htrace : WordTrace (prefixWord ++ tailWord_218903) baseStart_218903 baseEnd_218903 := by
    simpa [prefixWord, tailWord_218903, baseEnd_218903] using wordTrace_append hprefix tailTrace_218903
  have hstable : (prefixWord ++ tailWord_218903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218903).length < 2 ^ (prefixWord ++ tailWord_218903).sum := by decide
  have hdescent : baseEnd_218903 < baseStart_218903 := by decide
  rcases family_descends (prefixWord ++ tailWord_218903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219030 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_219030 : Nat := 118140960795 + 219030 * 2 ^ 59
def prefixEnd_219030 : Nat := 4983230072969 + 3 ^ 40 * 219030 * 2
def baseEnd_219030 : Nat := 49985630113059234585647

theorem tailTrace_219030 : CollatzResearch.WordTrace tailWord_219030 prefixEnd_219030 49985630113059234585647 := by
  unfold tailWord_219030
  simp only [CollatzResearch.WordTrace]
  refine ⟨499292524781199511934909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5325786930999461460639029 499292524781199511934909)
  ·
    refine ⟨187234696792949816975591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 499292524781199511934909 187234696792949816975591)
    ·
      refine ⟨280852045189424725463387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187234696792949816975591 280852045189424725463387)
      ·
        refine ⟨421278067784137088195081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280852045189424725463387 421278067784137088195081)
        ·
          refine ⟨315958550838102816146311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421278067784137088195081 315958550838102816146311)
          ·
            refine ⟨473937826257154224219467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315958550838102816146311 473937826257154224219467)
            ·
              refine ⟨710906739385731336329201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473937826257154224219467 710906739385731336329201)
              ·
                refine ⟨533180054539298502246901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710906739385731336329201 533180054539298502246901)
                ·
                  refine ⟨49985630113059234585647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533180054539298502246901 49985630113059234585647)
                  ·
                    rfl

theorem cell21_219030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_219030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219030 prefixEnd_219030 := by exact prefixLift 219030
  have htrace : WordTrace (prefixWord ++ tailWord_219030) baseStart_219030 baseEnd_219030 := by
    simpa [prefixWord, tailWord_219030, baseEnd_219030] using wordTrace_append hprefix tailTrace_219030
  have hstable : (prefixWord ++ tailWord_219030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219030).length < 2 ^ (prefixWord ++ tailWord_219030).sum := by decide
  have hdescent : baseEnd_219030 < baseStart_219030 := by decide
  rcases family_descends (prefixWord ++ tailWord_219030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219083 : List Nat := [1, 1, 1, 1, 3, 4, 2, 8]
def baseStart_219083 : Nat := 118140960795 + 219083 * 2 ^ 59
def prefixEnd_219083 : Nat := 4983230072969 + 3 ^ 40 * 219083 * 2
def baseEnd_219083 : Nat := 16665908478380973400735

theorem tailTrace_219083 : CollatzResearch.WordTrace tailWord_219083 prefixEnd_219083 16665908478380973400735 := by
  unfold tailWord_219083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990613465307182242637903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327075643538121495091935 7990613465307182242637903)
  ·
    refine ⟨11985920197960773363956855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990613465307182242637903 11985920197960773363956855)
    ·
      refine ⟨17978880296941160045935283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11985920197960773363956855 17978880296941160045935283)
      ·
        refine ⟨26968320445411740068902925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17978880296941160045935283 26968320445411740068902925)
        ·
          refine ⟨10113120167029402525838597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26968320445411740068902925 10113120167029402525838597)
          ·
            refine ⟨1896210031318012973594737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10113120167029402525838597 1896210031318012973594737)
            ·
              refine ⟨1422157523488509730196053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896210031318012973594737 1422157523488509730196053)
              ·
                refine ⟨16665908478380973400735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1422157523488509730196053 16665908478380973400735)
                ·
                  rfl

theorem cell21_219083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_219083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219083 prefixEnd_219083 := by exact prefixLift 219083
  have htrace : WordTrace (prefixWord ++ tailWord_219083) baseStart_219083 baseEnd_219083 := by
    simpa [prefixWord, tailWord_219083, baseEnd_219083] using wordTrace_append hprefix tailTrace_219083
  have hstable : (prefixWord ++ tailWord_219083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219083).length < 2 ^ (prefixWord ++ tailWord_219083).sum := by decide
  have hdescent : baseEnd_219083 < baseStart_219083 := by decide
  rcases family_descends (prefixWord ++ tailWord_219083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219131 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 3]
def baseStart_219131 : Nat := 118140960795 + 219131 * 2 ^ 59
def prefixEnd_219131 : Nat := 4983230072969 + 3 ^ 40 * 219131 * 2
def baseEnd_219131 : Nat := 50008679689105503402107

theorem tailTrace_219131 : CollatzResearch.WordTrace tailWord_219131 prefixEnd_219131 50008679689105503402107 := by
  unfold tailWord_219131
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992364169133286440385247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5328242779422190960256831 7992364169133286440385247)
  ·
    refine ⟨11988546253699929660577871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992364169133286440385247 11988546253699929660577871)
    ·
      refine ⟨17982819380549894490866807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11988546253699929660577871 17982819380549894490866807)
      ·
        refine ⟨26974229070824841736300211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17982819380549894490866807 26974229070824841736300211)
        ·
          refine ⟨40461343606237262604450317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974229070824841736300211 40461343606237262604450317)
          ·
            refine ⟨15173003852338973476668869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40461343606237262604450317 15173003852338973476668869)
            ·
              refine ⟨2844938222313557526875413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15173003852338973476668869 2844938222313557526875413)
              ·
                refine ⟨133356479170948009072285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2844938222313557526875413 133356479170948009072285)
                ·
                  refine ⟨50008679689105503402107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133356479170948009072285 50008679689105503402107)
                  ·
                    rfl

theorem cell21_219131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].length) (baseStart_219131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219131 prefixEnd_219131 := by exact prefixLift 219131
  have htrace : WordTrace (prefixWord ++ tailWord_219131) baseStart_219131 baseEnd_219131 := by
    simpa [prefixWord, tailWord_219131, baseEnd_219131] using wordTrace_append hprefix tailTrace_219131
  have hstable : (prefixWord ++ tailWord_219131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219131).length < 2 ^ (prefixWord ++ tailWord_219131).sum := by decide
  have hdescent : baseEnd_219131 < baseStart_219131 := by decide
  rcases family_descends (prefixWord ++ tailWord_219131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219176 : List Nat := [2, 1, 5, 3, 10]
def baseStart_219176 : Nat := 118140960795 + 219176 * 2 ^ 59
def prefixEnd_219176 : Nat := 4983230072969 + 3 ^ 40 * 219176 * 2
def baseEnd_219176 : Nat := 617517892619696606815

theorem tailTrace_219176 : CollatzResearch.WordTrace tailWord_219176 prefixEnd_219176 617517892619696606815 := by
  unfold tailWord_219176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997002726985129562886691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5329336969313506083848921 3997002726985129562886691)
  ·
    refine ⟨5995504090477694344330037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997002726985129562886691 5995504090477694344330037)
    ·
      refine ⟨562078508482283844780941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5995504090477694344330037 562078508482283844780941)
      ·
        refine ⟨210779440680856441792853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562078508482283844780941 210779440680856441792853)
        ·
          refine ⟨617517892619696606815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 210779440680856441792853 617517892619696606815)
          ·
            rfl

theorem cell21_219176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 10].length) (baseStart_219176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219176 prefixEnd_219176 := by exact prefixLift 219176
  have htrace : WordTrace (prefixWord ++ tailWord_219176) baseStart_219176 baseEnd_219176 := by
    simpa [prefixWord, tailWord_219176, baseEnd_219176] using wordTrace_append hprefix tailTrace_219176
  have hstable : (prefixWord ++ tailWord_219176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219176).length < 2 ^ (prefixWord ++ tailWord_219176).sum := by decide
  have hdescent : baseEnd_219176 < baseStart_219176 := by decide
  rcases family_descends (prefixWord ++ tailWord_219176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219182 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_219182 : Nat := 118140960795 + 219182 * 2 ^ 59
def prefixEnd_219182 : Nat := 4983230072969 + 3 ^ 40 * 219182 * 2
def baseEnd_219182 : Nat := 50020318583940748052003

theorem tailTrace_219182 : CollatzResearch.WordTrace tailWord_219182 prefixEnd_219182 50020318583940748052003 := by
  unfold tailWord_219182
  simp only [CollatzResearch.WordTrace]
  refine ⟨999278036493565268811475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5329482861299014766994533 999278036493565268811475)
  ·
    refine ⟨1498917054740347903217213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 999278036493565268811475 1498917054740347903217213)
    ·
      refine ⟨562093895527630463706455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1498917054740347903217213 562093895527630463706455)
      ·
        refine ⟨843140843291445695559683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562093895527630463706455 843140843291445695559683)
        ·
          refine ⟨1264711264937168543339525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843140843291445695559683 1264711264937168543339525)
          ·
            refine ⟨237133362175719101876161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1264711264937168543339525 237133362175719101876161)
            ·
              refine ⟨177850021631789326407121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237133362175719101876161 177850021631789326407121)
              ·
                refine ⟨133387516223841994805341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177850021631789326407121 133387516223841994805341)
                ·
                  refine ⟨50020318583940748052003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133387516223841994805341 50020318583940748052003)
                  ·
                    rfl

theorem cell21_219182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_219182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219182 prefixEnd_219182 := by exact prefixLift 219182
  have htrace : WordTrace (prefixWord ++ tailWord_219182) baseStart_219182 baseEnd_219182 := by
    simpa [prefixWord, tailWord_219182, baseEnd_219182] using wordTrace_append hprefix tailTrace_219182
  have hstable : (prefixWord ++ tailWord_219182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219182).length < 2 ^ (prefixWord ++ tailWord_219182).sum := by decide
  have hdescent : baseEnd_219182 < baseStart_219182 := by decide
  rcases family_descends (prefixWord ++ tailWord_219182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219193 : List Nat := [1, 2, 1, 5, 3, 2, 1, 6]
def baseStart_219193 : Nat := 118140960795 + 219193 * 2 ^ 59
def prefixEnd_219193 : Nat := 4983230072969 + 3 ^ 40 * 219193 * 2
def baseEnd_219193 : Nat := 16674276311269057789549

theorem tailTrace_219193 : CollatzResearch.WordTrace tailWord_219193 prefixEnd_219193 16674276311269057789549 := by
  unfold tailWord_219193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994625494908671029142233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329750329939114019428155 7994625494908671029142233)
  ·
    refine ⟨5995969121181503271856675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7994625494908671029142233 5995969121181503271856675)
    ·
      refine ⟨8993953681772254907785013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5995969121181503271856675 8993953681772254907785013)
      ·
        refine ⟨843183157666148897604845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8993953681772254907785013 843183157666148897604845)
        ·
          refine ⟨316193684124805836601817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 843183157666148897604845 316193684124805836601817)
          ·
            refine ⟨237145263093604377451363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316193684124805836601817 237145263093604377451363)
            ·
              refine ⟨355717894640406566177045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237145263093604377451363 355717894640406566177045)
              ·
                refine ⟨16674276311269057789549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355717894640406566177045 16674276311269057789549)
                ·
                  rfl

theorem cell21_219193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_219193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219193 prefixEnd_219193 := by exact prefixLift 219193
  have htrace : WordTrace (prefixWord ++ tailWord_219193) baseStart_219193 baseEnd_219193 := by
    simpa [prefixWord, tailWord_219193, baseEnd_219193] using wordTrace_append hprefix tailTrace_219193
  have hstable : (prefixWord ++ tailWord_219193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219193).length < 2 ^ (prefixWord ++ tailWord_219193).sum := by decide
  have hdescent : baseEnd_219193 < baseStart_219193 := by decide
  rcases family_descends (prefixWord ++ tailWord_219193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219224 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_219224 : Nat := 118140960795 + 219224 * 2 ^ 59
def prefixEnd_219224 : Nat := 4983230072969 + 3 ^ 40 * 219224 * 2
def baseEnd_219224 : Nat := 50029903556158008351917

theorem tailTrace_219224 : CollatzResearch.WordTrace tailWord_219224 prefixEnd_219224 50029903556158008351917 := by
  unfold tailWord_219224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997878078898181661760363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5330504105197575549013817 3997878078898181661760363)
  ·
    refine ⟨5996817118347272492640545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997878078898181661760363 5996817118347272492640545)
    ·
      refine ⟨4497612838760454369480409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996817118347272492640545 4497612838760454369480409)
      ·
        refine ⟨3373209629070340777110307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4497612838760454369480409 3373209629070340777110307)
        ·
          refine ⟨5059814443605511165665461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373209629070340777110307 5059814443605511165665461)
          ·
            refine ⟨474357604088016671781137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5059814443605511165665461 474357604088016671781137)
            ·
              refine ⟨355768203066012503835853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474357604088016671781137 355768203066012503835853)
              ·
                refine ⟨133413076149754688938445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355768203066012503835853 133413076149754688938445)
                ·
                  refine ⟨50029903556158008351917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133413076149754688938445 50029903556158008351917)
                  ·
                    rfl

theorem cell21_219224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_219224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219224 prefixEnd_219224 := by exact prefixLift 219224
  have htrace : WordTrace (prefixWord ++ tailWord_219224) baseStart_219224 baseEnd_219224 := by
    simpa [prefixWord, tailWord_219224, baseEnd_219224] using wordTrace_append hprefix tailTrace_219224
  have hstable : (prefixWord ++ tailWord_219224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219224).length < 2 ^ (prefixWord ++ tailWord_219224).sum := by decide
  have hdescent : baseEnd_219224 < baseStart_219224 := by decide
  rcases family_descends (prefixWord ++ tailWord_219224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219230 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_219230 : Nat := 118140960795 + 219230 * 2 ^ 59
def prefixEnd_219230 : Nat := 4983230072969 + 3 ^ 40 * 219230 * 2
def baseEnd_219230 : Nat := 50031272837903331251905

theorem tailTrace_219230 : CollatzResearch.WordTrace tailWord_219230 prefixEnd_219230 50031272837903331251905 := by
  unfold tailWord_219230
  simp only [CollatzResearch.WordTrace]
  refine ⟨999496874471828293529893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5330649997183084232159429 999496874471828293529893)
  ·
    refine ⟨187405663963467805036855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 999496874471828293529893 187405663963467805036855)
    ·
      refine ⟨281108495945201707555283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187405663963467805036855 281108495945201707555283)
      ·
        refine ⟨421662743917802561332925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281108495945201707555283 421662743917802561332925)
        ·
          refine ⟨158123528969175960499847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421662743917802561332925 158123528969175960499847)
          ·
            refine ⟨237185293453763940749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158123528969175960499847 237185293453763940749771)
            ·
              refine ⟨355777940180645911124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237185293453763940749771 355777940180645911124657)
              ·
                refine ⟨266833455135484433343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355777940180645911124657 266833455135484433343493)
                ·
                  refine ⟨50031272837903331251905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266833455135484433343493 50031272837903331251905)
                  ·
                    rfl

theorem cell21_219230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_219230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219230 prefixEnd_219230 := by exact prefixLift 219230
  have htrace : WordTrace (prefixWord ++ tailWord_219230) baseStart_219230 baseEnd_219230 := by
    simpa [prefixWord, tailWord_219230, baseEnd_219230] using wordTrace_append hprefix tailTrace_219230
  have hstable : (prefixWord ++ tailWord_219230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219230).length < 2 ^ (prefixWord ++ tailWord_219230).sum := by decide
  have hdescent : baseEnd_219230 < baseStart_219230 := by decide
  rcases family_descends (prefixWord ++ tailWord_219230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219269 : List Nat := [1, 3, 1, 1, 5, 3, 2, 5]
def baseStart_219269 : Nat := 118140960795 + 219269 * 2 ^ 59
def prefixEnd_219269 : Nat := 4983230072969 + 3 ^ 40 * 219269 * 2
def baseEnd_219269 : Nat := 16680057723082643367275

theorem tailTrace_219269 : CollatzResearch.WordTrace tailWord_219269 prefixEnd_219269 16680057723082643367275 := by
  unfold tailWord_219269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997397442633336008908861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5331598295088890672605907 7997397442633336008908861)
  ·
    refine ⟨2999024040987501003340823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7997397442633336008908861 2999024040987501003340823)
    ·
      refine ⟨4498536061481251505011235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2999024040987501003340823 4498536061481251505011235)
      ·
        refine ⟨6747804092221877257516853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498536061481251505011235 6747804092221877257516853)
        ·
          refine ⟨632606633645800992892205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6747804092221877257516853 632606633645800992892205)
          ·
            refine ⟨237227487617175372334577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632606633645800992892205 237227487617175372334577)
            ·
              refine ⟨177920615712881529250933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237227487617175372334577 177920615712881529250933)
              ·
                refine ⟨16680057723082643367275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177920615712881529250933 16680057723082643367275)
                ·
                  rfl

theorem cell21_219269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].length) (baseStart_219269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219269 prefixEnd_219269 := by exact prefixLift 219269
  have htrace : WordTrace (prefixWord ++ tailWord_219269) baseStart_219269 baseEnd_219269 := by
    simpa [prefixWord, tailWord_219269, baseEnd_219269] using wordTrace_append hprefix tailTrace_219269
  have hstable : (prefixWord ++ tailWord_219269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219269).length < 2 ^ (prefixWord ++ tailWord_219269).sum := by decide
  have hdescent : baseEnd_219269 < baseStart_219269 := by decide
  rcases family_descends (prefixWord ++ tailWord_219269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219280 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_219280 : Nat := 118140960795 + 219280 * 2 ^ 59
def prefixEnd_219280 : Nat := 4983230072969 + 3 ^ 40 * 219280 * 2
def baseEnd_219280 : Nat := 50042683519114355418469

theorem tailTrace_219280 : CollatzResearch.WordTrace tailWord_219280 prefixEnd_219280 50042683519114355418469 := by
  unfold tailWord_219280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998899322796742443779647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5331865763728989925039529 3998899322796742443779647)
  ·
    refine ⟨5998348984195113665669471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998899322796742443779647 5998348984195113665669471)
    ·
      refine ⟨8997523476292670498504207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998348984195113665669471 8997523476292670498504207)
      ·
        refine ⟨13496285214439005747756311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997523476292670498504207 13496285214439005747756311)
        ·
          refine ⟨20244427821658508621634467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13496285214439005747756311 20244427821658508621634467)
          ·
            refine ⟨30366641732487762932451701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20244427821658508621634467 30366641732487762932451701)
            ·
              refine ⟨2846872662420727774917347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30366641732487762932451701 2846872662420727774917347)
              ·
                refine ⟨4270308993631091662376021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846872662420727774917347 4270308993631091662376021)
                ·
                  refine ⟨50042683519114355418469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4270308993631091662376021 50042683519114355418469)
                  ·
                    rfl

theorem cell21_219280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_219280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219280 prefixEnd_219280 := by exact prefixLift 219280
  have htrace : WordTrace (prefixWord ++ tailWord_219280) baseStart_219280 baseEnd_219280 := by
    simpa [prefixWord, tailWord_219280, baseEnd_219280] using wordTrace_append hprefix tailTrace_219280
  have hstable : (prefixWord ++ tailWord_219280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219280).length < 2 ^ (prefixWord ++ tailWord_219280).sum := by decide
  have hdescent : baseEnd_219280 < baseStart_219280 := by decide
  rcases family_descends (prefixWord ++ tailWord_219280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219297 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_219297 : Nat := 118140960795 + 219297 * 2 ^ 59
def prefixEnd_219297 : Nat := 4983230072969 + 3 ^ 40 * 219297 * 2
def baseEnd_219297 : Nat := 50046563150726103635101

theorem tailTrace_219297 : CollatzResearch.WordTrace tailWord_219297 prefixEnd_219297 50046563150726103635101 := by
  unfold tailWord_219297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998418686531896790928145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5332279124354597860618763 7998418686531896790928145)
  ·
    refine ⟨5998814014898922593196109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7998418686531896790928145 5998814014898922593196109)
    ·
      refine ⟨2249555255587095972448541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5998814014898922593196109 2249555255587095972448541)
      ·
        refine ⟨843583220845160989668203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2249555255587095972448541 843583220845160989668203)
        ·
          refine ⟨1265374831267741484502305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843583220845160989668203 1265374831267741484502305)
          ·
            refine ⟨949031123450806113376729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265374831267741484502305 949031123450806113376729)
            ·
              refine ⟨711773342588104585032547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949031123450806113376729 711773342588104585032547)
              ·
                refine ⟨1067660013882156877548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711773342588104585032547 1067660013882156877548821)
                ·
                  refine ⟨50046563150726103635101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1067660013882156877548821 50046563150726103635101)
                  ·
                    rfl

theorem cell21_219297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_219297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219297 prefixEnd_219297 := by exact prefixLift 219297
  have htrace : WordTrace (prefixWord ++ tailWord_219297) baseStart_219297 baseEnd_219297 := by
    simpa [prefixWord, tailWord_219297, baseEnd_219297] using wordTrace_append hprefix tailTrace_219297
  have hstable : (prefixWord ++ tailWord_219297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219297).length < 2 ^ (prefixWord ++ tailWord_219297).sum := by decide
  have hdescent : baseEnd_219297 < baseStart_219297 := by decide
  rcases family_descends (prefixWord ++ tailWord_219297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219300 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_219300 : Nat := 118140960795 + 219300 * 2 ^ 59
def prefixEnd_219300 : Nat := 4983230072969 + 3 ^ 40 * 219300 * 2
def baseEnd_219300 : Nat := 50047247791598765085095

theorem tailTrace_219300 : CollatzResearch.WordTrace tailWord_219300 prefixEnd_219300 50047247791598765085095 := by
  unfold tailWord_219300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999264052760514151643677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5332352070347352202191569 3999264052760514151643677)
  ·
    refine ⟨1499724019785192806866379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3999264052760514151643677 1499724019785192806866379)
    ·
      refine ⟨2249586029677789210299569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499724019785192806866379 2249586029677789210299569)
      ·
        refine ⟨1687189522258341907724677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2249586029677789210299569 1687189522258341907724677)
        ·
          refine ⟨316348035423439107698377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1687189522258341907724677 316348035423439107698377)
          ·
            refine ⟨237261026567579330773783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316348035423439107698377 237261026567579330773783)
            ·
              refine ⟨355891539851368996160675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237261026567579330773783 355891539851368996160675)
              ·
                refine ⟨533837309777053494241013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355891539851368996160675 533837309777053494241013)
                ·
                  refine ⟨50047247791598765085095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533837309777053494241013 50047247791598765085095)
                  ·
                    rfl

theorem cell21_219300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_219300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219300 prefixEnd_219300 := by exact prefixLift 219300
  have htrace : WordTrace (prefixWord ++ tailWord_219300) baseStart_219300 baseEnd_219300 := by
    simpa [prefixWord, tailWord_219300, baseEnd_219300] using wordTrace_append hprefix tailTrace_219300
  have hstable : (prefixWord ++ tailWord_219300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219300).length < 2 ^ (prefixWord ++ tailWord_219300).sum := by decide
  have hdescent : baseEnd_219300 < baseStart_219300 := by decide
  rcases family_descends (prefixWord ++ tailWord_219300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219449 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_219449 : Nat := 118140960795 + 219449 * 2 ^ 59
def prefixEnd_219449 : Nat := 4983230072969 + 3 ^ 40 * 219449 * 2
def baseEnd_219449 : Nat := 50081251621607617101457

theorem tailTrace_219449 : CollatzResearch.WordTrace tailWord_219449 prefixEnd_219449 50081251621607617101457 := by
  unfold tailWord_219449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003962581981226750461401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5335975054654151166974267 8003962581981226750461401)
  ·
    refine ⟨6002971936485920062846051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8003962581981226750461401 6002971936485920062846051)
    ·
      refine ⟨9004457904728880094269077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002971936485920062846051 9004457904728880094269077)
      ·
        refine ⟨422083964284166254418863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9004457904728880094269077 422083964284166254418863)
        ·
          refine ⟨633125946426249381628295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422083964284166254418863 633125946426249381628295)
          ·
            refine ⟨949688919639374072442443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633125946426249381628295 949688919639374072442443)
            ·
              refine ⟨1424533379459061108663665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949688919639374072442443 1424533379459061108663665)
              ·
                refine ⟨1068400034594295831497749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424533379459061108663665 1068400034594295831497749)
                ·
                  refine ⟨50081251621607617101457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1068400034594295831497749 50081251621607617101457)
                  ·
                    rfl

theorem cell21_219449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_219449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219449 prefixEnd_219449 := by exact prefixLift 219449
  have htrace : WordTrace (prefixWord ++ tailWord_219449) baseStart_219449 baseEnd_219449 := by
    simpa [prefixWord, tailWord_219449, baseEnd_219449] using wordTrace_append hprefix tailTrace_219449
  have hstable : (prefixWord ++ tailWord_219449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219449).length < 2 ^ (prefixWord ++ tailWord_219449).sum := by decide
  have hdescent : baseEnd_219449 < baseStart_219449 := by decide
  rcases family_descends (prefixWord ++ tailWord_219449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219615 : List Nat := [1, 1, 2, 3, 3, 3, 1, 7]
def baseStart_219615 : Nat := 118140960795 + 219615 * 2 ^ 59
def prefixEnd_219615 : Nat := 4983230072969 + 3 ^ 40 * 219615 * 2
def baseEnd_219615 : Nat := 16706378361076072444817

theorem tailTrace_219615 : CollatzResearch.WordTrace tailWord_219615 prefixEnd_219615 16706378361076072444817 := by
  unfold tailWord_219615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010017099379837101004299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5340011399586558067336199 8010017099379837101004299)
  ·
    refine ⟨12015025649069755651506449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8010017099379837101004299 12015025649069755651506449)
    ·
      refine ⟨9011269236802316738629837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015025649069755651506449 9011269236802316738629837)
      ·
        refine ⟨3379225963800868776986189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9011269236802316738629837 3379225963800868776986189)
        ·
          refine ⟨1267209736425325791369821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3379225963800868776986189 1267209736425325791369821)
          ·
            refine ⟨475203651159497171763683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267209736425325791369821 475203651159497171763683)
            ·
              refine ⟨712805476739245757645525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475203651159497171763683 712805476739245757645525)
              ·
                refine ⟨16706378361076072444817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 712805476739245757645525 16706378361076072444817)
                ·
                  rfl

theorem cell21_219615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_219615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219615 prefixEnd_219615 := by exact prefixLift 219615
  have htrace : WordTrace (prefixWord ++ tailWord_219615) baseStart_219615 baseEnd_219615 := by
    simpa [prefixWord, tailWord_219615, baseEnd_219615] using wordTrace_append hprefix tailTrace_219615
  have hstable : (prefixWord ++ tailWord_219615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219615).length < 2 ^ (prefixWord ++ tailWord_219615).sum := by decide
  have hdescent : baseEnd_219615 < baseStart_219615 := by decide
  rcases family_descends (prefixWord ++ tailWord_219615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219621 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 3]
def baseStart_219621 : Nat := 118140960795 + 219621 * 2 ^ 59
def prefixEnd_219621 : Nat := 4983230072969 + 3 ^ 40 * 219621 * 2
def baseEnd_219621 : Nat := 50120504364973540234439

theorem tailTrace_219621 : CollatzResearch.WordTrace tailWord_219621 prefixEnd_219621 50120504364973540234439 := by
  unfold tailWord_219621
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010235937358100125722717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5340157291572066750481811 8010235937358100125722717)
  ·
    refine ⟨3003838476509287547146019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8010235937358100125722717 3003838476509287547146019)
    ·
      refine ⟨4505757714763931320719029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003838476509287547146019 4505757714763931320719029)
      ·
        refine ⟨422414785759118561317409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4505757714763931320719029 422414785759118561317409)
        ·
          refine ⟨316811089319338920988057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422414785759118561317409 316811089319338920988057)
          ·
            refine ⟨237608316989504190741043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316811089319338920988057 237608316989504190741043)
            ·
              refine ⟨356412475484256286111565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237608316989504190741043 356412475484256286111565)
              ·
                refine ⟨133654678306596107291837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356412475484256286111565 133654678306596107291837)
                ·
                  refine ⟨50120504364973540234439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133654678306596107291837 50120504364973540234439)
                  ·
                    rfl

theorem cell21_219621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_219621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219621 prefixEnd_219621 := by exact prefixLift 219621
  have htrace : WordTrace (prefixWord ++ tailWord_219621) baseStart_219621 baseEnd_219621 := by
    simpa [prefixWord, tailWord_219621, baseEnd_219621] using wordTrace_append hprefix tailTrace_219621
  have hstable : (prefixWord ++ tailWord_219621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219621).length < 2 ^ (prefixWord ++ tailWord_219621).sum := by decide
  have hdescent : baseEnd_219621 < baseStart_219621 := by decide
  rcases family_descends (prefixWord ++ tailWord_219621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219708 : List Nat := [2, 2, 2, 2, 3, 3, 1, 6]
def baseStart_219708 : Nat := 118140960795 + 219708 * 2 ^ 59
def prefixEnd_219708 : Nat := 4983230072969 + 3 ^ 40 * 219708 * 2
def baseEnd_219708 : Nat := 16713452983426907428087

theorem tailTrace_219708 : CollatzResearch.WordTrace tailWord_219708 prefixEnd_219708 16713452983426907428087 := by
  unfold tailWord_219708
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006704544021456992069889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5342272725361942656093185 4006704544021456992069889)
  ·
    refine ⟨3005028408016092744052417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4006704544021456992069889 3005028408016092744052417)
    ·
      refine ⟨2253771306012069558039313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3005028408016092744052417 2253771306012069558039313)
      ·
        refine ⟨1690328479509052168529485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253771306012069558039313 1690328479509052168529485)
        ·
          refine ⟨633873179815894563198557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1690328479509052168529485 633873179815894563198557)
          ·
            refine ⟨237702442430960461199459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633873179815894563198557 237702442430960461199459)
            ·
              refine ⟨356553663646440691799189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237702442430960461199459 356553663646440691799189)
              ·
                refine ⟨16713452983426907428087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 356553663646440691799189 16713452983426907428087)
                ·
                  rfl

theorem cell21_219708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_219708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219708 prefixEnd_219708 := by exact prefixLift 219708
  have htrace : WordTrace (prefixWord ++ tailWord_219708) baseStart_219708 baseEnd_219708 := by
    simpa [prefixWord, tailWord_219708, baseEnd_219708] using wordTrace_append hprefix tailTrace_219708
  have hstable : (prefixWord ++ tailWord_219708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219708).length < 2 ^ (prefixWord ++ tailWord_219708).sum := by decide
  have hdescent : baseEnd_219708 < baseStart_219708 := by decide
  rcases family_descends (prefixWord ++ tailWord_219708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219722 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_219722 : Nat := 118140960795 + 219722 * 2 ^ 59
def prefixEnd_219722 : Nat := 4983230072969 + 3 ^ 40 * 219722 * 2
def baseEnd_219722 : Nat := 50143553941019809050899

theorem tailTrace_219722 : CollatzResearch.WordTrace tailWord_219722 prefixEnd_219722 50143553941019809050899 := by
  unfold tailWord_219722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003479927498048593787355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5342613139994796250099613 2003479927498048593787355)
  ·
    refine ⟨3005219891247072890681033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2003479927498048593787355 3005219891247072890681033)
    ·
      refine ⟨2253914918435304668010775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3005219891247072890681033 2253914918435304668010775)
      ·
        refine ⟨3380872377652957002016163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253914918435304668010775 3380872377652957002016163)
        ·
          refine ⟨5071308566479435503024245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380872377652957002016163 5071308566479435503024245)
          ·
            refine ⟨475435178107447078408523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5071308566479435503024245 475435178107447078408523)
            ·
              refine ⟨713152767161170617612785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475435178107447078408523 713152767161170617612785)
              ·
                refine ⟨534864575370877963209589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713152767161170617612785 534864575370877963209589)
                ·
                  refine ⟨50143553941019809050899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534864575370877963209589 50143553941019809050899)
                  ·
                    rfl

theorem cell21_219722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_219722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219722 prefixEnd_219722 := by exact prefixLift 219722
  have htrace : WordTrace (prefixWord ++ tailWord_219722) baseStart_219722 baseEnd_219722 := by
    simpa [prefixWord, tailWord_219722, baseEnd_219722] using wordTrace_append hprefix tailTrace_219722
  have hstable : (prefixWord ++ tailWord_219722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219722).length < 2 ^ (prefixWord ++ tailWord_219722).sum := by decide
  have hdescent : baseEnd_219722 < baseStart_219722 := by decide
  rcases family_descends (prefixWord ++ tailWord_219722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219725 : List Nat := [1, 6, 1, 1, 2, 2, 3, 5]
def baseStart_219725 : Nat := 118140960795 + 219725 * 2 ^ 59
def prefixEnd_219725 : Nat := 4983230072969 + 3 ^ 40 * 219725 * 2
def baseEnd_219725 : Nat := 16714746193964156833631

theorem tailTrace_219725 : CollatzResearch.WordTrace tailWord_219725 prefixEnd_219725 16714746193964156833631 := by
  unfold tailWord_219725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014029128981325887508629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5342686085987550591672419 8014029128981325887508629)
  ·
    refine ⟨375657615420999650976967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8014029128981325887508629 375657615420999650976967)
    ·
      refine ⟨563486423131499476465451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375657615420999650976967 563486423131499476465451)
      ·
        refine ⟨845229634697249214698177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563486423131499476465451 845229634697249214698177)
        ·
          refine ⟨633922226022936911023633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845229634697249214698177 633922226022936911023633)
          ·
            refine ⟨475441669517202683267725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633922226022936911023633 475441669517202683267725)
            ·
              refine ⟨178290626068951006225397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475441669517202683267725 178290626068951006225397)
              ·
                refine ⟨16714746193964156833631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178290626068951006225397 16714746193964156833631)
                ·
                  rfl

theorem cell21_219725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].length) (baseStart_219725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219725 prefixEnd_219725 := by exact prefixLift 219725
  have htrace : WordTrace (prefixWord ++ tailWord_219725) baseStart_219725 baseEnd_219725 := by
    simpa [prefixWord, tailWord_219725, baseEnd_219725] using wordTrace_append hprefix tailTrace_219725
  have hstable : (prefixWord ++ tailWord_219725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219725).length < 2 ^ (prefixWord ++ tailWord_219725).sum := by decide
  have hdescent : baseEnd_219725 < baseStart_219725 := by decide
  rcases family_descends (prefixWord ++ tailWord_219725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219742 : List Nat := [4, 4, 1, 2, 1, 1, 8]
def baseStart_219742 : Nat := 118140960795 + 219742 * 2 ^ 59
def prefixEnd_219742 : Nat := 4983230072969 + 3 ^ 40 * 219742 * 2
def baseEnd_219742 : Nat := 5572013134833802079725

theorem tailTrace_219742 : CollatzResearch.WordTrace tailWord_219742 prefixEnd_219742 5572013134833802079725 := by
  unfold tailWord_219742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001831146239967223859685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5343099446613158527251653 1001831146239967223859685)
  ·
    refine ⟨187843339919993854473691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1001831146239967223859685 187843339919993854473691)
    ·
      refine ⟨281765009879990781710537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187843339919993854473691 281765009879990781710537)
      ·
        refine ⟨211323757409993086282903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281765009879990781710537 211323757409993086282903)
        ·
          refine ⟨316985636114989629424355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211323757409993086282903 316985636114989629424355)
          ·
            refine ⟨475478454172484444136533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316985636114989629424355 475478454172484444136533)
            ·
              refine ⟨5572013134833802079725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 475478454172484444136533 5572013134833802079725)
              ·
                rfl

theorem cell21_219742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 8].length) (baseStart_219742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219742 prefixEnd_219742 := by exact prefixLift 219742
  have htrace : WordTrace (prefixWord ++ tailWord_219742) baseStart_219742 baseEnd_219742 := by
    simpa [prefixWord, tailWord_219742, baseEnd_219742] using wordTrace_append hprefix tailTrace_219742
  have hstable : (prefixWord ++ tailWord_219742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219742).length < 2 ^ (prefixWord ++ tailWord_219742).sum := by decide
  have hdescent : baseEnd_219742 < baseStart_219742 := by decide
  rcases family_descends (prefixWord ++ tailWord_219742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219812 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_219812 : Nat := 118140960795 + 219812 * 2 ^ 59
def prefixEnd_219812 : Nat := 4983230072969 + 3 ^ 40 * 219812 * 2
def baseEnd_219812 : Nat := 50164093167199652550715

theorem tailTrace_219812 : CollatzResearch.WordTrace tailWord_219812 prefixEnd_219812 50164093167199652550715 := by
  unfold tailWord_219812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008601139833069872962845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5344801519777426497283793 4008601139833069872962845)
  ·
    refine ⟨1503225427437401202361067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4008601139833069872962845 1503225427437401202361067)
    ·
      refine ⟨2254838141156101803541601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503225427437401202361067 2254838141156101803541601)
      ·
        refine ⟨1691128605867076352656201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2254838141156101803541601 1691128605867076352656201)
        ·
          refine ⟨1268346454400307264492151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691128605867076352656201 1268346454400307264492151)
          ·
            refine ⟨1902519681600460896738227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268346454400307264492151 1902519681600460896738227)
            ·
              refine ⟨2853779522400691345107341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902519681600460896738227 2853779522400691345107341)
              ·
                refine ⟨1070167320900259254415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853779522400691345107341 1070167320900259254415253)
                ·
                  refine ⟨50164093167199652550715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1070167320900259254415253 50164093167199652550715)
                  ·
                    rfl

theorem cell21_219812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_219812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219812 prefixEnd_219812 := by exact prefixLift 219812
  have htrace : WordTrace (prefixWord ++ tailWord_219812) baseStart_219812 baseEnd_219812 := by
    simpa [prefixWord, tailWord_219812, baseEnd_219812] using wordTrace_append hprefix tailTrace_219812
  have hstable : (prefixWord ++ tailWord_219812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219812).length < 2 ^ (prefixWord ++ tailWord_219812).sum := by decide
  have hdescent : baseEnd_219812 < baseStart_219812 := by decide
  rcases family_descends (prefixWord ++ tailWord_219812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219860 : List Nat := [2, 4, 1, 3, 3, 8]
def baseStart_219860 : Nat := 118140960795 + 219860 * 2 ^ 59
def prefixEnd_219860 : Nat := 4983230072969 + 3 ^ 40 * 219860 * 2
def baseEnd_219860 : Nat := 1858335089672675398171

theorem tailTrace_219860 : CollatzResearch.WordTrace tailWord_219860 prefixEnd_219860 1858335089672675398171 := by
  unfold tailWord_219860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009476491746121971836517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5345968655661495962448689 4009476491746121971836517)
  ·
    refine ⟨751776842202397869719347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4009476491746121971836517 751776842202397869719347)
    ·
      refine ⟨1127665263303596804579021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751776842202397869719347 1127665263303596804579021)
      ·
        refine ⟨422874473738848801717133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1127665263303596804579021 422874473738848801717133)
        ·
          refine ⟨158577927652068300643925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422874473738848801717133 158577927652068300643925)
          ·
            refine ⟨1858335089672675398171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 158577927652068300643925 1858335089672675398171)
            ·
              rfl

theorem cell21_219860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 8].length) (baseStart_219860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219860 prefixEnd_219860 := by exact prefixLift 219860
  have htrace : WordTrace (prefixWord ++ tailWord_219860) baseStart_219860 baseEnd_219860 := by
    simpa [prefixWord, tailWord_219860, baseEnd_219860] using wordTrace_append hprefix tailTrace_219860
  have hstable : (prefixWord ++ tailWord_219860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219860).length < 2 ^ (prefixWord ++ tailWord_219860).sum := by decide
  have hdescent : baseEnd_219860 < baseStart_219860 := by decide
  rcases family_descends (prefixWord ++ tailWord_219860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219888 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_219888 : Nat := 118140960795 + 219888 * 2 ^ 59
def prefixEnd_219888 : Nat := 4983230072969 + 3 ^ 40 * 219888 * 2
def baseEnd_219888 : Nat := 50181437402640409283893

theorem tailTrace_219888 : CollatzResearch.WordTrace tailWord_219888 prefixEnd_219888 50181437402640409283893 := by
  unfold tailWord_219888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009987113695402362846159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5346649484927203150461545 4009987113695402362846159)
  ·
    refine ⟨6014980670543103544269239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009987113695402362846159 6014980670543103544269239)
    ·
      refine ⟨9022471005814655316403859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014980670543103544269239 9022471005814655316403859)
      ·
        refine ⟨13533706508721982974605789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022471005814655316403859 13533706508721982974605789)
        ·
          refine ⟨5075139940770743615477171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13533706508721982974605789 5075139940770743615477171)
          ·
            refine ⟨7612709911156115423215757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075139940770743615477171 7612709911156115423215757)
            ·
              refine ⟨2854766216683543283705909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7612709911156115423215757 2854766216683543283705909)
              ·
                refine ⟨267634332814082182847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2854766216683543283705909 267634332814082182847429)
                ·
                  refine ⟨50181437402640409283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267634332814082182847429 50181437402640409283893)
                  ·
                    rfl

theorem cell21_219888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_219888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219888 prefixEnd_219888 := by exact prefixLift 219888
  have htrace : WordTrace (prefixWord ++ tailWord_219888) baseStart_219888 baseEnd_219888 := by
    simpa [prefixWord, tailWord_219888, baseEnd_219888] using wordTrace_append hprefix tailTrace_219888
  have hstable : (prefixWord ++ tailWord_219888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219888).length < 2 ^ (prefixWord ++ tailWord_219888).sum := by decide
  have hdescent : baseEnd_219888 < baseStart_219888 := by decide
  rcases family_descends (prefixWord ++ tailWord_219888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219922 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_219922 : Nat := 118140960795 + 219922 * 2 ^ 59
def prefixEnd_219922 : Nat := 4983230072969 + 3 ^ 40 * 219922 * 2
def baseEnd_219922 : Nat := 50189196665863905717157

theorem tailTrace_219922 : CollatzResearch.WordTrace tailWord_219922 prefixEnd_219922 50189196665863905717157 := by
  unfold tailWord_219922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005303577316907133107505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5347476206178419021620013 2005303577316907133107505)
  ·
    refine ⟨1503977682987680349830629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2005303577316907133107505 1503977682987680349830629)
    ·
      refine ⟨281995815560190065593243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1503977682987680349830629 281995815560190065593243)
      ·
        refine ⟨422993723340285098389865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281995815560190065593243 422993723340285098389865)
        ·
          refine ⟨317245292505213823792399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422993723340285098389865 317245292505213823792399)
          ·
            refine ⟨475867938757820735688599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317245292505213823792399 475867938757820735688599)
            ·
              refine ⟨713801908136731103532899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475867938757820735688599 713801908136731103532899)
              ·
                refine ⟨1070702862205096655299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713801908136731103532899 1070702862205096655299349)
                ·
                  refine ⟨50189196665863905717157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1070702862205096655299349 50189196665863905717157)
                  ·
                    rfl

theorem cell21_219922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_219922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219922 prefixEnd_219922 := by exact prefixLift 219922
  have htrace : WordTrace (prefixWord ++ tailWord_219922) baseStart_219922 baseEnd_219922 := by
    simpa [prefixWord, tailWord_219922, baseEnd_219922] using wordTrace_append hprefix tailTrace_219922
  have hstable : (prefixWord ++ tailWord_219922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219922).length < 2 ^ (prefixWord ++ tailWord_219922).sum := by decide
  have hdescent : baseEnd_219922 < baseStart_219922 := by decide
  rcases family_descends (prefixWord ++ tailWord_219922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219947 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_219947 : Nat := 118140960795 + 219947 * 2 ^ 59
def prefixEnd_219947 : Nat := 4983230072969 + 3 ^ 40 * 219947 * 2
def baseEnd_219947 : Nat := 50194902006469417800439

theorem tailTrace_219947 : CollatzResearch.WordTrace tailWord_219947 prefixEnd_219947 50194902006469417800439 := by
  unfold tailWord_219947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022126134177057802090095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348084089451371868060063 8022126134177057802090095)
  ·
    refine ⟨12033189201265586703135143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8022126134177057802090095 12033189201265586703135143)
    ·
      refine ⟨18049783801898380054702715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033189201265586703135143 18049783801898380054702715)
      ·
        refine ⟨27074675702847570082054073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18049783801898380054702715 27074675702847570082054073)
        ·
          refine ⟨20306006777135677561540555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27074675702847570082054073 20306006777135677561540555)
          ·
            refine ⟨30459010165703516342310833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20306006777135677561540555 30459010165703516342310833)
            ·
              refine ⟨22844257624277637256733125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30459010165703516342310833 22844257624277637256733125)
              ·
                refine ⟨4283298304552056985637461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22844257624277637256733125 4283298304552056985637461)
                ·
                  refine ⟨50194902006469417800439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4283298304552056985637461 50194902006469417800439)
                  ·
                    rfl

theorem cell21_219947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_219947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219947 prefixEnd_219947 := by exact prefixLift 219947
  have htrace : WordTrace (prefixWord ++ tailWord_219947) baseStart_219947 baseEnd_219947 := by
    simpa [prefixWord, tailWord_219947, baseEnd_219947] using wordTrace_append hprefix tailTrace_219947
  have hstable : (prefixWord ++ tailWord_219947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219947).length < 2 ^ (prefixWord ++ tailWord_219947).sum := by decide
  have hdescent : baseEnd_219947 < baseStart_219947 := by decide
  rcases family_descends (prefixWord ++ tailWord_219947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219967 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 3]
def baseStart_219967 : Nat := 118140960795 + 219967 * 2 ^ 59
def prefixEnd_219967 : Nat := 4983230072969 + 3 ^ 40 * 219967 * 2
def baseEnd_219967 : Nat := 50199466278953827467065

theorem tailTrace_219967 : CollatzResearch.WordTrace tailWord_219967 prefixEnd_219967 50199466278953827467065 := by
  unfold tailWord_219967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022855594104601217818155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348570396069734145212103 8022855594104601217818155)
  ·
    refine ⟨12034283391156901826727233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8022855594104601217818155 12034283391156901826727233)
    ·
      refine ⟨9025712543367676370045425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12034283391156901826727233 9025712543367676370045425)
      ·
        refine ⟨6769284407525757277534069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9025712543367676370045425 6769284407525757277534069)
        ·
          refine ⟨634620413205539744768819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6769284407525757277534069 634620413205539744768819)
          ·
            refine ⟨951930619808309617153229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634620413205539744768819 951930619808309617153229)
            ·
              refine ⟨356973982428116106432461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951930619808309617153229 356973982428116106432461)
              ·
                refine ⟨133865243410543539912173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356973982428116106432461 133865243410543539912173)
                ·
                  refine ⟨50199466278953827467065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133865243410543539912173 50199466278953827467065)
                  ·
                    rfl

theorem cell21_219967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].length) (baseStart_219967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_219967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_219967 prefixEnd_219967 := by exact prefixLift 219967
  have htrace : WordTrace (prefixWord ++ tailWord_219967) baseStart_219967 baseEnd_219967 := by
    simpa [prefixWord, tailWord_219967, baseEnd_219967] using wordTrace_append hprefix tailTrace_219967
  have hstable : (prefixWord ++ tailWord_219967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219967).length < 2 ^ (prefixWord ++ tailWord_219967).sum := by decide
  have hdescent : baseEnd_219967 < baseStart_219967 := by decide
  rcases family_descends (prefixWord ++ tailWord_219967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220023 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_220023 : Nat := 118140960795 + 220023 * 2 ^ 59
def prefixEnd_220023 : Nat := 4983230072969 + 3 ^ 40 * 220023 * 2
def baseEnd_220023 : Nat := 50212246241910174533617

theorem tailTrace_220023 : CollatzResearch.WordTrace tailWord_220023 prefixEnd_220023 50212246241910174533617 := by
  unfold tailWord_220023
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024898081901722781856723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5349932054601148521237815 8024898081901722781856723)
  ·
    refine ⟨12037347122852584172785085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024898081901722781856723 12037347122852584172785085)
    ·
      refine ⟨4514005171069719064794407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12037347122852584172785085 4514005171069719064794407)
      ·
        refine ⟨6771007756604578597191611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514005171069719064794407 6771007756604578597191611)
        ·
          refine ⟨10156511634906867895787417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771007756604578597191611 10156511634906867895787417)
          ·
            refine ⟨7617383726180150921840563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10156511634906867895787417 7617383726180150921840563)
            ·
              refine ⟨11426075589270226382760845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617383726180150921840563 11426075589270226382760845)
              ·
                refine ⟨4284778345976334893535317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11426075589270226382760845 4284778345976334893535317)
                ·
                  refine ⟨50212246241910174533617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4284778345976334893535317 50212246241910174533617)
                  ·
                    rfl

theorem cell21_220023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_220023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220023 prefixEnd_220023 := by exact prefixLift 220023
  have htrace : WordTrace (prefixWord ++ tailWord_220023) baseStart_220023 baseEnd_220023 := by
    simpa [prefixWord, tailWord_220023, baseEnd_220023] using wordTrace_append hprefix tailTrace_220023
  have hstable : (prefixWord ++ tailWord_220023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220023).length < 2 ^ (prefixWord ++ tailWord_220023).sum := by decide
  have hdescent : baseEnd_220023 < baseStart_220023 := by decide
  rcases family_descends (prefixWord ++ tailWord_220023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220026 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_220026 : Nat := 118140960795 + 220026 * 2 ^ 59
def prefixEnd_220026 : Nat := 4983230072969 + 3 ^ 40 * 220026 * 2
def baseEnd_220026 : Nat := 50212930882782835983611

theorem tailTrace_220026 : CollatzResearch.WordTrace tailWord_220026 prefixEnd_220026 50212930882782835983611 := by
  unfold tailWord_220026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006251875222713573553983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5350005000593902862810621 2006251875222713573553983)
  ·
    refine ⟨3009377812834070360330975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006251875222713573553983 3009377812834070360330975)
    ·
      refine ⟨4514066719251105540496463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009377812834070360330975 4514066719251105540496463)
      ·
        refine ⟨6771100078876658310744695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514066719251105540496463 6771100078876658310744695)
        ·
          refine ⟨10156650118314987466117043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771100078876658310744695 10156650118314987466117043)
          ·
            refine ⟨15234975177472481199175565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156650118314987466117043 15234975177472481199175565)
            ·
              refine ⟨5713115691552180449690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15234975177472481199175565 5713115691552180449690837)
              ·
                refine ⟨133901149020754229289629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5713115691552180449690837 133901149020754229289629)
                ·
                  refine ⟨50212930882782835983611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133901149020754229289629 50212930882782835983611)
                  ·
                    rfl

theorem cell21_220026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_220026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220026 prefixEnd_220026 := by exact prefixLift 220026
  have htrace : WordTrace (prefixWord ++ tailWord_220026) baseStart_220026 baseEnd_220026 := by
    simpa [prefixWord, tailWord_220026, baseEnd_220026] using wordTrace_append hprefix tailTrace_220026
  have hstable : (prefixWord ++ tailWord_220026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220026).length < 2 ^ (prefixWord ++ tailWord_220026).sum := by decide
  have hdescent : baseEnd_220026 < baseStart_220026 := by decide
  rcases family_descends (prefixWord ++ tailWord_220026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220043 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 3]
def baseStart_220043 : Nat := 118140960795 + 220043 * 2 ^ 59
def prefixEnd_220043 : Nat := 4983230072969 + 3 ^ 40 * 220043 * 2
def baseEnd_220043 : Nat := 50216810514394584200243

theorem tailTrace_220043 : CollatzResearch.WordTrace tailWord_220043 prefixEnd_220043 50216810514394584200243 := by
  unfold tailWord_220043
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025627541829266197584783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5350418361219510798389855 8025627541829266197584783)
  ·
    refine ⟨12038441312743899296377175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025627541829266197584783 12038441312743899296377175)
    ·
      refine ⟨18057661969115848944565763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038441312743899296377175 18057661969115848944565763)
      ·
        refine ⟨27086492953673773416848645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18057661969115848944565763 27086492953673773416848645)
        ·
          refine ⟨5078717428813832515659121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27086492953673773416848645 5078717428813832515659121)
          ·
            refine ⟨3809038071610374386744341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5078717428813832515659121 3809038071610374386744341)
            ·
              refine ⟨178548659606736299378641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3809038071610374386744341 178548659606736299378641)
              ·
                refine ⟨133911494705052224533981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178548659606736299378641 133911494705052224533981)
                ·
                  refine ⟨50216810514394584200243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133911494705052224533981 50216810514394584200243)
                  ·
                    rfl

theorem cell21_220043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].length) (baseStart_220043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220043 prefixEnd_220043 := by exact prefixLift 220043
  have htrace : WordTrace (prefixWord ++ tailWord_220043) baseStart_220043 baseEnd_220043 := by
    simpa [prefixWord, tailWord_220043, baseEnd_220043] using wordTrace_append hprefix tailTrace_220043
  have hstable : (prefixWord ++ tailWord_220043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220043).length < 2 ^ (prefixWord ++ tailWord_220043).sum := by decide
  have hdescent : baseEnd_220043 < baseStart_220043 := by decide
  rcases family_descends (prefixWord ++ tailWord_220043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220077 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 3]
def baseStart_220077 : Nat := 118140960795 + 220077 * 2 ^ 59
def prefixEnd_220077 : Nat := 4983230072969 + 3 ^ 40 * 220077 * 2
def baseEnd_220077 : Nat := 50224569777618080633507

theorem tailTrace_220077 : CollatzResearch.WordTrace tailWord_220077 prefixEnd_220077 50224569777618080633507 := by
  unfold tailWord_220077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026867623706090004322485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5351245082470726669548323 8026867623706090004322485)
  ·
    refine ⟨752518839722445937905233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8026867623706090004322485 752518839722445937905233)
    ·
      refine ⟨564389129791834453428925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752518839722445937905233 564389129791834453428925)
      ·
        refine ⟨211645923671937920035847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564389129791834453428925 211645923671937920035847)
        ·
          refine ⟨317468885507906880053771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211645923671937920035847 317468885507906880053771)
          ·
            refine ⟨476203328261860320080657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317468885507906880053771 476203328261860320080657)
            ·
              refine ⟨357152496196395240060493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476203328261860320080657 357152496196395240060493)
              ·
                refine ⟨133932186073648215022685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357152496196395240060493 133932186073648215022685)
                ·
                  refine ⟨50224569777618080633507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133932186073648215022685 50224569777618080633507)
                  ·
                    rfl

theorem cell21_220077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_220077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220077 prefixEnd_220077 := by exact prefixLift 220077
  have htrace : WordTrace (prefixWord ++ tailWord_220077) baseStart_220077 baseEnd_220077 := by
    simpa [prefixWord, tailWord_220077, baseEnd_220077] using wordTrace_append hprefix tailTrace_220077
  have hstable : (prefixWord ++ tailWord_220077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220077).length < 2 ^ (prefixWord ++ tailWord_220077).sum := by decide
  have hdescent : baseEnd_220077 < baseStart_220077 := by decide
  rcases family_descends (prefixWord ++ tailWord_220077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220085 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_220085 : Nat := 118140960795 + 220085 * 2 ^ 59
def prefixEnd_220085 : Nat := 4983230072969 + 3 ^ 40 * 220085 * 2
def baseEnd_220085 : Nat := 50226395486611844500157

theorem tailTrace_220085 : CollatzResearch.WordTrace tailWord_220085 prefixEnd_220085 50226395486611844500157 := by
  unfold tailWord_220085
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027159407677107370613709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5351439605118071580409139 8027159407677107370613709)
  ·
    refine ⟨3010184777878915263980141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8027159407677107370613709 3010184777878915263980141)
    ·
      refine ⟨1128819291704593223992553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3010184777878915263980141 1128819291704593223992553)
      ·
        refine ⟨846614468778444917994415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1128819291704593223992553 846614468778444917994415)
        ·
          refine ⟨1269921703167667376991623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846614468778444917994415 1269921703167667376991623)
          ·
            refine ⟨1904882554751501065487435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269921703167667376991623 1904882554751501065487435)
            ·
              refine ⟨2857323832127251598231153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904882554751501065487435 2857323832127251598231153)
              ·
                refine ⟨2142992874095438698673365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857323832127251598231153 2142992874095438698673365)
                ·
                  refine ⟨50226395486611844500157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2142992874095438698673365 50226395486611844500157)
                  ·
                    rfl

theorem cell21_220085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_220085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220085 prefixEnd_220085 := by exact prefixLift 220085
  have htrace : WordTrace (prefixWord ++ tailWord_220085) baseStart_220085 baseEnd_220085 := by
    simpa [prefixWord, tailWord_220085, baseEnd_220085] using wordTrace_append hprefix tailTrace_220085
  have hstable : (prefixWord ++ tailWord_220085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220085).length < 2 ^ (prefixWord ++ tailWord_220085).sum := by decide
  have hdescent : baseEnd_220085 < baseStart_220085 := by decide
  rcases family_descends (prefixWord ++ tailWord_220085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220099 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_220099 : Nat := 118140960795 + 220099 * 2 ^ 59
def prefixEnd_220099 : Nat := 4983230072969 + 3 ^ 40 * 220099 * 2
def baseEnd_220099 : Nat := 50229590477350931266795

theorem tailTrace_220099 : CollatzResearch.WordTrace tailWord_220099 prefixEnd_220099 50229590477350931266795 := by
  unfold tailWord_220099
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027670029626387761623351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5351780019750925174415567 8027670029626387761623351)
  ·
    refine ⟨12041505044439581642435027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8027670029626387761623351 12041505044439581642435027)
    ·
      refine ⟨18062257566659372463652541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041505044439581642435027 18062257566659372463652541)
      ·
        refine ⟨6773346587497264673869703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18062257566659372463652541 6773346587497264673869703)
        ·
          refine ⟨10160019881245897010804555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773346587497264673869703 10160019881245897010804555)
          ·
            refine ⟨15240029821868845516206833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160019881245897010804555 15240029821868845516206833)
            ·
              refine ⟨11430022366401634137155125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15240029821868845516206833 11430022366401634137155125)
              ·
                refine ⟨1071564596850153200358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11430022366401634137155125 1071564596850153200358293)
                ·
                  refine ⟨50229590477350931266795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1071564596850153200358293 50229590477350931266795)
                  ·
                    rfl

theorem cell21_220099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_220099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220099 prefixEnd_220099 := by exact prefixLift 220099
  have htrace : WordTrace (prefixWord ++ tailWord_220099) baseStart_220099 baseEnd_220099 := by
    simpa [prefixWord, tailWord_220099, baseEnd_220099] using wordTrace_append hprefix tailTrace_220099
  have hstable : (prefixWord ++ tailWord_220099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220099).length < 2 ^ (prefixWord ++ tailWord_220099).sum := by decide
  have hdescent : baseEnd_220099 < baseStart_220099 := by decide
  rcases family_descends (prefixWord ++ tailWord_220099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220212 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_220212 : Nat := 118140960795 + 220212 * 2 ^ 59
def prefixEnd_220212 : Nat := 4983230072969 + 3 ^ 40 * 220212 * 2
def baseEnd_220212 : Nat := 50255378616887845883231

theorem tailTrace_220212 : CollatzResearch.WordTrace tailWord_220212 prefixEnd_220212 50255378616887845883231 := by
  unfold tailWord_220212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015895739108504030243445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5354527652144672040324593 4015895739108504030243445)
  ·
    refine ⟨376490225541422252835323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4015895739108504030243445 376490225541422252835323)
    ·
      refine ⟨564735338312133379252985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376490225541422252835323 564735338312133379252985)
      ·
        refine ⟨423551503734100034439739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564735338312133379252985 423551503734100034439739)
        ·
          refine ⟨635327255601150051659609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423551503734100034439739 635327255601150051659609)
          ·
            refine ⟨476495441700862538744707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635327255601150051659609 476495441700862538744707)
            ·
              refine ⟨714743162551293808117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476495441700862538744707 714743162551293808117061)
              ·
                refine ⟨134014342978367589021949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714743162551293808117061 134014342978367589021949)
                ·
                  refine ⟨50255378616887845883231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134014342978367589021949 50255378616887845883231)
                  ·
                    rfl

theorem cell21_220212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_220212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220212 prefixEnd_220212 := by exact prefixLift 220212
  have htrace : WordTrace (prefixWord ++ tailWord_220212) baseStart_220212 baseEnd_220212 := by
    simpa [prefixWord, tailWord_220212, baseEnd_220212] using wordTrace_append hprefix tailTrace_220212
  have hstable : (prefixWord ++ tailWord_220212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220212).length < 2 ^ (prefixWord ++ tailWord_220212).sum := by decide
  have hdescent : baseEnd_220212 < baseStart_220212 := by decide
  rcases family_descends (prefixWord ++ tailWord_220212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220285 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 4]
def baseStart_220285 : Nat := 118140960795 + 220285 * 2 ^ 59
def prefixEnd_220285 : Nat := 4983230072969 + 3 ^ 40 * 220285 * 2
def baseEnd_220285 : Nat := 50272038211455941166415

theorem tailTrace_220285 : CollatzResearch.WordTrace tailWord_220285 prefixEnd_220285 50272038211455941166415 := by
  unfold tailWord_220285
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034454006952541527894309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5356302671301694351929539 8034454006952541527894309)
  ·
    refine ⟨1506460126303601536480183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8034454006952541527894309 1506460126303601536480183)
    ·
      refine ⟨2259690189455402304720275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506460126303601536480183 2259690189455402304720275)
      ·
        refine ⟨3389535284183103457080413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259690189455402304720275 3389535284183103457080413)
        ·
          refine ⟨1271075731568663796405155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3389535284183103457080413 1271075731568663796405155)
          ·
            refine ⟨1906613597352995694607733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271075731568663796405155 1906613597352995694607733)
            ·
              refine ⟨178745024751843346369475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1906613597352995694607733 178745024751843346369475)
              ·
                refine ⟨268117537127765019554213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178745024751843346369475 268117537127765019554213)
                ·
                  refine ⟨50272038211455941166415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268117537127765019554213 50272038211455941166415)
                  ·
                    rfl

theorem cell21_220285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_220285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220285 prefixEnd_220285 := by exact prefixLift 220285
  have htrace : WordTrace (prefixWord ++ tailWord_220285) baseStart_220285 baseEnd_220285 := by
    simpa [prefixWord, tailWord_220285, baseEnd_220285] using wordTrace_append hprefix tailTrace_220285
  have hstable : (prefixWord ++ tailWord_220285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220285).length < 2 ^ (prefixWord ++ tailWord_220285).sum := by decide
  have hdescent : baseEnd_220285 < baseStart_220285 := by decide
  rcases family_descends (prefixWord ++ tailWord_220285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220381 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 3]
def baseStart_220381 : Nat := 118140960795 + 220381 * 2 ^ 59
def prefixEnd_220381 : Nat := 4983230072969 + 3 ^ 40 * 220381 * 2
def baseEnd_220381 : Nat := 50293946719381107566219

theorem tailTrace_220381 : CollatzResearch.WordTrace tailWord_220381 prefixEnd_220381 50293946719381107566219 := by
  unfold tailWord_220381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037955414604749923388997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5358636943069833282259331 8037955414604749923388997)
  ·
    refine ⟨1507116640238390610635437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8037955414604749923388997 1507116640238390610635437)
    ·
      refine ⟨565168740089396478988289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1507116640238390610635437 565168740089396478988289)
      ·
        refine ⟨423876555067047359241217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565168740089396478988289 423876555067047359241217)
        ·
          refine ⟨317907416300285519430913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423876555067047359241217 317907416300285519430913)
          ·
            refine ⟨238430562225214139573185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317907416300285519430913 238430562225214139573185)
            ·
              refine ⟨178822921668910604679889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238430562225214139573185 178822921668910604679889)
              ·
                refine ⟨134117191251682953509917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178822921668910604679889 134117191251682953509917)
                ·
                  refine ⟨50293946719381107566219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134117191251682953509917 50293946719381107566219)
                  ·
                    rfl

theorem cell21_220381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_220381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220381 prefixEnd_220381 := by exact prefixLift 220381
  have htrace : WordTrace (prefixWord ++ tailWord_220381) baseStart_220381 baseEnd_220381 := by
    simpa [prefixWord, tailWord_220381, baseEnd_220381] using wordTrace_append hprefix tailTrace_220381
  have hstable : (prefixWord ++ tailWord_220381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220381).length < 2 ^ (prefixWord ++ tailWord_220381).sum := by decide
  have hdescent : baseEnd_220381 < baseStart_220381 := by decide
  rcases family_descends (prefixWord ++ tailWord_220381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220465 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_220465 : Nat := 118140960795 + 220465 * 2 ^ 59
def prefixEnd_220465 : Nat := 4983230072969 + 3 ^ 40 * 220465 * 2
def baseEnd_220465 : Nat := 50313116663815628166047

theorem tailTrace_220465 : CollatzResearch.WordTrace tailWord_220465 prefixEnd_220465 50313116663815628166047 := by
  unfold tailWord_220465
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041019146300432269446849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5360679430866954846297899 8041019146300432269446849)
  ·
    refine ⟨6030764359725324202085137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8041019146300432269446849 6030764359725324202085137)
    ·
      refine ⟨4523073269793993151563853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6030764359725324202085137 4523073269793993151563853)
      ·
        refine ⟨1696152476172747431836445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4523073269793993151563853 1696152476172747431836445)
        ·
          refine ⟨636057178564780286938667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696152476172747431836445 636057178564780286938667)
          ·
            refine ⟨954085767847170430408001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636057178564780286938667 954085767847170430408001)
            ·
              refine ⟨715564325885377822806001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954085767847170430408001 715564325885377822806001)
              ·
                refine ⟨536673244414033367104501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715564325885377822806001 536673244414033367104501)
                ·
                  refine ⟨50313116663815628166047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 536673244414033367104501 50313116663815628166047)
                  ·
                    rfl

theorem cell21_220465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_220465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220465 prefixEnd_220465 := by exact prefixLift 220465
  have htrace : WordTrace (prefixWord ++ tailWord_220465) baseStart_220465 baseEnd_220465 := by
    simpa [prefixWord, tailWord_220465, baseEnd_220465] using wordTrace_append hprefix tailTrace_220465
  have hstable : (prefixWord ++ tailWord_220465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220465).length < 2 ^ (prefixWord ++ tailWord_220465).sum := by decide
  have hdescent : baseEnd_220465 < baseStart_220465 := by decide
  rcases family_descends (prefixWord ++ tailWord_220465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220479 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_220479 : Nat := 118140960795 + 220479 * 2 ^ 59
def prefixEnd_220479 : Nat := 4983230072969 + 3 ^ 40 * 220479 * 2
def baseEnd_220479 : Nat := 50316311654554714932685

theorem tailTrace_220479 : CollatzResearch.WordTrace tailWord_220479 prefixEnd_220479 50316311654554714932685 := by
  unfold tailWord_220479
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041529768249712660456491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361019845499808440304327 8041529768249712660456491)
  ·
    refine ⟨12062294652374568990684737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8041529768249712660456491 12062294652374568990684737)
    ·
      refine ⟨9046720989280926743013553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12062294652374568990684737 9046720989280926743013553)
      ·
        refine ⟨6785040741960695057260165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9046720989280926743013553 6785040741960695057260165)
        ·
          refine ⟨1272195139117630323236281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6785040741960695057260165 1272195139117630323236281)
          ·
            refine ⟨954146354338222742427211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272195139117630323236281 954146354338222742427211)
            ·
              refine ⟨1431219531507334113640817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954146354338222742427211 1431219531507334113640817)
              ·
                refine ⟨1073414648630500585230613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431219531507334113640817 1073414648630500585230613)
                ·
                  refine ⟨50316311654554714932685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1073414648630500585230613 50316311654554714932685)
                  ·
                    rfl

theorem cell21_220479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_220479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220479 prefixEnd_220479 := by exact prefixLift 220479
  have htrace : WordTrace (prefixWord ++ tailWord_220479) baseStart_220479 baseEnd_220479 := by
    simpa [prefixWord, tailWord_220479, baseEnd_220479] using wordTrace_append hprefix tailTrace_220479
  have hstable : (prefixWord ++ tailWord_220479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220479).length < 2 ^ (prefixWord ++ tailWord_220479).sum := by decide
  have hdescent : baseEnd_220479 < baseStart_220479 := by decide
  rcases family_descends (prefixWord ++ tailWord_220479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220502 : List Nat := [5, 2, 3, 1, 1, 1, 2, 6]
def baseStart_220502 : Nat := 118140960795 + 220502 * 2 ^ 59
def prefixEnd_220502 : Nat := 4983230072969 + 3 ^ 40 * 220502 * 2
def baseEnd_220502 : Nat := 16773853522637262016435

theorem tailTrace_220502 : CollatzResearch.WordTrace tailWord_220502 prefixEnd_220502 16773853522637262016435 := by
  unfold tailWord_220502
  simp only [CollatzResearch.WordTrace]
  refine ⟨502648040447899224283985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5361579098110925059029173 502648040447899224283985)
  ·
    refine ⟨376986030335924418212989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 502648040447899224283985 376986030335924418212989)
    ·
      refine ⟨141369761375971656829871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376986030335924418212989 141369761375971656829871)
      ·
        refine ⟨212054642063957485244807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141369761375971656829871 212054642063957485244807)
        ·
          refine ⟨318081963095936227867211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212054642063957485244807 318081963095936227867211)
          ·
            refine ⟨477122944643904341800817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318081963095936227867211 477122944643904341800817)
            ·
              refine ⟨357842208482928256350613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477122944643904341800817 357842208482928256350613)
              ·
                refine ⟨16773853522637262016435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357842208482928256350613 16773853522637262016435)
                ·
                  rfl

theorem cell21_220502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_220502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220502 prefixEnd_220502 := by exact prefixLift 220502
  have htrace : WordTrace (prefixWord ++ tailWord_220502) baseStart_220502 baseEnd_220502 := by
    simpa [prefixWord, tailWord_220502, baseEnd_220502] using wordTrace_append hprefix tailTrace_220502
  have hstable : (prefixWord ++ tailWord_220502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220502).length < 2 ^ (prefixWord ++ tailWord_220502).sum := by decide
  have hdescent : baseEnd_220502 < baseStart_220502 := by decide
  rcases family_descends (prefixWord ++ tailWord_220502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220631 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_220631 : Nat := 118140960795 + 220631 * 2 ^ 59
def prefixEnd_220631 : Nat := 4983230072969 + 3 ^ 40 * 220631 * 2
def baseEnd_220631 : Nat := 50351000125436228399041

theorem tailTrace_220631 : CollatzResearch.WordTrace tailWord_220631 prefixEnd_220631 50351000125436228399041 := by
  unfold tailWord_220631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047073663699042619989747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5364715775799361746659831 8047073663699042619989747)
  ·
    refine ⟨12070610495548563929984621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047073663699042619989747 12070610495548563929984621)
    ·
      refine ⟨4526478935830711473744233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12070610495548563929984621 4526478935830711473744233)
      ·
        refine ⟨3394859201873033605308175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4526478935830711473744233 3394859201873033605308175)
        ·
          refine ⟨5092288802809550407962263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394859201873033605308175 5092288802809550407962263)
          ·
            refine ⟨7638433204214325611943395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092288802809550407962263 7638433204214325611943395)
            ·
              refine ⟨11457649806321488417915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638433204214325611943395 11457649806321488417915093)
              ·
                refine ⟨268538667335659884794885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11457649806321488417915093 268538667335659884794885)
                ·
                  refine ⟨50351000125436228399041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268538667335659884794885 50351000125436228399041)
                  ·
                    rfl

theorem cell21_220631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_220631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220631 prefixEnd_220631 := by exact prefixLift 220631
  have htrace : WordTrace (prefixWord ++ tailWord_220631) baseStart_220631 baseEnd_220631 := by
    simpa [prefixWord, tailWord_220631, baseEnd_220631] using wordTrace_append hprefix tailTrace_220631
  have hstable : (prefixWord ++ tailWord_220631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220631).length < 2 ^ (prefixWord ++ tailWord_220631).sum := by decide
  have hdescent : baseEnd_220631 < baseStart_220631 := by decide
  rcases family_descends (prefixWord ++ tailWord_220631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220662 : List Nat := [5, 1, 1, 1, 2, 2, 9]
def baseStart_220662 : Nat := 118140960795 + 220662 * 2 ^ 59
def prefixEnd_220662 : Nat := 4983230072969 + 3 ^ 40 * 220662 * 2
def baseEnd_220662 : Nat := 5595341638643007042479

theorem tailTrace_220662 : CollatzResearch.WordTrace tailWord_220662 prefixEnd_220662 5595341638643007042479 := by
  unfold tailWord_220662
  simp only [CollatzResearch.WordTrace]
  refine ⟨503012770411670932148015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5365469551057823276245493 503012770411670932148015)
  ·
    refine ⟨754519155617506398222023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503012770411670932148015 754519155617506398222023)
    ·
      refine ⟨1131778733426259597333035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754519155617506398222023 1131778733426259597333035)
      ·
        refine ⟨1697668100139389395999553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131778733426259597333035 1697668100139389395999553)
        ·
          refine ⟨1273251075104542046999665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697668100139389395999553 1273251075104542046999665)
          ·
            refine ⟨954938306328406535249749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273251075104542046999665 954938306328406535249749)
            ·
              refine ⟨5595341638643007042479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 954938306328406535249749 5595341638643007042479)
              ·
                rfl

theorem cell21_220662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 9].length) (baseStart_220662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220662 prefixEnd_220662 := by exact prefixLift 220662
  have htrace : WordTrace (prefixWord ++ tailWord_220662) baseStart_220662 baseEnd_220662 := by
    simpa [prefixWord, tailWord_220662, baseEnd_220662] using wordTrace_append hprefix tailTrace_220662
  have hstable : (prefixWord ++ tailWord_220662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220662).length < 2 ^ (prefixWord ++ tailWord_220662).sum := by decide
  have hdescent : baseEnd_220662 < baseStart_220662 := by decide
  rcases family_descends (prefixWord ++ tailWord_220662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220727 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 3]
def baseStart_220727 : Nat := 118140960795 + 220727 * 2 ^ 59
def prefixEnd_220727 : Nat := 4983230072969 + 3 ^ 40 * 220727 * 2
def baseEnd_220727 : Nat := 50372908633361394798845

theorem tailTrace_220727 : CollatzResearch.WordTrace tailWord_220727 prefixEnd_220727 50372908633361394798845 := by
  unfold tailWord_220727
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050575071351251015484435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5367050047567500676989623 8050575071351251015484435)
  ·
    refine ⟨12075862607026876523226653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050575071351251015484435 12075862607026876523226653)
    ·
      refine ⟨4528448477635078696209995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12075862607026876523226653 4528448477635078696209995)
      ·
        refine ⟨6792672716452618044314993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528448477635078696209995 6792672716452618044314993)
        ·
          refine ⟨5094504537339463533236245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6792672716452618044314993 5094504537339463533236245)
          ·
            refine ⟨238804900187787353120449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5094504537339463533236245 238804900187787353120449)
            ·
              refine ⟨179103675140840514840337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238804900187787353120449 179103675140840514840337)
              ·
                refine ⟨134327756355630386130253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179103675140840514840337 134327756355630386130253)
                ·
                  refine ⟨50372908633361394798845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134327756355630386130253 50372908633361394798845)
                  ·
                    rfl

theorem cell21_220727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].length) (baseStart_220727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220727 prefixEnd_220727 := by exact prefixLift 220727
  have htrace : WordTrace (prefixWord ++ tailWord_220727) baseStart_220727 baseEnd_220727 := by
    simpa [prefixWord, tailWord_220727, baseEnd_220727] using wordTrace_append hprefix tailTrace_220727
  have hstable : (prefixWord ++ tailWord_220727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220727).length < 2 ^ (prefixWord ++ tailWord_220727).sum := by decide
  have hdescent : baseEnd_220727 < baseStart_220727 := by decide
  rcases family_descends (prefixWord ++ tailWord_220727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220752 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_220752 : Nat := 118140960795 + 220752 * 2 ^ 59
def prefixEnd_220752 : Nat := 4983230072969 + 3 ^ 40 * 220752 * 2
def baseEnd_220752 : Nat := 50378613973966906882127

theorem tailTrace_220752 : CollatzResearch.WordTrace tailWord_220752 prefixEnd_220752 50378613973966906882127 := by
  unfold tailWord_220752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025743448130340142572255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5367657930840453523429673 4025743448130340142572255)
  ·
    refine ⟨6038615172195510213858383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4025743448130340142572255 6038615172195510213858383)
    ·
      refine ⟨9057922758293265320787575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6038615172195510213858383 9057922758293265320787575)
      ·
        refine ⟨13586884137439897981181363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057922758293265320787575 13586884137439897981181363)
        ·
          refine ⟨20380326206159846971772045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13586884137439897981181363 20380326206159846971772045)
          ·
            refine ⟨7642622327309942614414517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20380326206159846971772045 7642622327309942614414517)
            ·
              refine ⟨716495843185307120101361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7642622327309942614414517 716495843185307120101361)
              ·
                refine ⟨537371882388980340076021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716495843185307120101361 537371882388980340076021)
                ·
                  refine ⟨50378613973966906882127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 537371882388980340076021 50378613973966906882127)
                  ·
                    rfl

theorem cell21_220752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_220752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220752 prefixEnd_220752 := by exact prefixLift 220752
  have htrace : WordTrace (prefixWord ++ tailWord_220752) baseStart_220752 baseEnd_220752 := by
    simpa [prefixWord, tailWord_220752, baseEnd_220752] using wordTrace_append hprefix tailTrace_220752
  have hstable : (prefixWord ++ tailWord_220752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220752).length < 2 ^ (prefixWord ++ tailWord_220752).sum := by decide
  have hdescent : baseEnd_220752 < baseStart_220752 := by decide
  rcases family_descends (prefixWord ++ tailWord_220752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220786 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_220786 : Nat := 118140960795 + 220786 * 2 ^ 59
def prefixEnd_220786 : Nat := 4983230072969 + 3 ^ 40 * 220786 * 2
def baseEnd_220786 : Nat := 50386373237190403315391

theorem tailTrace_220786 : CollatzResearch.WordTrace tailWord_220786 prefixEnd_220786 50386373237190403315391 := by
  unfold tailWord_220786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2013181744534376022970553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5368484652091669394588141 2013181744534376022970553)
  ·
    refine ⟨1509886308400782017227915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2013181744534376022970553 1509886308400782017227915)
    ·
      refine ⟨2264829462601173025841873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509886308400782017227915 2264829462601173025841873)
      ·
        refine ⟨1698622096950879769381405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2264829462601173025841873 1698622096950879769381405)
        ·
          refine ⟨636983286356579913518027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1698622096950879769381405 636983286356579913518027)
          ·
            refine ⟨955474929534869870277041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636983286356579913518027 955474929534869870277041)
            ·
              refine ⟨716606197151152402707781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955474929534869870277041 716606197151152402707781)
              ·
                refine ⟨134363661965841075507709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716606197151152402707781 134363661965841075507709)
                ·
                  refine ⟨50386373237190403315391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134363661965841075507709 50386373237190403315391)
                  ·
                    rfl

theorem cell21_220786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_220786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220786 prefixEnd_220786 := by exact prefixLift 220786
  have htrace : WordTrace (prefixWord ++ tailWord_220786) baseStart_220786 baseEnd_220786 := by
    simpa [prefixWord, tailWord_220786, baseEnd_220786] using wordTrace_append hprefix tailTrace_220786
  have hstable : (prefixWord ++ tailWord_220786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220786).length < 2 ^ (prefixWord ++ tailWord_220786).sum := by decide
  have hdescent : baseEnd_220786 < baseStart_220786 := by decide
  rcases family_descends (prefixWord ++ tailWord_220786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220800 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_220800 : Nat := 118140960795 + 220800 * 2 ^ 59
def prefixEnd_220800 : Nat := 4983230072969 + 3 ^ 40 * 220800 * 2
def baseEnd_220800 : Nat := 50389568227929490082029

theorem tailTrace_220800 : CollatzResearch.WordTrace tailWord_220800 prefixEnd_220800 50389568227929490082029 := by
  unfold tailWord_220800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026618800043392241445927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5368825066724522988594569 4026618800043392241445927)
  ·
    refine ⟨6039928200065088362168891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026618800043392241445927 6039928200065088362168891)
    ·
      refine ⟨9059892300097632543253337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6039928200065088362168891 9059892300097632543253337)
      ·
        refine ⟨6794919225073224407440003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9059892300097632543253337 6794919225073224407440003)
        ·
          refine ⟨10192378837609836611160005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794919225073224407440003 10192378837609836611160005)
          ·
            refine ⟨1911071032051844364592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10192378837609836611160005 1911071032051844364592501)
            ·
              refine ⟨179162909254860409180547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1911071032051844364592501 179162909254860409180547)
              ·
                refine ⟨268744363882290613770821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179162909254860409180547 268744363882290613770821)
                ·
                  refine ⟨50389568227929490082029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268744363882290613770821 50389568227929490082029)
                  ·
                    rfl

theorem cell21_220800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_220800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220800 prefixEnd_220800 := by exact prefixLift 220800
  have htrace : WordTrace (prefixWord ++ tailWord_220800) baseStart_220800 baseEnd_220800 := by
    simpa [prefixWord, tailWord_220800, baseEnd_220800] using wordTrace_append hprefix tailTrace_220800
  have hstable : (prefixWord ++ tailWord_220800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220800).length < 2 ^ (prefixWord ++ tailWord_220800).sum := by decide
  have hdescent : baseEnd_220800 < baseStart_220800 := by decide
  rcases family_descends (prefixWord ++ tailWord_220800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220814 : List Nat := [4, 1, 1, 3, 1, 3, 1, 7]
def baseStart_220814 : Nat := 118140960795 + 220814 * 2 ^ 59
def prefixEnd_220814 : Nat := 4983230072969 + 3 ^ 40 * 220814 * 2
def baseEnd_220814 : Nat := 16797587739556192282889

theorem tailTrace_220814 : CollatzResearch.WordTrace tailWord_220814 prefixEnd_220814 16797587739556192282889 := by
  unfold tailWord_220814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006718527754508109237687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5369165481357376582600997 1006718527754508109237687)
  ·
    refine ⟨1510077791631762163856531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006718527754508109237687 1510077791631762163856531)
    ·
      refine ⟨2265116687447643245784797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510077791631762163856531 2265116687447643245784797)
      ·
        refine ⟨849418757792866217169299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2265116687447643245784797 849418757792866217169299)
        ·
          refine ⟨1274128136689299325753949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849418757792866217169299 1274128136689299325753949)
          ·
            refine ⟨477798051258487247157731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274128136689299325753949 477798051258487247157731)
            ·
              refine ⟨716697076887730870736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477798051258487247157731 716697076887730870736597)
              ·
                refine ⟨16797587739556192282889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 716697076887730870736597 16797587739556192282889)
                ·
                  rfl

theorem cell21_220814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_220814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220814 prefixEnd_220814 := by exact prefixLift 220814
  have htrace : WordTrace (prefixWord ++ tailWord_220814) baseStart_220814 baseEnd_220814 := by
    simpa [prefixWord, tailWord_220814, baseEnd_220814] using wordTrace_append hprefix tailTrace_220814
  have hstable : (prefixWord ++ tailWord_220814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220814).length < 2 ^ (prefixWord ++ tailWord_220814).sum := by decide
  have hdescent : baseEnd_220814 < baseStart_220814 := by decide
  rcases family_descends (prefixWord ++ tailWord_220814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220820 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_220820 : Nat := 118140960795 + 220820 * 2 ^ 59
def prefixEnd_220820 : Nat := 4983230072969 + 3 ^ 40 * 220820 * 2
def baseEnd_220820 : Nat := 50394132500413899748655

theorem tailTrace_220820 : CollatzResearch.WordTrace tailWord_220820 prefixEnd_220820 50394132500413899748655 := by
  unfold tailWord_220820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026983530007163949309957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5369311373342885265746609 4026983530007163949309957)
  ·
    refine ⟨755059411876343240495617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4026983530007163949309957 755059411876343240495617)
    ·
      refine ⟨566294558907257430371713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755059411876343240495617 566294558907257430371713)
      ·
        refine ⟨424720919180443072778785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566294558907257430371713 424720919180443072778785)
        ·
          refine ⟨318540689385332304584089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424720919180443072778785 318540689385332304584089)
          ·
            refine ⟨238905517038999228438067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318540689385332304584089 238905517038999228438067)
            ·
              refine ⟨358358275558498842657101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238905517038999228438067 358358275558498842657101)
              ·
                refine ⟨134384353334437065996413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358358275558498842657101 134384353334437065996413)
                ·
                  refine ⟨50394132500413899748655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134384353334437065996413 50394132500413899748655)
                  ·
                    rfl

theorem cell21_220820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_220820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220820 prefixEnd_220820 := by exact prefixLift 220820
  have htrace : WordTrace (prefixWord ++ tailWord_220820) baseStart_220820 baseEnd_220820 := by
    simpa [prefixWord, tailWord_220820, baseEnd_220820] using wordTrace_append hprefix tailTrace_220820
  have hstable : (prefixWord ++ tailWord_220820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220820).length < 2 ^ (prefixWord ++ tailWord_220820).sum := by decide
  have hdescent : baseEnd_220820 < baseStart_220820 := by decide
  rcases family_descends (prefixWord ++ tailWord_220820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220831 : List Nat := [1, 1, 2, 7, 1, 2, 7]
def baseStart_220831 : Nat := 118140960795 + 220831 * 2 ^ 59
def prefixEnd_220831 : Nat := 4983230072969 + 3 ^ 40 * 220831 * 2
def baseEnd_220831 : Nat := 5599626983364480562811

theorem tailTrace_220831 : CollatzResearch.WordTrace tailWord_220831 prefixEnd_220831 5599626983364480562811 := by
  unfold tailWord_220831
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054368262974476777270347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5369578841982984518180231 8054368262974476777270347)
  ·
    refine ⟨12081552394461715165905521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8054368262974476777270347 12081552394461715165905521)
    ·
      refine ⟨9061164295846286374429141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12081552394461715165905521 9061164295846286374429141)
      ·
        refine ⟨212371038183897336900683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9061164295846286374429141 212371038183897336900683)
        ·
          refine ⟨318556557275846005351025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212371038183897336900683 318556557275846005351025)
          ·
            refine ⟨238917417956884504013269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318556557275846005351025 238917417956884504013269)
            ·
              refine ⟨5599626983364480562811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238917417956884504013269 5599626983364480562811)
              ·
                rfl

theorem cell21_220831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 7].length) (baseStart_220831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220831 prefixEnd_220831 := by exact prefixLift 220831
  have htrace : WordTrace (prefixWord ++ tailWord_220831) baseStart_220831 baseEnd_220831 := by
    simpa [prefixWord, tailWord_220831, baseEnd_220831] using wordTrace_append hprefix tailTrace_220831
  have hstable : (prefixWord ++ tailWord_220831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220831).length < 2 ^ (prefixWord ++ tailWord_220831).sum := by decide
  have hdescent : baseEnd_220831 < baseStart_220831 := by decide
  rcases family_descends (prefixWord ++ tailWord_220831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220938 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_220938 : Nat := 118140960795 + 220938 * 2 ^ 59
def prefixEnd_220938 : Nat := 4983230072969 + 3 ^ 40 * 220938 * 2
def baseEnd_220938 : Nat := 50421061708071916781747

theorem tailTrace_220938 : CollatzResearch.WordTrace tailWord_220938 prefixEnd_220938 50421061708071916781747 := by
  unfold tailWord_220938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014567718396708512853867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5372180582391222700943645 2014567718396708512853867)
  ·
    refine ⟨3021851577595062769280801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014567718396708512853867 3021851577595062769280801)
    ·
      refine ⟨2266388683196297076960601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3021851577595062769280801 2266388683196297076960601)
      ·
        refine ⟨1699791512397222807720451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266388683196297076960601 1699791512397222807720451)
        ·
          refine ⟨2549687268595834211580677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699791512397222807720451 2549687268595834211580677)
          ·
            refine ⟨478066362861718914671377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2549687268595834211580677 478066362861718914671377)
            ·
              refine ⟨358549772146289186003533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478066362861718914671377 358549772146289186003533)
              ·
                refine ⟨134456164554858444751325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358549772146289186003533 134456164554858444751325)
                ·
                  refine ⟨50421061708071916781747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134456164554858444751325 50421061708071916781747)
                  ·
                    rfl

theorem cell21_220938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_220938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220938 prefixEnd_220938 := by exact prefixLift 220938
  have htrace : WordTrace (prefixWord ++ tailWord_220938) baseStart_220938 baseEnd_220938 := by
    simpa [prefixWord, tailWord_220938, baseEnd_220938] using wordTrace_append hprefix tailTrace_220938
  have hstable : (prefixWord ++ tailWord_220938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220938).length < 2 ^ (prefixWord ++ tailWord_220938).sum := by decide
  have hdescent : baseEnd_220938 < baseStart_220938 := by decide
  rcases family_descends (prefixWord ++ tailWord_220938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220941 : List Nat := [1, 7, 2, 1, 1, 1, 8]
def baseStart_220941 : Nat := 118140960795 + 220941 * 2 ^ 59
def prefixEnd_220941 : Nat := 4983230072969 + 3 ^ 40 * 220941 * 2
def baseEnd_220941 : Nat := 5602416260993842025749

theorem tailTrace_220941 : CollatzResearch.WordTrace tailWord_220941 prefixEnd_220941 5602416260993842025749 := by
  unfold tailWord_220941
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058380292575965563774677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372253528383977042516451 8058380292575965563774677)
  ·
    refine ⟨188868288107249192900969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8058380292575965563774677 188868288107249192900969)
    ·
      refine ⟨141651216080436894675727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188868288107249192900969 141651216080436894675727)
      ·
        refine ⟨212476824120655342013591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141651216080436894675727 212476824120655342013591)
        ·
          refine ⟨318715236180983013020387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212476824120655342013591 318715236180983013020387)
          ·
            refine ⟨478072854271474519530581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318715236180983013020387 478072854271474519530581)
            ·
              refine ⟨5602416260993842025749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 478072854271474519530581 5602416260993842025749)
              ·
                rfl

theorem cell21_220941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 8].length) (baseStart_220941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220941 prefixEnd_220941 := by exact prefixLift 220941
  have htrace : WordTrace (prefixWord ++ tailWord_220941) baseStart_220941 baseEnd_220941 := by
    simpa [prefixWord, tailWord_220941, baseEnd_220941] using wordTrace_append hprefix tailTrace_220941
  have hstable : (prefixWord ++ tailWord_220941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220941).length < 2 ^ (prefixWord ++ tailWord_220941).sum := by decide
  have hdescent : baseEnd_220941 < baseStart_220941 := by decide
  rcases family_descends (prefixWord ++ tailWord_220941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220949 : List Nat := [1, 3, 2, 1, 2, 4, 8]
def baseStart_220949 : Nat := 118140960795 + 220949 * 2 ^ 59
def prefixEnd_220949 : Nat := 4983230072969 + 3 ^ 40 * 220949 * 2
def baseEnd_220949 : Nat := 5602619117548704677599

theorem tailTrace_220949 : CollatzResearch.WordTrace tailWord_220949 prefixEnd_220949 5602619117548704677599 := by
  unfold tailWord_220949
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058672076546982930065901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372448051031321953377267 8058672076546982930065901)
  ·
    refine ⟨3022002028705118598774713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8058672076546982930065901 3022002028705118598774713)
    ·
      refine ⟨2266501521528838949081035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3022002028705118598774713 2266501521528838949081035)
      ·
        refine ⟨3399752282293258423621553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266501521528838949081035 3399752282293258423621553)
        ·
          refine ⟨2549814211719943817716165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399752282293258423621553 2549814211719943817716165)
          ·
            refine ⟨478090164697489465821781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2549814211719943817716165 478090164697489465821781)
            ·
              refine ⟨5602619117548704677599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 478090164697489465821781 5602619117548704677599)
              ·
                rfl

theorem cell21_220949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 8].length) (baseStart_220949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_220949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_220949 prefixEnd_220949 := by exact prefixLift 220949
  have htrace : WordTrace (prefixWord ++ tailWord_220949) baseStart_220949 baseEnd_220949 := by
    simpa [prefixWord, tailWord_220949, baseEnd_220949] using wordTrace_append hprefix tailTrace_220949
  have hstable : (prefixWord ++ tailWord_220949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220949).length < 2 ^ (prefixWord ++ tailWord_220949).sum := by decide
  have hdescent : baseEnd_220949 < baseStart_220949 := by decide
  rcases family_descends (prefixWord ++ tailWord_220949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221025 : List Nat := [1, 2, 3, 1, 1, 1, 6, 6]
def baseStart_221025 : Nat := 118140960795 + 221025 * 2 ^ 59
def prefixEnd_221025 : Nat := 4983230072969 + 3 ^ 40 * 221025 * 2
def baseEnd_221025 : Nat := 16813638764459699610523

theorem tailTrace_221025 : CollatzResearch.WordTrace tailWord_221025 prefixEnd_221025 16813638764459699610523 := by
  unfold tailWord_221025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061444024271647909832529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374296016181098606555019 8061444024271647909832529)
  ·
    refine ⟨6046083018203735932374397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8061444024271647909832529 6046083018203735932374397)
    ·
      refine ⟨2267281131826400974640399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6046083018203735932374397 2267281131826400974640399)
      ·
        refine ⟨3400921697739601461960599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267281131826400974640399 3400921697739601461960599)
        ·
          refine ⟨5101382546609402192940899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400921697739601461960599 5101382546609402192940899)
          ·
            refine ⟨7652073819914103289411349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101382546609402192940899 7652073819914103289411349)
            ·
              refine ⟨358690960308473591691157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7652073819914103289411349 358690960308473591691157)
              ·
                refine ⟨16813638764459699610523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358690960308473591691157 16813638764459699610523)
                ·
                  rfl

theorem cell21_221025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_221025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221025 prefixEnd_221025 := by exact prefixLift 221025
  have htrace : WordTrace (prefixWord ++ tailWord_221025) baseStart_221025 baseEnd_221025 := by
    simpa [prefixWord, tailWord_221025, baseEnd_221025] using wordTrace_append hprefix tailTrace_221025
  have hstable : (prefixWord ++ tailWord_221025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221025).length < 2 ^ (prefixWord ++ tailWord_221025).sum := by decide
  have hdescent : baseEnd_221025 < baseStart_221025 := by decide
  rcases family_descends (prefixWord ++ tailWord_221025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221028 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_221028 : Nat := 118140960795 + 221028 * 2 ^ 59
def prefixEnd_221028 : Nat := 4983230072969 + 3 ^ 40 * 221028 * 2
def baseEnd_221028 : Nat := 50441600934251760281563

theorem tailTrace_221028 : CollatzResearch.WordTrace tailWord_221028 prefixEnd_221028 50441600934251760281563 := by
  unfold tailWord_221028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030776721630389711095869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5374368962173852948127825 4030776721630389711095869)
  ·
    refine ⟨1511541270611396141660951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4030776721630389711095869 1511541270611396141660951)
    ·
      refine ⟨2267311905917094212491427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511541270611396141660951 2267311905917094212491427)
      ·
        refine ⟨3400967858875641318737141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267311905917094212491427 3400967858875641318737141)
        ·
          refine ⟨318840736769591373631607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3400967858875641318737141 318840736769591373631607)
          ·
            refine ⟨478261105154387060447411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318840736769591373631607 478261105154387060447411)
            ·
              refine ⟨717391657731580590671117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478261105154387060447411 717391657731580590671117)
              ·
                refine ⟨269021871649342721501669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717391657731580590671117 269021871649342721501669)
                ·
                  refine ⟨50441600934251760281563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269021871649342721501669 50441600934251760281563)
                  ·
                    rfl

theorem cell21_221028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_221028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221028 prefixEnd_221028 := by exact prefixLift 221028
  have htrace : WordTrace (prefixWord ++ tailWord_221028) baseStart_221028 baseEnd_221028 := by
    simpa [prefixWord, tailWord_221028, baseEnd_221028] using wordTrace_append hprefix tailTrace_221028
  have hstable : (prefixWord ++ tailWord_221028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221028).length < 2 ^ (prefixWord ++ tailWord_221028).sum := by decide
  have hdescent : baseEnd_221028 < baseStart_221028 := by decide
  rcases family_descends (prefixWord ++ tailWord_221028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221132 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_221132 : Nat := 118140960795 + 221132 * 2 ^ 59
def prefixEnd_221132 : Nat := 4983230072969 + 3 ^ 40 * 221132 * 2
def baseEnd_221132 : Nat := 50465335151170690548017

theorem tailTrace_221132 : CollatzResearch.WordTrace tailWord_221132 prefixEnd_221132 50465335151170690548017 := by
  unfold tailWord_221132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032673317442002591988825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5376897756589336789318433 4032673317442002591988825)
  ·
    refine ⟨3024504988081501943991619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4032673317442002591988825 3024504988081501943991619)
    ·
      refine ⟨4536757482122252915987429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024504988081501943991619 4536757482122252915987429)
      ·
        refine ⟨850642027897922421747643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4536757482122252915987429 850642027897922421747643)
        ·
          refine ⟨1275963041846883632621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850642027897922421747643 1275963041846883632621465)
          ·
            refine ⟨956972281385162724466099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275963041846883632621465 956972281385162724466099)
            ·
              refine ⟨1435458422077744086699149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956972281385162724466099 1435458422077744086699149)
              ·
                refine ⟨538296908279154032512181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1435458422077744086699149 538296908279154032512181)
                ·
                  refine ⟨50465335151170690548017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538296908279154032512181 50465335151170690548017)
                  ·
                    rfl

theorem cell21_221132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_221132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221132 prefixEnd_221132 := by exact prefixLift 221132
  have htrace : WordTrace (prefixWord ++ tailWord_221132) baseStart_221132 baseEnd_221132 := by
    simpa [prefixWord, tailWord_221132, baseEnd_221132] using wordTrace_append hprefix tailTrace_221132
  have hstable : (prefixWord ++ tailWord_221132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221132).length < 2 ^ (prefixWord ++ tailWord_221132).sum := by decide
  have hdescent : baseEnd_221132 < baseStart_221132 := by decide
  rcases family_descends (prefixWord ++ tailWord_221132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221166 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_221166 : Nat := 118140960795 + 221166 * 2 ^ 59
def prefixEnd_221166 : Nat := 4983230072969 + 3 ^ 40 * 221166 * 2
def baseEnd_221166 : Nat := 50473094414394186981281

theorem tailTrace_221166 : CollatzResearch.WordTrace tailWord_221166 prefixEnd_221166 50473094414394186981281 := by
  unfold tailWord_221166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008323339595103623839419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5377724477840552660476901 1008323339595103623839419)
  ·
    refine ⟨1512485009392655435759129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008323339595103623839419 1512485009392655435759129)
    ·
      refine ⟨1134363757044491576819347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512485009392655435759129 1134363757044491576819347)
      ·
        refine ⟨1701545635566737365229021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134363757044491576819347 1701545635566737365229021)
        ·
          refine ⟨638079613337526511960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1701545635566737365229021 638079613337526511960883)
          ·
            refine ⟨957119420006289767941325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638079613337526511960883 957119420006289767941325)
            ·
              refine ⟨358919782502358662977997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957119420006289767941325 358919782502358662977997)
              ·
                refine ⟨134594918438384498616749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358919782502358662977997 134594918438384498616749)
                ·
                  refine ⟨50473094414394186981281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134594918438384498616749 50473094414394186981281)
                  ·
                    rfl

theorem cell21_221166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_221166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221166 prefixEnd_221166 := by exact prefixLift 221166
  have htrace : WordTrace (prefixWord ++ tailWord_221166) baseStart_221166 baseEnd_221166 := by
    simpa [prefixWord, tailWord_221166, baseEnd_221166] using wordTrace_append hprefix tailTrace_221166
  have hstable : (prefixWord ++ tailWord_221166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221166).length < 2 ^ (prefixWord ++ tailWord_221166).sum := by decide
  have hdescent : baseEnd_221166 < baseStart_221166 := by decide
  rcases family_descends (prefixWord ++ tailWord_221166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221177 : List Nat := [1, 2, 1, 3, 1, 6, 7]
def baseStart_221177 : Nat := 118140960795 + 221177 * 2 ^ 59
def prefixEnd_221177 : Nat := 4983230072969 + 3 ^ 40 * 221177 * 2
def baseEnd_221177 : Nat := 5608400529362290255325

theorem tailTrace_221177 : CollatzResearch.WordTrace tailWord_221177 prefixEnd_221177 5608400529362290255325 := by
  unfold tailWord_221177
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066987919720977869365785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5377991946480651912910523 8066987919720977869365785)
  ·
    refine ⟨6050240939790733402024339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8066987919720977869365785 6050240939790733402024339)
    ·
      refine ⟨9075361409686100103036509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050240939790733402024339 9075361409686100103036509)
      ·
        refine ⟨3403260528632287538638691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9075361409686100103036509 3403260528632287538638691)
        ·
          refine ⟨5104890792948431307958037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403260528632287538638691 5104890792948431307958037)
          ·
            refine ⟨239291755919457717560533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5104890792948431307958037 239291755919457717560533)
            ·
              refine ⟨5608400529362290255325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239291755919457717560533 5608400529362290255325)
              ·
                rfl

theorem cell21_221177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 7].length) (baseStart_221177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221177 prefixEnd_221177 := by exact prefixLift 221177
  have htrace : WordTrace (prefixWord ++ tailWord_221177) baseStart_221177 baseEnd_221177 := by
    simpa [prefixWord, tailWord_221177, baseEnd_221177] using wordTrace_append hprefix tailTrace_221177
  have hstable : (prefixWord ++ tailWord_221177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221177).length < 2 ^ (prefixWord ++ tailWord_221177).sum := by decide
  have hdescent : baseEnd_221177 < baseStart_221177 := by decide
  rcases family_descends (prefixWord ++ tailWord_221177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221194 : List Nat := [3, 1, 2, 2, 4, 1, 2, 6]
def baseStart_221194 : Nat := 118140960795 + 221194 * 2 ^ 59
def prefixEnd_221194 : Nat := 4983230072969 + 3 ^ 40 * 221194 * 2
def baseEnd_221194 : Nat := 16826494798624120171519

theorem tailTrace_221194 : CollatzResearch.WordTrace tailWord_221194 prefixEnd_221194 16826494798624120171519 := by
  unfold tailWord_221194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016901990164847443183659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5378405307106259848489757 2016901990164847443183659)
  ·
    refine ⟨3025352985247271164775489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2016901990164847443183659 3025352985247271164775489)
    ·
      refine ⟨2269014738935453373581617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025352985247271164775489 2269014738935453373581617)
      ·
        refine ⟨1701761054201590030186213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269014738935453373581617 1701761054201590030186213)
        ·
          refine ⟨319080197662798130659915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1701761054201590030186213 319080197662798130659915)
          ·
            refine ⟨478620296494197195989873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319080197662798130659915 478620296494197195989873)
            ·
              refine ⟨358965222370647896992405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478620296494197195989873 358965222370647896992405)
              ·
                refine ⟨16826494798624120171519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358965222370647896992405 16826494798624120171519)
                ·
                  rfl

theorem cell21_221194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_221194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221194 prefixEnd_221194 := by exact prefixLift 221194
  have htrace : WordTrace (prefixWord ++ tailWord_221194) baseStart_221194 baseEnd_221194 := by
    simpa [prefixWord, tailWord_221194, baseEnd_221194] using wordTrace_append hprefix tailTrace_221194
  have hstable : (prefixWord ++ tailWord_221194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221194).length < 2 ^ (prefixWord ++ tailWord_221194).sum := by decide
  have hdescent : baseEnd_221194 < baseStart_221194 := by decide
  rcases family_descends (prefixWord ++ tailWord_221194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221312 : List Nat := [2, 1, 1, 2, 1, 3, 1, 10]
def baseStart_221312 : Nat := 118140960795 + 221312 * 2 ^ 59
def prefixEnd_221312 : Nat := 4983230072969 + 3 ^ 40 * 221312 * 2
def baseEnd_221312 : Nat := 16835471201176792515883

theorem tailTrace_221312 : CollatzResearch.WordTrace tailWord_221312 prefixEnd_221312 16835471201176792515883 := by
  unfold tailWord_221312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035955887115947962765095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5381274516154597283686793 4035955887115947962765095)
  ·
    refine ⟨6053933830673921944147643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035955887115947962765095 6053933830673921944147643)
    ·
      refine ⟨9080900746010882916221465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053933830673921944147643 9080900746010882916221465)
      ·
        refine ⟨6810675559508162187166099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080900746010882916221465 6810675559508162187166099)
        ·
          refine ⟨10216013339262243280749149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810675559508162187166099 10216013339262243280749149)
          ·
            refine ⟨3831005002223341230280931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10216013339262243280749149 3831005002223341230280931)
            ·
              refine ⟨5746507503335011845421397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831005002223341230280931 5746507503335011845421397)
              ·
                refine ⟨16835471201176792515883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5746507503335011845421397 16835471201176792515883)
                ·
                  rfl

theorem cell21_221312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_221312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221312 prefixEnd_221312 := by exact prefixLift 221312
  have htrace : WordTrace (prefixWord ++ tailWord_221312) baseStart_221312 baseEnd_221312 := by
    simpa [prefixWord, tailWord_221312, baseEnd_221312] using wordTrace_append hprefix tailTrace_221312
  have hstable : (prefixWord ++ tailWord_221312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221312).length < 2 ^ (prefixWord ++ tailWord_221312).sum := by decide
  have hdescent : baseEnd_221312 < baseStart_221312 := by decide
  rcases family_descends (prefixWord ++ tailWord_221312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221335 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 3]
def baseStart_221335 : Nat := 118140960795 + 221335 * 2 ^ 59
def prefixEnd_221335 : Nat := 4983230072969 + 3 ^ 40 * 221335 * 2
def baseEnd_221335 : Nat := 50511662516887448664269

theorem tailTrace_221335 : CollatzResearch.WordTrace tailWord_221335 prefixEnd_221335 50511662516887448664269 := by
  unfold tailWord_221335
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072750653148570853617459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5381833768765713902411639 8072750653148570853617459)
  ·
    refine ⟨12109125979722856280426189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8072750653148570853617459 12109125979722856280426189)
    ·
      refine ⟨4540922242396071105159821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12109125979722856280426189 4540922242396071105159821)
      ·
        refine ⟨1702845840898526664434933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4540922242396071105159821 1702845840898526664434933)
        ·
          refine ⟨159641797584236874790775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1702845840898526664434933 159641797584236874790775)
          ·
            refine ⟨239462696376355312186163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159641797584236874790775 239462696376355312186163)
            ·
              refine ⟨359194044564532968279245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239462696376355312186163 359194044564532968279245)
              ·
                refine ⟨134697766711699863104717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359194044564532968279245 134697766711699863104717)
                ·
                  refine ⟨50511662516887448664269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134697766711699863104717 50511662516887448664269)
                  ·
                    rfl

theorem cell21_221335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].length) (baseStart_221335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221335 prefixEnd_221335 := by exact prefixLift 221335
  have htrace : WordTrace (prefixWord ++ tailWord_221335) baseStart_221335 baseEnd_221335 := by
    simpa [prefixWord, tailWord_221335, baseEnd_221335] using wordTrace_append hprefix tailTrace_221335
  have hstable : (prefixWord ++ tailWord_221335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221335).length < 2 ^ (prefixWord ++ tailWord_221335).sum := by decide
  have hdescent : baseEnd_221335 < baseStart_221335 := by decide
  rcases family_descends (prefixWord ++ tailWord_221335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221346 : List Nat := [3, 3, 1, 3, 1, 3, 7]
def baseStart_221346 : Nat := 118140960795 + 221346 * 2 ^ 59
def prefixEnd_221346 : Nat := 4983230072969 + 3 ^ 40 * 221346 * 2
def baseEnd_221346 : Nat := 5612685874083763775657

theorem tailTrace_221346 : CollatzResearch.WordTrace tailWord_221346 prefixEnd_221346 5612685874083763775657 := by
  unfold tailWord_221346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018287964027179933066973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5382101237405813154845261 2018287964027179933066973)
  ·
    refine ⟨756857986510192474900115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2018287964027179933066973 756857986510192474900115)
    ·
      refine ⟨1135286979765288712350173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756857986510192474900115 1135286979765288712350173)
      ·
        refine ⟨425732617411983267131315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1135286979765288712350173 425732617411983267131315)
        ·
          refine ⟨638598926117974900696973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425732617411983267131315 638598926117974900696973)
          ·
            refine ⟨239474597294240587761365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638598926117974900696973 239474597294240587761365)
            ·
              refine ⟨5612685874083763775657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239474597294240587761365 5612685874083763775657)
              ·
                rfl

theorem cell21_221346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 7].length) (baseStart_221346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221346 prefixEnd_221346 := by exact prefixLift 221346
  have htrace : WordTrace (prefixWord ++ tailWord_221346) baseStart_221346 baseEnd_221346 := by
    simpa [prefixWord, tailWord_221346, baseEnd_221346] using wordTrace_append hprefix tailTrace_221346
  have hstable : (prefixWord ++ tailWord_221346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221346).length < 2 ^ (prefixWord ++ tailWord_221346).sum := by decide
  have hdescent : baseEnd_221346 < baseStart_221346 := by decide
  rcases family_descends (prefixWord ++ tailWord_221346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221405 : List Nat := [1, 4, 3, 2, 1, 10]
def baseStart_221405 : Nat := 118140960795 + 221405 * 2 ^ 59
def prefixEnd_221405 : Nat := 4983230072969 + 3 ^ 40 * 221405 * 2
def baseEnd_221405 : Nat := 1871393980391958611017

theorem tailTrace_221405 : CollatzResearch.WordTrace tailWord_221405 prefixEnd_221405 1871393980391958611017 := by
  unfold tailWord_221405
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075303762894972808665669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383535841929981872443779 8075303762894972808665669)
  ·
    refine ⟨1514119455542807401624813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8075303762894972808665669 1514119455542807401624813)
    ·
      refine ⟨567794795828552775609305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1514119455542807401624813 567794795828552775609305)
      ·
        refine ⟨425846096871414581706979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567794795828552775609305 425846096871414581706979)
        ·
          refine ⟨638769145307121872560469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425846096871414581706979 638769145307121872560469)
          ·
            refine ⟨1871393980391958611017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 638769145307121872560469 1871393980391958611017)
            ·
              rfl

theorem cell21_221405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 10].length) (baseStart_221405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221405 prefixEnd_221405 := by exact prefixLift 221405
  have htrace : WordTrace (prefixWord ++ tailWord_221405) baseStart_221405 baseEnd_221405 := by
    simpa [prefixWord, tailWord_221405, baseEnd_221405] using wordTrace_append hprefix tailTrace_221405
  have hstable : (prefixWord ++ tailWord_221405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221405).length < 2 ^ (prefixWord ++ tailWord_221405).sum := by decide
  have hdescent : baseEnd_221405 < baseStart_221405 := by decide
  rcases family_descends (prefixWord ++ tailWord_221405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221419 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_221419 : Nat := 118140960795 + 221419 * 2 ^ 59
def prefixEnd_221419 : Nat := 4983230072969 + 3 ^ 40 * 221419 * 2
def baseEnd_221419 : Nat := 50530832461321969264097

theorem tailTrace_221419 : CollatzResearch.WordTrace tailWord_221419 prefixEnd_221419 50530832461321969264097 := by
  unfold tailWord_221419
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075814384844253199675311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383876256562835466450207 8075814384844253199675311)
  ·
    refine ⟨12113721577266379799512967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075814384844253199675311 12113721577266379799512967)
    ·
      refine ⟨18170582365899569699269451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113721577266379799512967 18170582365899569699269451)
      ·
        refine ⟨27255873548849354548904177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18170582365899569699269451 27255873548849354548904177)
        ·
          refine ⟨20441905161637015911678133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27255873548849354548904177 20441905161637015911678133)
          ·
            refine ⟨1916428608903470241719825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20441905161637015911678133 1916428608903470241719825)
            ·
              refine ⟨1437321456677602681289869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916428608903470241719825 1437321456677602681289869)
              ·
                refine ⟨538995546254101005483701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437321456677602681289869 538995546254101005483701)
                ·
                  refine ⟨50530832461321969264097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538995546254101005483701 50530832461321969264097)
                  ·
                    rfl

theorem cell21_221419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_221419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221419 prefixEnd_221419 := by exact prefixLift 221419
  have htrace : WordTrace (prefixWord ++ tailWord_221419) baseStart_221419 baseEnd_221419 := by
    simpa [prefixWord, tailWord_221419, baseEnd_221419] using wordTrace_append hprefix tailTrace_221419
  have hstable : (prefixWord ++ tailWord_221419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221419).length < 2 ^ (prefixWord ++ tailWord_221419).sum := by decide
  have hdescent : baseEnd_221419 < baseStart_221419 := by decide
  rcases family_descends (prefixWord ++ tailWord_221419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221436 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_221436 : Nat := 118140960795 + 221436 * 2 ^ 59
def prefixEnd_221436 : Nat := 4983230072969 + 3 ^ 40 * 221436 * 2
def baseEnd_221436 : Nat := 50534712092933717480729

theorem tailTrace_221436 : CollatzResearch.WordTrace tailWord_221436 prefixEnd_221436 50534712092933717480729 := by
  unfold tailWord_221436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038217212891332551522081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5384289617188443402029441 4038217212891332551522081)
  ·
    refine ⟨3028662909668499413641561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4038217212891332551522081 3028662909668499413641561)
    ·
      refine ⟨2271497182251374560231171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028662909668499413641561 2271497182251374560231171)
      ·
        refine ⟨3407245773377061840346757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271497182251374560231171 3407245773377061840346757)
        ·
          refine ⟨638858582508199095065017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3407245773377061840346757 638858582508199095065017)
          ·
            refine ⟨479143936881149321298763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638858582508199095065017 479143936881149321298763)
            ·
              refine ⟨718715905321723981948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479143936881149321298763 718715905321723981948145)
              ·
                refine ⟨539036928991292986461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718715905321723981948145 539036928991292986461109)
                ·
                  refine ⟨50534712092933717480729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539036928991292986461109 50534712092933717480729)
                  ·
                    rfl

theorem cell21_221436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_221436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221436 prefixEnd_221436 := by exact prefixLift 221436
  have htrace : WordTrace (prefixWord ++ tailWord_221436) baseStart_221436 baseEnd_221436 := by
    simpa [prefixWord, tailWord_221436, baseEnd_221436] using wordTrace_append hprefix tailTrace_221436
  have hstable : (prefixWord ++ tailWord_221436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221436).length < 2 ^ (prefixWord ++ tailWord_221436).sum := by decide
  have hdescent : baseEnd_221436 < baseStart_221436 := by decide
  rcases family_descends (prefixWord ++ tailWord_221436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221464 : List Nat := [2, 1, 2, 3, 1, 2, 10]
def baseStart_221464 : Nat := 118140960795 + 221464 * 2 ^ 59
def prefixEnd_221464 : Nat := 4983230072969 + 3 ^ 40 * 221464 * 2
def baseEnd_221464 : Nat := 5615678008267987890445

theorem tailTrace_221464 : CollatzResearch.WordTrace tailWord_221464 prefixEnd_221464 5615678008267987890445 := by
  unfold tailWord_221464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038727834840612942531723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5384970446454150590042297 4038727834840612942531723)
  ·
    refine ⟨6058091752260919413797585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038727834840612942531723 6058091752260919413797585)
    ·
      refine ⟨4543568814195689560348189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6058091752260919413797585 4543568814195689560348189)
      ·
        refine ⟨1703838305323383585130571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4543568814195689560348189 1703838305323383585130571)
        ·
          refine ⟨2555757457985075377695857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703838305323383585130571 2555757457985075377695857)
          ·
            refine ⟨1916818093488806533271893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555757457985075377695857 1916818093488806533271893)
            ·
              refine ⟨5615678008267987890445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1916818093488806533271893 5615678008267987890445)
              ·
                rfl

theorem cell21_221464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 10].length) (baseStart_221464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221464 prefixEnd_221464 := by exact prefixLift 221464
  have htrace : WordTrace (prefixWord ++ tailWord_221464) baseStart_221464 baseEnd_221464 := by
    simpa [prefixWord, tailWord_221464, baseEnd_221464] using wordTrace_append hprefix tailTrace_221464
  have hstable : (prefixWord ++ tailWord_221464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221464).length < 2 ^ (prefixWord ++ tailWord_221464).sum := by decide
  have hdescent : baseEnd_221464 < baseStart_221464 := by decide
  rcases family_descends (prefixWord ++ tailWord_221464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221470 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_221470 : Nat := 118140960795 + 221470 * 2 ^ 59
def prefixEnd_221470 : Nat := 4983230072969 + 3 ^ 40 * 221470 * 2
def baseEnd_221470 : Nat := 50542471356157213913993

theorem tailTrace_221470 : CollatzResearch.WordTrace tailWord_221470 prefixEnd_221470 50542471356157213913993 := by
  unfold tailWord_221470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009709313457436113722733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5385116338439659273187909 1009709313457436113722733)
  ·
    refine ⟨378640992546538542646025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1009709313457436113722733 378640992546538542646025)
    ·
      refine ⟨283980744409903906984519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378640992546538542646025 283980744409903906984519)
      ·
        refine ⟨425971116614855860476779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283980744409903906984519 425971116614855860476779)
        ·
          refine ⟨638956674922283790715169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425971116614855860476779 638956674922283790715169)
          ·
            refine ⟨479217506191712843036377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638956674922283790715169 479217506191712843036377)
            ·
              refine ⟨359413129643784632277283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479217506191712843036377 359413129643784632277283)
              ·
                refine ⟨539119694465676948415925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359413129643784632277283 539119694465676948415925)
                ·
                  refine ⟨50542471356157213913993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539119694465676948415925 50542471356157213913993)
                  ·
                    rfl

theorem cell21_221470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_221470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221470 prefixEnd_221470 := by exact prefixLift 221470
  have htrace : WordTrace (prefixWord ++ tailWord_221470) baseStart_221470 baseEnd_221470 := by
    simpa [prefixWord, tailWord_221470, baseEnd_221470] using wordTrace_append hprefix tailTrace_221470
  have hstable : (prefixWord ++ tailWord_221470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221470).length < 2 ^ (prefixWord ++ tailWord_221470).sum := by decide
  have hdescent : baseEnd_221470 < baseStart_221470 := by decide
  rcases family_descends (prefixWord ++ tailWord_221470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221498 : List Nat := [3, 1, 1, 1, 4, 4, 2, 5]
def baseStart_221498 : Nat := 118140960795 + 221498 * 2 ^ 59
def prefixEnd_221498 : Nat := 4983230072969 + 3 ^ 40 * 221498 * 2
def baseEnd_221498 : Nat := 16849620445878462482423

theorem tailTrace_221498 : CollatzResearch.WordTrace tailWord_221498 prefixEnd_221498 16849620445878462482423 := by
  unfold tailWord_221498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019673937889512422950287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5385797167705366461200765 2019673937889512422950287)
  ·
    refine ⟨3029510906834268634425431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019673937889512422950287 3029510906834268634425431)
    ·
      refine ⟨4544266360251402951638147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029510906834268634425431 4544266360251402951638147)
      ·
        refine ⟨6816399540377104427457221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544266360251402951638147 6816399540377104427457221)
        ·
          refine ⟨1278074913820707080148229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6816399540377104427457221 1278074913820707080148229)
          ·
            refine ⟨239639046341382577527793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1278074913820707080148229 239639046341382577527793)
            ·
              refine ⟨179729284756036933145845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239639046341382577527793 179729284756036933145845)
              ·
                refine ⟨16849620445878462482423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179729284756036933145845 16849620445878462482423)
                ·
                  rfl

theorem cell21_221498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_221498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221498 prefixEnd_221498 := by exact prefixLift 221498
  have htrace : WordTrace (prefixWord ++ tailWord_221498) baseStart_221498 baseEnd_221498 := by
    simpa [prefixWord, tailWord_221498, baseEnd_221498] using wordTrace_append hprefix tailTrace_221498
  have hstable : (prefixWord ++ tailWord_221498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221498).length < 2 ^ (prefixWord ++ tailWord_221498).sum := by decide
  have hdescent : baseEnd_221498 < baseStart_221498 := by decide
  rcases family_descends (prefixWord ++ tailWord_221498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221543 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_221543 : Nat := 118140960795 + 221543 * 2 ^ 59
def prefixEnd_221543 : Nat := 4983230072969 + 3 ^ 40 * 221543 * 2
def baseEnd_221543 : Nat := 50559130950725309197177

theorem tailTrace_221543 : CollatzResearch.WordTrace tailWord_221543 prefixEnd_221543 50559130950725309197177 := by
  unfold tailWord_221543
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080337036395022377189283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5386891357596681584792855 8080337036395022377189283)
  ·
    refine ⟨12120505554592533565783925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8080337036395022377189283 12120505554592533565783925)
    ·
      refine ⟨1136297395743050021792243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12120505554592533565783925 1136297395743050021792243)
      ·
        refine ⟨1704446093614575032688365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136297395743050021792243 1704446093614575032688365)
        ·
          refine ⟨639167285105465637258137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1704446093614575032688365 639167285105465637258137)
          ·
            refine ⟨479375463829099227943603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639167285105465637258137 479375463829099227943603)
            ·
              refine ⟨719063195743648841915405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479375463829099227943603 719063195743648841915405)
              ·
                refine ⟨269648698403868315718277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719063195743648841915405 269648698403868315718277)
                ·
                  refine ⟨50559130950725309197177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269648698403868315718277 50559130950725309197177)
                  ·
                    rfl

theorem cell21_221543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_221543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221543 prefixEnd_221543 := by exact prefixLift 221543
  have htrace : WordTrace (prefixWord ++ tailWord_221543) baseStart_221543 baseEnd_221543 := by
    simpa [prefixWord, tailWord_221543, baseEnd_221543] using wordTrace_append hprefix tailTrace_221543
  have hstable : (prefixWord ++ tailWord_221543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221543).length < 2 ^ (prefixWord ++ tailWord_221543).sum := by decide
  have hdescent : baseEnd_221543 < baseStart_221543 := by decide
  rcases family_descends (prefixWord ++ tailWord_221543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221557 : List Nat := [1, 3, 4, 1, 2, 1, 2, 7]
def baseStart_221557 : Nat := 118140960795 + 221557 * 2 ^ 59
def prefixEnd_221557 : Nat := 4983230072969 + 3 ^ 40 * 221557 * 2
def baseEnd_221557 : Nat := 16854108647154798654605

theorem tailTrace_221557 : CollatzResearch.WordTrace tailWord_221557 prefixEnd_221557 16854108647154798654605 := by
  unfold tailWord_221557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080847658344302768198925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5387231772229535178799283 8080847658344302768198925)
  ·
    refine ⟨3030317871879113538074597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8080847658344302768198925 3030317871879113538074597)
    ·
      refine ⟨568184600977333788388987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3030317871879113538074597 568184600977333788388987)
      ·
        refine ⟨852276901466000682583481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568184600977333788388987 852276901466000682583481)
        ·
          refine ⟨639207676099500511937611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852276901466000682583481 639207676099500511937611)
          ·
            refine ⟨958811514149250767906417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639207676099500511937611 958811514149250767906417)
            ·
              refine ⟨719108635611938075929813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958811514149250767906417 719108635611938075929813)
              ·
                refine ⟨16854108647154798654605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 719108635611938075929813 16854108647154798654605)
                ·
                  rfl

theorem cell21_221557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_221557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221557 prefixEnd_221557 := by exact prefixLift 221557
  have htrace : WordTrace (prefixWord ++ tailWord_221557) baseStart_221557 baseEnd_221557 := by
    simpa [prefixWord, tailWord_221557, baseEnd_221557] using wordTrace_append hprefix tailTrace_221557
  have hstable : (prefixWord ++ tailWord_221557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221557).length < 2 ^ (prefixWord ++ tailWord_221557).sum := by decide
  have hdescent : baseEnd_221557 < baseStart_221557 := by decide
  rcases family_descends (prefixWord ++ tailWord_221557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221667 : List Nat := [1, 1, 1, 6, 4, 1, 2, 5]
def baseStart_221667 : Nat := 118140960795 + 221667 * 2 ^ 59
def prefixEnd_221667 : Nat := 4983230072969 + 3 ^ 40 * 221667 * 2
def baseEnd_221667 : Nat := 16862476480042883043419

theorem tailTrace_221667 : CollatzResearch.WordTrace tailWord_221667 prefixEnd_221667 16862476480042883043419 := by
  unfold tailWord_221667
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084859687945791554703255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5389906458630527703135503 8084859687945791554703255)
  ·
    refine ⟨12127289531918687332054883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8084859687945791554703255 12127289531918687332054883)
    ·
      refine ⟨18190934297878030998082325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127289531918687332054883 18190934297878030998082325)
      ·
        refine ⟨852700045213032703035109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18190934297878030998082325 852700045213032703035109)
        ·
          refine ⟨159881258477443631819083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 852700045213032703035109 159881258477443631819083)
          ·
            refine ⟨239821887716165447728625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159881258477443631819083 239821887716165447728625)
            ·
              refine ⟨179866415787124085796469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239821887716165447728625 179866415787124085796469)
              ·
                refine ⟨16862476480042883043419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179866415787124085796469 16862476480042883043419)
                ·
                  rfl

theorem cell21_221667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 5].length) (baseStart_221667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221667 prefixEnd_221667 := by exact prefixLift 221667
  have htrace : WordTrace (prefixWord ++ tailWord_221667) baseStart_221667 baseEnd_221667 := by
    simpa [prefixWord, tailWord_221667, baseEnd_221667] using wordTrace_append hprefix tailTrace_221667
  have hstable : (prefixWord ++ tailWord_221667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221667).length < 2 ^ (prefixWord ++ tailWord_221667).sum := by decide
  have hdescent : baseEnd_221667 < baseStart_221667 := by decide
  rcases family_descends (prefixWord ++ tailWord_221667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221678 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_221678 : Nat := 118140960795 + 221678 * 2 ^ 59
def prefixEnd_221678 : Nat := 4983230072969 + 3 ^ 40 * 221678 * 2
def baseEnd_221678 : Nat := 50589939789995074446901

theorem tailTrace_221678 : CollatzResearch.WordTrace tailWord_221678 prefixEnd_221678 50589939789995074446901 := by
  unfold tailWord_221678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010657611363242554169211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5390173927270626955569125 1010657611363242554169211)
  ·
    refine ⟨1515986417044863831253817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010657611363242554169211 1515986417044863831253817)
    ·
      refine ⟨1136989812783647873440363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1515986417044863831253817 1136989812783647873440363)
      ·
        refine ⟨1705484719175471810160545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136989812783647873440363 1705484719175471810160545)
        ·
          refine ⟨1279113539381603857620409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705484719175471810160545 1279113539381603857620409)
          ·
            refine ⟨959335154536202893215307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279113539381603857620409 959335154536202893215307)
            ·
              refine ⟨1439002731804304339822961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959335154536202893215307 1439002731804304339822961)
              ·
                refine ⟨1079252048853228254867221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439002731804304339822961 1079252048853228254867221)
                ·
                  refine ⟨50589939789995074446901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1079252048853228254867221 50589939789995074446901)
                  ·
                    rfl

theorem cell21_221678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_221678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221678 prefixEnd_221678 := by exact prefixLift 221678
  have htrace : WordTrace (prefixWord ++ tailWord_221678) baseStart_221678 baseEnd_221678 := by
    simpa [prefixWord, tailWord_221678, baseEnd_221678] using wordTrace_append hprefix tailTrace_221678
  have hstable : (prefixWord ++ tailWord_221678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221678).length < 2 ^ (prefixWord ++ tailWord_221678).sum := by decide
  have hdescent : baseEnd_221678 < baseStart_221678 := by decide
  rcases family_descends (prefixWord ++ tailWord_221678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221698 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_221698 : Nat := 118140960795 + 221698 * 2 ^ 59
def prefixEnd_221698 : Nat := 4983230072969 + 3 ^ 40 * 221698 * 2
def baseEnd_221698 : Nat := 50594504062479484113527

theorem tailTrace_221698 : CollatzResearch.WordTrace tailWord_221698 prefixEnd_221698 50594504062479484113527 := by
  unfold tailWord_221698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021497587708370962270437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5390660233888989232721165 2021497587708370962270437)
  ·
    refine ⟨379030797695319555425707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2021497587708370962270437 379030797695319555425707)
    ·
      refine ⟨568546196542979333138561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379030797695319555425707 568546196542979333138561)
      ·
        refine ⟨426409647407234499853921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568546196542979333138561 426409647407234499853921)
        ·
          refine ⟨319807235555425874890441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426409647407234499853921 319807235555425874890441)
          ·
            refine ⟨239855426666569406167831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319807235555425874890441 239855426666569406167831)
            ·
              refine ⟨359783139999854109251747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239855426666569406167831 359783139999854109251747)
              ·
                refine ⟨539674709999781163877621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359783139999854109251747 539674709999781163877621)
                ·
                  refine ⟨50594504062479484113527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539674709999781163877621 50594504062479484113527)
                  ·
                    rfl

theorem cell21_221698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_221698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221698 prefixEnd_221698 := by exact prefixLift 221698
  have htrace : WordTrace (prefixWord ++ tailWord_221698) baseStart_221698 baseEnd_221698 := by
    simpa [prefixWord, tailWord_221698, baseEnd_221698] using wordTrace_append hprefix tailTrace_221698
  have hstable : (prefixWord ++ tailWord_221698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221698).length < 2 ^ (prefixWord ++ tailWord_221698).sum := by decide
  have hdescent : baseEnd_221698 < baseStart_221698 := by decide
  rcases family_descends (prefixWord ++ tailWord_221698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221754 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_221754 : Nat := 118140960795 + 221754 * 2 ^ 59
def prefixEnd_221754 : Nat := 4983230072969 + 3 ^ 40 * 221754 * 2
def baseEnd_221754 : Nat := 50607284025435831180079

theorem tailTrace_221754 : CollatzResearch.WordTrace tailWord_221754 prefixEnd_221754 50607284025435831180079 := by
  unfold tailWord_221754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022008209657651353280079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5392021892420403608746877 2022008209657651353280079)
  ·
    refine ⟨3033012314486477029920119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2022008209657651353280079 3033012314486477029920119)
    ·
      refine ⟨4549518471729715544880179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033012314486477029920119 4549518471729715544880179)
      ·
        refine ⟨6824277707594573317320269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549518471729715544880179 6824277707594573317320269)
        ·
          refine ⟨2559104140347964993995101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6824277707594573317320269 2559104140347964993995101)
          ·
            refine ⟨959664052630486872748163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2559104140347964993995101 959664052630486872748163)
            ·
              refine ⟨1439496078945730309122245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959664052630486872748163 1439496078945730309122245)
              ·
                refine ⟨269905514802324432960421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1439496078945730309122245 269905514802324432960421)
                ·
                  refine ⟨50607284025435831180079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269905514802324432960421 50607284025435831180079)
                  ·
                    rfl

theorem cell21_221754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_221754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221754 prefixEnd_221754 := by exact prefixLift 221754
  have htrace : WordTrace (prefixWord ++ tailWord_221754) baseStart_221754 baseEnd_221754 := by
    simpa [prefixWord, tailWord_221754, baseEnd_221754] using wordTrace_append hprefix tailTrace_221754
  have hstable : (prefixWord ++ tailWord_221754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221754).length < 2 ^ (prefixWord ++ tailWord_221754).sum := by decide
  have hdescent : baseEnd_221754 < baseStart_221754 := by decide
  rcases family_descends (prefixWord ++ tailWord_221754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221757 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 3]
def baseStart_221757 : Nat := 118140960795 + 221757 * 2 ^ 59
def prefixEnd_221757 : Nat := 4983230072969 + 3 ^ 40 * 221757 * 2
def baseEnd_221757 : Nat := 50607968666308492630073

theorem tailTrace_221757 : CollatzResearch.WordTrace tailWord_221757 prefixEnd_221757 50607968666308492630073 := by
  unfold tailWord_221757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088142257619736925479525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5392094838413157950319683 8088142257619736925479525)
  ·
    refine ⟨1516526673303700673527411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8088142257619736925479525 1516526673303700673527411)
    ·
      refine ⟨2274790009955551010291117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516526673303700673527411 2274790009955551010291117)
      ·
        refine ⟨853046253733331628859169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2274790009955551010291117 853046253733331628859169)
        ·
          refine ⟨639784690299998721644377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853046253733331628859169 639784690299998721644377)
          ·
            refine ⟨479838517724999041233283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639784690299998721644377 479838517724999041233283)
            ·
              refine ⟨719757776587498561849925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479838517724999041233283 719757776587498561849925)
              ·
                refine ⟨134954583110155980346861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719757776587498561849925 134954583110155980346861)
                ·
                  refine ⟨50607968666308492630073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134954583110155980346861 50607968666308492630073)
                  ·
                    rfl

theorem cell21_221757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_221757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221757 prefixEnd_221757 := by exact prefixLift 221757
  have htrace : WordTrace (prefixWord ++ tailWord_221757) baseStart_221757 baseEnd_221757 := by
    simpa [prefixWord, tailWord_221757, baseEnd_221757] using wordTrace_append hprefix tailTrace_221757
  have hstable : (prefixWord ++ tailWord_221757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221757).length < 2 ^ (prefixWord ++ tailWord_221757).sum := by decide
  have hdescent : baseEnd_221757 < baseStart_221757 := by decide
  rcases family_descends (prefixWord ++ tailWord_221757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221875 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_221875 : Nat := 118140960795 + 221875 * 2 ^ 59
def prefixEnd_221875 : Nat := 4983230072969 + 3 ^ 40 * 221875 * 2
def baseEnd_221875 : Nat := 50634897873966509663165

theorem tailTrace_221875 : CollatzResearch.WordTrace tailWord_221875 prefixEnd_221875 50634897873966509663165 := by
  unfold tailWord_221875
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092446071192243078275079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5394964047461495385516719 8092446071192243078275079)
  ·
    refine ⟨12138669106788364617412619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8092446071192243078275079 12138669106788364617412619)
    ·
      refine ⟨18208003660182546926118929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12138669106788364617412619 18208003660182546926118929)
      ·
        refine ⟨13656002745136910194589197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18208003660182546926118929 13656002745136910194589197)
        ·
          refine ⟨5121001029426341322970949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13656002745136910194589197 5121001029426341322970949)
          ·
            refine ⟨960187693017438998057053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5121001029426341322970949 960187693017438998057053)
            ·
              refine ⟨360070384881539624271395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960187693017438998057053 360070384881539624271395)
              ·
                refine ⟨540105577322309436407093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360070384881539624271395 540105577322309436407093)
                ·
                  refine ⟨50634897873966509663165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540105577322309436407093 50634897873966509663165)
                  ·
                    rfl

theorem cell21_221875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_221875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221875 prefixEnd_221875 := by exact prefixLift 221875
  have htrace : WordTrace (prefixWord ++ tailWord_221875) baseStart_221875 baseEnd_221875 := by
    simpa [prefixWord, tailWord_221875, baseEnd_221875] using wordTrace_append hprefix tailTrace_221875
  have hstable : (prefixWord ++ tailWord_221875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221875).length < 2 ^ (prefixWord ++ tailWord_221875).sum := by decide
  have hdescent : baseEnd_221875 < baseStart_221875 := by decide
  rcases family_descends (prefixWord ++ tailWord_221875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221923 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_221923 : Nat := 118140960795 + 221923 * 2 ^ 59
def prefixEnd_221923 : Nat := 4983230072969 + 3 ^ 40 * 221923 * 2
def baseEnd_221923 : Nat := 50645852127929092863067

theorem tailTrace_221923 : CollatzResearch.WordTrace tailWord_221923 prefixEnd_221923 50645852127929092863067 := by
  unfold tailWord_221923
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094196775018347276022423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5396131183345564850681615 8094196775018347276022423)
  ·
    refine ⟨12141295162527520914033635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8094196775018347276022423 12141295162527520914033635)
    ·
      refine ⟨18211942743791281371050453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141295162527520914033635 18211942743791281371050453)
      ·
        refine ⟨426842408057608157133995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18211942743791281371050453 426842408057608157133995)
        ·
          refine ⟨640263612086412235700993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426842408057608157133995 640263612086412235700993)
          ·
            refine ⟨480197709064809176775745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640263612086412235700993 480197709064809176775745)
            ·
              refine ⟨360148281798606882581809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480197709064809176775745 360148281798606882581809)
              ·
                refine ⟨270111211348955161936357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360148281798606882581809 270111211348955161936357)
                ·
                  refine ⟨50645852127929092863067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270111211348955161936357 50645852127929092863067)
                  ·
                    rfl

theorem cell21_221923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_221923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221923 prefixEnd_221923 := by exact prefixLift 221923
  have htrace : WordTrace (prefixWord ++ tailWord_221923) baseStart_221923 baseEnd_221923 := by
    simpa [prefixWord, tailWord_221923, baseEnd_221923] using wordTrace_append hprefix tailTrace_221923
  have hstable : (prefixWord ++ tailWord_221923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221923).length < 2 ^ (prefixWord ++ tailWord_221923).sum := by decide
  have hdescent : baseEnd_221923 < baseStart_221923 := by decide
  rcases family_descends (prefixWord ++ tailWord_221923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221954 : List Nat := [3, 4, 1, 1, 1, 3, 3, 5]
def baseStart_221954 : Nat := 118140960795 + 221954 * 2 ^ 59
def prefixEnd_221954 : Nat := 4983230072969 + 3 ^ 40 * 221954 * 2
def baseEnd_221954 : Nat := 16884308916759975948779

theorem tailTrace_221954 : CollatzResearch.WordTrace tailWord_221954 prefixEnd_221954 16884308916759975948779 := by
  unfold tailWord_221954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023831859476509892600229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5396884958604026380267277 2023831859476509892600229)
  ·
    refine ⟨379468473651845604862543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2023831859476509892600229 379468473651845604862543)
    ·
      refine ⟨569202710477768407293815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379468473651845604862543 569202710477768407293815)
      ·
        refine ⟨853804065716652610940723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569202710477768407293815 853804065716652610940723)
        ·
          refine ⟨1280706098574978916411085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853804065716652610940723 1280706098574978916411085)
          ·
            refine ⟨480264786965617093654157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1280706098574978916411085 480264786965617093654157)
            ·
              refine ⟨180099295112106410120309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480264786965617093654157 180099295112106410120309)
              ·
                refine ⟨16884308916759975948779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180099295112106410120309 16884308916759975948779)
                ·
                  rfl

theorem cell21_221954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_221954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_221954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_221954 prefixEnd_221954 := by exact prefixLift 221954
  have htrace : WordTrace (prefixWord ++ tailWord_221954) baseStart_221954 baseEnd_221954 := by
    simpa [prefixWord, tailWord_221954, baseEnd_221954] using wordTrace_append hprefix tailTrace_221954
  have hstable : (prefixWord ++ tailWord_221954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221954).length < 2 ^ (prefixWord ++ tailWord_221954).sum := by decide
  have hdescent : baseEnd_221954 < baseStart_221954 := by decide
  rcases family_descends (prefixWord ++ tailWord_221954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222013 : List Nat := [1, 4, 1, 4, 2, 1, 1, 7]
def baseStart_222013 : Nat := 118140960795 + 222013 * 2 ^ 59
def prefixEnd_222013 : Nat := 4983230072969 + 3 ^ 40 * 222013 * 2
def baseEnd_222013 : Nat := 16888797118036312120961

theorem tailTrace_222013 : CollatzResearch.WordTrace tailWord_222013 prefixEnd_222013 16888797118036312120961 := by
  unfold tailWord_222013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097479344692292646798693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398319563128195097865795 8097479344692292646798693)
  ·
    refine ⟨1518277377129804871274755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8097479344692292646798693 1518277377129804871274755)
    ·
      refine ⟨2277416065694707306912133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518277377129804871274755 2277416065694707306912133)
      ·
        refine ⟨427015512317757620046025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2277416065694707306912133 427015512317757620046025)
        ·
          refine ⟨320261634238318215034519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427015512317757620046025 320261634238318215034519)
          ·
            refine ⟨480392451357477322551779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320261634238318215034519 480392451357477322551779)
            ·
              refine ⟨720588677036215983827669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480392451357477322551779 720588677036215983827669)
              ·
                refine ⟨16888797118036312120961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 720588677036215983827669 16888797118036312120961)
                ·
                  rfl

theorem cell21_222013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_222013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222013 prefixEnd_222013 := by exact prefixLift 222013
  have htrace : WordTrace (prefixWord ++ tailWord_222013) baseStart_222013 baseEnd_222013 := by
    simpa [prefixWord, tailWord_222013, baseEnd_222013] using wordTrace_append hprefix tailTrace_222013
  have hstable : (prefixWord ++ tailWord_222013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222013).length < 2 ^ (prefixWord ++ tailWord_222013).sum := by decide
  have hdescent : baseEnd_222013 < baseStart_222013 := by decide
  rcases family_descends (prefixWord ++ tailWord_222013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222041 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_222041 : Nat := 118140960795 + 222041 * 2 ^ 59
def prefixEnd_222041 : Nat := 4983230072969 + 3 ^ 40 * 222041 * 2
def baseEnd_222041 : Nat := 50672781335587109896159

theorem tailTrace_222041 : CollatzResearch.WordTrace tailWord_222041 prefixEnd_222041 50672781335587109896159 := by
  unfold tailWord_222041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098500588590853428817977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5399000392393902285878651 8098500588590853428817977)
  ·
    refine ⟨6073875441443140071613483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8098500588590853428817977 6073875441443140071613483)
    ·
      refine ⟨9110813162164710107420225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073875441443140071613483 9110813162164710107420225)
      ·
        refine ⟨6833109871623532580565169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9110813162164710107420225 6833109871623532580565169)
        ·
          refine ⟨5124832403717649435423877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6833109871623532580565169 5124832403717649435423877)
          ·
            refine ⟨960906075697059269141977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5124832403717649435423877 960906075697059269141977)
            ·
              refine ⟨720679556772794451856483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960906075697059269141977 720679556772794451856483)
              ·
                refine ⟨1081019335159191677784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720679556772794451856483 1081019335159191677784725)
                ·
                  refine ⟨50672781335587109896159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1081019335159191677784725 50672781335587109896159)
                  ·
                    rfl

theorem cell21_222041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_222041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222041 prefixEnd_222041 := by exact prefixLift 222041
  have htrace : WordTrace (prefixWord ++ tailWord_222041) baseStart_222041 baseEnd_222041 := by
    simpa [prefixWord, tailWord_222041, baseEnd_222041] using wordTrace_append hprefix tailTrace_222041
  have hstable : (prefixWord ++ tailWord_222041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222041).length < 2 ^ (prefixWord ++ tailWord_222041).sum := by decide
  have hdescent : baseEnd_222041 < baseStart_222041 := by decide
  rcases family_descends (prefixWord ++ tailWord_222041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222044 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_222044 : Nat := 118140960795 + 222044 * 2 ^ 59
def prefixEnd_222044 : Nat := 4983230072969 + 3 ^ 40 * 222044 * 2
def baseEnd_222044 : Nat := 50673465976459771346153

theorem tailTrace_222044 : CollatzResearch.WordTrace tailWord_222044 prefixEnd_222044 50673465976459771346153 := by
  unfold tailWord_222044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049305003789992470588593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5399073338386656627451457 4049305003789992470588593)
  ·
    refine ⟨3036978752842494352941445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4049305003789992470588593 3036978752842494352941445)
    ·
      refine ⟨569433516157967691176521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3036978752842494352941445 569433516157967691176521)
      ·
        refine ⟨427075137118475768382391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569433516157967691176521 427075137118475768382391)
        ·
          refine ⟨640612705677713652573587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427075137118475768382391 640612705677713652573587)
          ·
            refine ⟨960919058516570478860381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640612705677713652573587 960919058516570478860381)
            ·
              refine ⟨360344646943713929572643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960919058516570478860381 360344646943713929572643)
              ·
                refine ⟨540516970415570894358965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360344646943713929572643 540516970415570894358965)
                ·
                  refine ⟨50673465976459771346153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540516970415570894358965 50673465976459771346153)
                  ·
                    rfl

theorem cell21_222044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_222044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222044 prefixEnd_222044 := by exact prefixLift 222044
  have htrace : WordTrace (prefixWord ++ tailWord_222044) baseStart_222044 baseEnd_222044 := by
    simpa [prefixWord, tailWord_222044, baseEnd_222044] using wordTrace_append hprefix tailTrace_222044
  have hstable : (prefixWord ++ tailWord_222044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222044).length < 2 ^ (prefixWord ++ tailWord_222044).sum := by decide
  have hdescent : baseEnd_222044 < baseStart_222044 := by decide
  rcases family_descends (prefixWord ++ tailWord_222044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222106 : List Nat := [3, 1, 1, 4, 4, 1, 1, 6]
def baseStart_222106 : Nat := 118140960795 + 222106 * 2 ^ 59
def prefixEnd_222106 : Nat := 4983230072969 + 3 ^ 40 * 222106 * 2
def baseEnd_222106 : Nat := 16895871740387147104231

theorem tailTrace_222106 : CollatzResearch.WordTrace tailWord_222106 prefixEnd_222106 16895871740387147104231 := by
  unfold tailWord_222106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025217833338842382483543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5400580888903579686622781 2025217833338842382483543)
  ·
    refine ⟨3037826750008263573725315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025217833338842382483543 3037826750008263573725315)
    ·
      refine ⟨4556740125012395360587973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037826750008263573725315 4556740125012395360587973)
      ·
        refine ⟨854388773439824130110245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4556740125012395360587973 854388773439824130110245)
        ·
          refine ⟨160197895019967024395671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 854388773439824130110245 160197895019967024395671)
          ·
            refine ⟨240296842529950536593507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160197895019967024395671 240296842529950536593507)
            ·
              refine ⟨360445263794925804890261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240296842529950536593507 360445263794925804890261)
              ·
                refine ⟨16895871740387147104231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 360445263794925804890261 16895871740387147104231)
                ·
                  rfl

theorem cell21_222106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_222106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222106 prefixEnd_222106 := by exact prefixLift 222106
  have htrace : WordTrace (prefixWord ++ tailWord_222106) baseStart_222106 baseEnd_222106 := by
    simpa [prefixWord, tailWord_222106, baseEnd_222106] using wordTrace_append hprefix tailTrace_222106
  have hstable : (prefixWord ++ tailWord_222106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222106).length < 2 ^ (prefixWord ++ tailWord_222106).sum := by decide
  have hdescent : baseEnd_222106 < baseStart_222106 := by decide
  rcases family_descends (prefixWord ++ tailWord_222106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222193 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_222193 : Nat := 118140960795 + 222193 * 2 ^ 59
def prefixEnd_222193 : Nat := 4983230072969 + 3 ^ 40 * 222193 * 2
def baseEnd_222193 : Nat := 50707469806468623362515

theorem tailTrace_222193 : CollatzResearch.WordTrace tailWord_222193 prefixEnd_222193 50707469806468623362515 := by
  unfold tailWord_222193
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104044484040183388351233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5402696322693455592234155 8104044484040183388351233)
  ·
    refine ⟨6078033363030137541263425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8104044484040183388351233 6078033363030137541263425)
    ·
      refine ⟨4558525022272603155947569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078033363030137541263425 4558525022272603155947569)
      ·
        refine ⟨3418893766704452366960677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558525022272603155947569 3418893766704452366960677)
        ·
          refine ⟨641042581257084818805127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3418893766704452366960677 641042581257084818805127)
          ·
            refine ⟨961563871885627228207691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641042581257084818805127 961563871885627228207691)
            ·
              refine ⟨1442345807828440842311537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961563871885627228207691 1442345807828440842311537)
              ·
                refine ⟨1081759355871330631733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442345807828440842311537 1081759355871330631733653)
                ·
                  refine ⟨50707469806468623362515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1081759355871330631733653 50707469806468623362515)
                  ·
                    rfl

theorem cell21_222193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_222193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222193 prefixEnd_222193 := by exact prefixLift 222193
  have htrace : WordTrace (prefixWord ++ tailWord_222193) baseStart_222193 baseEnd_222193 := by
    simpa [prefixWord, tailWord_222193, baseEnd_222193] using wordTrace_append hprefix tailTrace_222193
  have hstable : (prefixWord ++ tailWord_222193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222193).length < 2 ^ (prefixWord ++ tailWord_222193).sum := by decide
  have hdescent : baseEnd_222193 < baseStart_222193 := by decide
  rcases family_descends (prefixWord ++ tailWord_222193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222618 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_222618 : Nat := 118140960795 + 222618 * 2 ^ 59
def prefixEnd_222618 : Nat := 4983230072969 + 3 ^ 40 * 222618 * 2
def baseEnd_222618 : Nat := 50804460596762328778313

theorem tailTrace_222618 : CollatzResearch.WordTrace tailWord_222618 prefixEnd_222618 50804460596762328778313 := by
  unfold tailWord_222618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029886376875120243143127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5413030338333653981715005 2029886376875120243143127)
  ·
    refine ⟨3044829565312680364714691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029886376875120243143127 3044829565312680364714691)
    ·
      refine ⟨4567244347969020547072037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044829565312680364714691 4567244347969020547072037)
      ·
        refine ⟨856358315244191352576007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4567244347969020547072037 856358315244191352576007)
        ·
          refine ⟨1284537472866287028864011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856358315244191352576007 1284537472866287028864011)
          ·
            refine ⟨1926806209299430543296017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284537472866287028864011 1926806209299430543296017)
            ·
              refine ⟨1445104656974572907472013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926806209299430543296017 1445104656974572907472013)
              ·
                refine ⟨541914246365464840302005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445104656974572907472013 541914246365464840302005)
                ·
                  refine ⟨50804460596762328778313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 541914246365464840302005 50804460596762328778313)
                  ·
                    rfl

theorem cell21_222618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_222618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222618 prefixEnd_222618 := by exact prefixLift 222618
  have htrace : WordTrace (prefixWord ++ tailWord_222618) baseStart_222618 baseEnd_222618 := by
    simpa [prefixWord, tailWord_222618, baseEnd_222618] using wordTrace_append hprefix tailTrace_222618
  have hstable : (prefixWord ++ tailWord_222618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222618).length < 2 ^ (prefixWord ++ tailWord_222618).sum := by decide
  have hdescent : baseEnd_222618 < baseStart_222618 := by decide
  rcases family_descends (prefixWord ++ tailWord_222618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222658 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_222658 : Nat := 118140960795 + 222658 * 2 ^ 59
def prefixEnd_222658 : Nat := 4983230072969 + 3 ^ 40 * 222658 * 2
def baseEnd_222658 : Nat := 50813589141731148111565

theorem tailTrace_222658 : CollatzResearch.WordTrace tailWord_222658 prefixEnd_222658 50813589141731148111565 := by
  unfold tailWord_222658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030251106838891951007157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5414002951570378536019085 2030251106838891951007157)
  ·
    refine ⟨190336041266146120406921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2030251106838891951007157 190336041266146120406921)
    ·
      refine ⟨142752030949609590305191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190336041266146120406921 142752030949609590305191)
      ·
        refine ⟨214128046424414385457787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142752030949609590305191 214128046424414385457787)
        ·
          refine ⟨321192069636621578186681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214128046424414385457787 321192069636621578186681)
          ·
            refine ⟨240894052227466183640011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321192069636621578186681 240894052227466183640011)
            ·
              refine ⟨361341078341199275460017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240894052227466183640011 361341078341199275460017)
              ·
                refine ⟨271005808755899456595013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361341078341199275460017 271005808755899456595013)
                ·
                  refine ⟨50813589141731148111565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271005808755899456595013 50813589141731148111565)
                  ·
                    rfl

theorem cell21_222658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_222658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222658 prefixEnd_222658 := by exact prefixLift 222658
  have htrace : WordTrace (prefixWord ++ tailWord_222658) baseStart_222658 baseEnd_222658 := by
    simpa [prefixWord, tailWord_222658, baseEnd_222658] using wordTrace_append hprefix tailTrace_222658
  have hstable : (prefixWord ++ tailWord_222658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222658).length < 2 ^ (prefixWord ++ tailWord_222658).sum := by decide
  have hdescent : baseEnd_222658 < baseStart_222658 := by decide
  rcases family_descends (prefixWord ++ tailWord_222658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222666 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_222666 : Nat := 118140960795 + 222666 * 2 ^ 59
def prefixEnd_222666 : Nat := 4983230072969 + 3 ^ 40 * 222666 * 2
def baseEnd_222666 : Nat := 50815414850724911978215

theorem tailTrace_222666 : CollatzResearch.WordTrace tailWord_222666 prefixEnd_222666 50815414850724911978215 := by
  unfold tailWord_222666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030324052831646292579963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5414197474217723446879901 2030324052831646292579963)
  ·
    refine ⟨3045486079247469438869945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030324052831646292579963 3045486079247469438869945)
    ·
      refine ⟨2284114559435602079152459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045486079247469438869945 2284114559435602079152459)
      ·
        refine ⟨3426171839153403118728689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284114559435602079152459 3426171839153403118728689)
        ·
          refine ⟨2569628879365052339046517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3426171839153403118728689 2569628879365052339046517)
          ·
            refine ⟨240902707440473656785611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2569628879365052339046517 240902707440473656785611)
            ·
              refine ⟨361354061160710485178417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240902707440473656785611 361354061160710485178417)
              ·
                refine ⟨271015545870532863883813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361354061160710485178417 271015545870532863883813)
                ·
                  refine ⟨50815414850724911978215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271015545870532863883813 50815414850724911978215)
                  ·
                    rfl

theorem cell21_222666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_222666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222666 prefixEnd_222666 := by exact prefixLift 222666
  have htrace : WordTrace (prefixWord ++ tailWord_222666) baseStart_222666 baseEnd_222666 := by
    simpa [prefixWord, tailWord_222666, baseEnd_222666] using wordTrace_append hprefix tailTrace_222666
  have hstable : (prefixWord ++ tailWord_222666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222666).length < 2 ^ (prefixWord ++ tailWord_222666).sum := by decide
  have hdescent : baseEnd_222666 < baseStart_222666 := by decide
  rcases family_descends (prefixWord ++ tailWord_222666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222739 : List Nat := [1, 1, 1, 2, 1, 7, 2, 6]
def baseStart_222739 : Nat := 118140960795 + 222739 * 2 ^ 59
def prefixEnd_222739 : Nat := 4983230072969 + 3 ^ 40 * 222739 * 2
def baseEnd_222739 : Nat := 16944024815097669087133

theorem tailTrace_222739 : CollatzResearch.WordTrace tailWord_222739 prefixEnd_222739 16944024815097669087133 := by
  unfold tailWord_222739
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123958740062118637727271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5415972493374745758484847 8123958740062118637727271)
  ·
    refine ⟨12185938110093177956590907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8123958740062118637727271 12185938110093177956590907)
    ·
      refine ⟨18278907165139766934886361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12185938110093177956590907 18278907165139766934886361)
      ·
        refine ⟨13709180373854825201164771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18278907165139766934886361 13709180373854825201164771)
        ·
          refine ⟨20563770560782237801747157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709180373854825201164771 20563770560782237801747157)
          ·
            refine ⟨481963372518333698478449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20563770560782237801747157 481963372518333698478449)
            ·
              refine ⟨361472529388750273858837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481963372518333698478449 361472529388750273858837)
              ·
                refine ⟨16944024815097669087133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361472529388750273858837 16944024815097669087133)
                ·
                  rfl

theorem cell21_222739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_222739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222739 prefixEnd_222739 := by exact prefixLift 222739
  have htrace : WordTrace (prefixWord ++ tailWord_222739) baseStart_222739 baseEnd_222739 := by
    simpa [prefixWord, tailWord_222739, baseEnd_222739] using wordTrace_append hprefix tailTrace_222739
  have hstable : (prefixWord ++ tailWord_222739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222739).length < 2 ^ (prefixWord ++ tailWord_222739).sum := by decide
  have hdescent : baseEnd_222739 < baseStart_222739 := by decide
  rcases family_descends (prefixWord ++ tailWord_222739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222790 : List Nat := [6, 1, 1, 1, 3, 2, 1, 6]
def baseStart_222790 : Nat := 118140960795 + 222790 * 2 ^ 59
def prefixEnd_222790 : Nat := 4983230072969 + 3 ^ 40 * 222790 * 2
def baseEnd_222790 : Nat := 16947904446709417303765

theorem tailTrace_222790 : CollatzResearch.WordTrace tailWord_222790 prefixEnd_222790 16947904446709417303765 := by
  unfold tailWord_222790
  simp only [CollatzResearch.WordTrace]
  refine ⟨253931839464917323369807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5417212575251569565222549 253931839464917323369807)
  ·
    refine ⟨380897759197375985054711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253931839464917323369807 380897759197375985054711)
    ·
      refine ⟨571346638796063977582067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380897759197375985054711 571346638796063977582067)
      ·
        refine ⟨857019958194095966373101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571346638796063977582067 857019958194095966373101)
        ·
          refine ⟨321382484322785987389913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857019958194095966373101 321382484322785987389913)
          ·
            refine ⟨241036863242089490542435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321382484322785987389913 241036863242089490542435)
            ·
              refine ⟨361555294863134235813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241036863242089490542435 361555294863134235813653)
              ·
                refine ⟨16947904446709417303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361555294863134235813653 16947904446709417303765)
                ·
                  rfl

theorem cell21_222790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_222790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222790 prefixEnd_222790 := by exact prefixLift 222790
  have htrace : WordTrace (prefixWord ++ tailWord_222790) baseStart_222790 baseEnd_222790 := by
    simpa [prefixWord, tailWord_222790, baseEnd_222790] using wordTrace_append hprefix tailTrace_222790
  have hstable : (prefixWord ++ tailWord_222790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222790).length < 2 ^ (prefixWord ++ tailWord_222790).sum := by decide
  have hdescent : baseEnd_222790 < baseStart_222790 := by decide
  rcases family_descends (prefixWord ++ tailWord_222790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222866 : List Nat := [3, 2, 3, 1, 4, 1, 2, 5]
def baseStart_222866 : Nat := 118140960795 + 222866 * 2 ^ 59
def prefixEnd_222866 : Nat := 4983230072969 + 3 ^ 40 * 222866 * 2
def baseEnd_222866 : Nat := 16953685858523002881491

theorem tailTrace_222866 : CollatzResearch.WordTrace tailWord_222866 prefixEnd_222866 16953685858523002881491 := by
  unfold tailWord_222866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032147702650504831900113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5419060540401346218400301 2032147702650504831900113)
  ·
    refine ⟨1524110776987878623925085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2032147702650504831900113 1524110776987878623925085)
    ·
      refine ⟨571541541370454483971907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1524110776987878623925085 571541541370454483971907)
      ·
        refine ⟨857312312055681725957861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571541541370454483971907 857312312055681725957861)
        ·
          refine ⟨160746058510440323617099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 857312312055681725957861 160746058510440323617099)
          ·
            refine ⟨241119087765660485425649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160746058510440323617099 241119087765660485425649)
            ·
              refine ⟨180839315824245364069237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241119087765660485425649 180839315824245364069237)
              ·
                refine ⟨16953685858523002881491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180839315824245364069237 16953685858523002881491)
                ·
                  rfl

theorem cell21_222866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_222866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222866 prefixEnd_222866 := by exact prefixLift 222866
  have htrace : WordTrace (prefixWord ++ tailWord_222866) baseStart_222866 baseEnd_222866 := by
    simpa [prefixWord, tailWord_222866, baseEnd_222866] using wordTrace_append hprefix tailTrace_222866
  have hstable : (prefixWord ++ tailWord_222866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222866).length < 2 ^ (prefixWord ++ tailWord_222866).sum := by decide
  have hdescent : baseEnd_222866 < baseStart_222866 := by decide
  rcases family_descends (prefixWord ++ tailWord_222866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222880 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_222880 : Nat := 118140960795 + 222880 * 2 ^ 59
def prefixEnd_222880 : Nat := 4983230072969 + 3 ^ 40 * 222880 * 2
def baseEnd_222880 : Nat := 50864252566308095411111

theorem tailTrace_222880 : CollatzResearch.WordTrace tailWord_222880 prefixEnd_222880 50864252566308095411111 := by
  unfold tailWord_222880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064550716275649859305047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5419400955034199812406729 4064550716275649859305047)
  ·
    refine ⟨6096826074413474788957571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064550716275649859305047 6096826074413474788957571)
    ·
      refine ⟨9145239111620212183436357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096826074413474788957571 9145239111620212183436357)
      ·
        refine ⟨1714732333428789784394317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9145239111620212183436357 1714732333428789784394317)
        ·
          refine ⟨643024625035796169147869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1714732333428789784394317 643024625035796169147869)
          ·
            refine ⟨241134234388423563430451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 643024625035796169147869 241134234388423563430451)
            ·
              refine ⟨361701351582635345145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241134234388423563430451 361701351582635345145677)
              ·
                refine ⟨135638006843488254429629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361701351582635345145677 135638006843488254429629)
                ·
                  refine ⟨50864252566308095411111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135638006843488254429629 50864252566308095411111)
                  ·
                    rfl

theorem cell21_222880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_222880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_222880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_222880 prefixEnd_222880 := by exact prefixLift 222880
  have htrace : WordTrace (prefixWord ++ tailWord_222880) baseStart_222880 baseEnd_222880 := by
    simpa [prefixWord, tailWord_222880, baseEnd_222880] using wordTrace_append hprefix tailTrace_222880
  have hstable : (prefixWord ++ tailWord_222880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222880).length < 2 ^ (prefixWord ++ tailWord_222880).sum := by decide
  have hdescent : baseEnd_222880 < baseStart_222880 := by decide
  rcases family_descends (prefixWord ++ tailWord_222880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223043 : List Nat := [1, 1, 1, 3, 1, 5, 4, 5]
def baseStart_223043 : Nat := 118140960795 + 223043 * 2 ^ 59
def prefixEnd_223043 : Nat := 4983230072969 + 3 ^ 40 * 223043 * 2
def baseEnd_223043 : Nat := 16967150462352011398037

theorem tailTrace_223043 : CollatzResearch.WordTrace tailWord_223043 prefixEnd_223043 16967150462352011398037 := by
  unfold tailWord_223043
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135046530960778556793783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5423364353973852371195855 8135046530960778556793783)
  ·
    refine ⟨12202569796441167835190675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135046530960778556793783 12202569796441167835190675)
    ·
      refine ⟨18303854694661751752786013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202569796441167835190675 18303854694661751752786013)
      ·
        refine ⟨6863945510498156907294755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18303854694661751752786013 6863945510498156907294755)
        ·
          refine ⟨10295918265747235360942133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863945510498156907294755 10295918265747235360942133)
          ·
            refine ⟨965242337413803315088325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10295918265747235360942133 965242337413803315088325)
            ·
              refine ⟨180982938265088121579061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 965242337413803315088325 180982938265088121579061)
              ·
                refine ⟨16967150462352011398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180982938265088121579061 16967150462352011398037)
                ·
                  rfl

theorem cell21_223043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].length) (baseStart_223043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223043 prefixEnd_223043 := by exact prefixLift 223043
  have htrace : WordTrace (prefixWord ++ tailWord_223043) baseStart_223043 baseEnd_223043 := by
    simpa [prefixWord, tailWord_223043, baseEnd_223043] using wordTrace_append hprefix tailTrace_223043
  have hstable : (prefixWord ++ tailWord_223043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223043).length < 2 ^ (prefixWord ++ tailWord_223043).sum := by decide
  have hdescent : baseEnd_223043 < baseStart_223043 := by decide
  rcases family_descends (prefixWord ++ tailWord_223043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223046 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_223046 : Nat := 118140960795 + 223046 * 2 ^ 59
def prefixEnd_223046 : Nat := 4983230072969 + 3 ^ 40 * 223046 * 2
def baseEnd_223046 : Nat := 50902136027928695644105

theorem tailTrace_223046 : CollatzResearch.WordTrace tailWord_223046 prefixEnd_223046 50902136027928695644105 := by
  unfold tailWord_223046
  simp only [CollatzResearch.WordTrace]
  refine ⟨254223623435934689661031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5423437299966606712768661 254223623435934689661031)
  ·
    refine ⟨381335435153902034491547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254223623435934689661031 381335435153902034491547)
    ·
      refine ⟨572003152730853051737321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381335435153902034491547 572003152730853051737321)
      ·
        refine ⟨429002364548139788802991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572003152730853051737321 429002364548139788802991)
        ·
          refine ⟨643503546822209683204487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429002364548139788802991 643503546822209683204487)
          ·
            refine ⟨965255320233314524806731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643503546822209683204487 965255320233314524806731)
            ·
              refine ⟨1447882980349971787210097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965255320233314524806731 1447882980349971787210097)
              ·
                refine ⟨1085912235262478840407573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447882980349971787210097 1085912235262478840407573)
                ·
                  refine ⟨50902136027928695644105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1085912235262478840407573 50902136027928695644105)
                  ·
                    rfl

theorem cell21_223046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_223046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223046 prefixEnd_223046 := by exact prefixLift 223046
  have htrace : WordTrace (prefixWord ++ tailWord_223046) baseStart_223046 baseEnd_223046 := by
    simpa [prefixWord, tailWord_223046, baseEnd_223046] using wordTrace_append hprefix tailTrace_223046
  have hstable : (prefixWord ++ tailWord_223046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223046).length < 2 ^ (prefixWord ++ tailWord_223046).sum := by decide
  have hdescent : baseEnd_223046 < baseStart_223046 := by decide
  rcases family_descends (prefixWord ++ tailWord_223046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223122 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_223122 : Nat := 118140960795 + 223122 * 2 ^ 59
def prefixEnd_223122 : Nat := 4983230072969 + 3 ^ 40 * 223122 * 2
def baseEnd_223122 : Nat := 50919480263369452377283

theorem tailTrace_223122 : CollatzResearch.WordTrace tailWord_223122 prefixEnd_223122 50919480263369452377283 := by
  unfold tailWord_223122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034481974418643762229905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5425285265116383365946413 2034481974418643762229905)
  ·
    refine ⟨1525861480813982821672429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2034481974418643762229905 1525861480813982821672429)
    ·
      refine ⟨572198055305243558127161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1525861480813982821672429 572198055305243558127161)
      ·
        refine ⟨429148541478932668595371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572198055305243558127161 429148541478932668595371)
        ·
          refine ⟨643722812218399002893057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429148541478932668595371 643722812218399002893057)
          ·
            refine ⟨482792109163799252169793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643722812218399002893057 482792109163799252169793)
            ·
              refine ⟨362094081872849439127345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482792109163799252169793 362094081872849439127345)
              ·
                refine ⟨271570561404637079345509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362094081872849439127345 271570561404637079345509)
                ·
                  refine ⟨50919480263369452377283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271570561404637079345509 50919480263369452377283)
                  ·
                    rfl

theorem cell21_223122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_223122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223122 prefixEnd_223122 := by exact prefixLift 223122
  have htrace : WordTrace (prefixWord ++ tailWord_223122) baseStart_223122 baseEnd_223122 := by
    simpa [prefixWord, tailWord_223122, baseEnd_223122] using wordTrace_append hprefix tailTrace_223122
  have hstable : (prefixWord ++ tailWord_223122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223122).length < 2 ^ (prefixWord ++ tailWord_223122).sum := by decide
  have hdescent : baseEnd_223122 < baseStart_223122 := by decide
  rcases family_descends (prefixWord ++ tailWord_223122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223240 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_223240 : Nat := 118140960795 + 223240 * 2 ^ 59
def prefixEnd_223240 : Nat := 4983230072969 + 3 ^ 40 * 223240 * 2
def baseEnd_223240 : Nat := 50946409471027469410375

theorem tailTrace_223240 : CollatzResearch.WordTrace tailWord_223240 prefixEnd_223240 50946409471027469410375 := by
  unfold tailWord_223240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071115855623540600857587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5428154474164720801143449 4071115855623540600857587)
  ·
    refine ⟨6106673783435310901286381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071115855623540600857587 6106673783435310901286381)
    ·
      refine ⟨2290002668788241587982393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6106673783435310901286381 2290002668788241587982393)
      ·
        refine ⟨1717502001591181190986795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2290002668788241587982393 1717502001591181190986795)
        ·
          refine ⟨2576253002386771786480193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717502001591181190986795 2576253002386771786480193)
          ·
            refine ⟨1932189751790078839860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576253002386771786480193 1932189751790078839860145)
            ·
              refine ⟨1449142313842559129895109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932189751790078839860145 1449142313842559129895109)
              ·
                refine ⟨271714183845479836855333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1449142313842559129895109 271714183845479836855333)
                ·
                  refine ⟨50946409471027469410375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271714183845479836855333 50946409471027469410375)
                  ·
                    rfl

theorem cell21_223240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_223240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223240 prefixEnd_223240 := by exact prefixLift 223240
  have htrace : WordTrace (prefixWord ++ tailWord_223240) baseStart_223240 baseEnd_223240 := by
    simpa [prefixWord, tailWord_223240, baseEnd_223240] using wordTrace_append hprefix tailTrace_223240
  have hstable : (prefixWord ++ tailWord_223240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223240).length < 2 ^ (prefixWord ++ tailWord_223240).sum := by decide
  have hdescent : baseEnd_223240 < baseStart_223240 := by decide
  rcases family_descends (prefixWord ++ tailWord_223240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223243 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 3]
def baseStart_223243 : Nat := 118140960795 + 223243 * 2 ^ 59
def prefixEnd_223243 : Nat := 4983230072969 + 3 ^ 40 * 223243 * 2
def baseEnd_223243 : Nat := 50947094111900130860369

theorem tailTrace_223243 : CollatzResearch.WordTrace tailWord_223243 prefixEnd_223243 50947094111900130860369 := by
  unfold tailWord_223243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142341130236212714074383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5428227420157475142716255 8142341130236212714074383)
  ·
    refine ⟨12213511695354319071111575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8142341130236212714074383 12213511695354319071111575)
    ·
      refine ⟨18320267543031478606667363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213511695354319071111575 18320267543031478606667363)
      ·
        refine ⟨27480401314547217910001045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18320267543031478606667363 27480401314547217910001045)
        ·
          refine ⟨1288143811619400839531299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27480401314547217910001045 1288143811619400839531299)
          ·
            refine ⟨1932215717429101259296949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288143811619400839531299 1932215717429101259296949)
            ·
              refine ⟨181145223508978243059089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1932215717429101259296949 181145223508978243059089)
              ·
                refine ⟨135858917631733682294317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181145223508978243059089 135858917631733682294317)
                ·
                  refine ⟨50947094111900130860369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135858917631733682294317 50947094111900130860369)
                  ·
                    rfl

theorem cell21_223243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].length) (baseStart_223243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223243 prefixEnd_223243 := by exact prefixLift 223243
  have htrace : WordTrace (prefixWord ++ tailWord_223243) baseStart_223243 baseEnd_223243 := by
    simpa [prefixWord, tailWord_223243, baseEnd_223243] using wordTrace_append hprefix tailTrace_223243
  have hstable : (prefixWord ++ tailWord_223243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223243).length < 2 ^ (prefixWord ++ tailWord_223243).sum := by decide
  have hdescent : baseEnd_223243 < baseStart_223243 := by decide
  rcases family_descends (prefixWord ++ tailWord_223243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223294 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_223294 : Nat := 118140960795 + 223294 * 2 ^ 59
def prefixEnd_223294 : Nat := 4983230072969 + 3 ^ 40 * 223294 * 2
def baseEnd_223294 : Nat := 50958733006735375510265

theorem tailTrace_223294 : CollatzResearch.WordTrace tailWord_223294 prefixEnd_223294 50958733006735375510265 := by
  unfold tailWord_223294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018025156631431053022617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5429467502034298949453957 1018025156631431053022617)
  ·
    refine ⟨763518867473573289766963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018025156631431053022617 763518867473573289766963)
    ·
      refine ⟨1145278301210359934650445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763518867473573289766963 1145278301210359934650445)
      ·
        refine ⟨429479362953884975493917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1145278301210359934650445 429479362953884975493917)
        ·
          refine ⟨161054761107706865810219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429479362953884975493917 161054761107706865810219)
          ·
            refine ⟨241582141661560298715329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161054761107706865810219 241582141661560298715329)
            ·
              refine ⟨181186606246170224036497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241582141661560298715329 181186606246170224036497)
              ·
                refine ⟨135889954684627668027373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181186606246170224036497 135889954684627668027373)
                ·
                  refine ⟨50958733006735375510265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135889954684627668027373 50958733006735375510265)
                  ·
                    rfl

theorem cell21_223294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_223294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223294 prefixEnd_223294 := by exact prefixLift 223294
  have htrace : WordTrace (prefixWord ++ tailWord_223294) baseStart_223294 baseEnd_223294 := by
    simpa [prefixWord, tailWord_223294, baseEnd_223294] using wordTrace_append hprefix tailTrace_223294
  have hstable : (prefixWord ++ tailWord_223294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223294).length < 2 ^ (prefixWord ++ tailWord_223294).sum := by decide
  have hdescent : baseEnd_223294 < baseStart_223294 := by decide
  rcases family_descends (prefixWord ++ tailWord_223294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223350 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_223350 : Nat := 118140960795 + 223350 * 2 ^ 59
def prefixEnd_223350 : Nat := 4983230072969 + 3 ^ 40 * 223350 * 2
def baseEnd_223350 : Nat := 50971512969691722576817

theorem tailTrace_223350 : CollatzResearch.WordTrace tailWord_223350 prefixEnd_223350 50971512969691722576817 := by
  unfold tailWord_223350
  simp only [CollatzResearch.WordTrace]
  refine ⟨509140233803035624263719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5430829160565713325479669 509140233803035624263719)
  ·
    refine ⟨763710350704553436395579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509140233803035624263719 763710350704553436395579)
    ·
      refine ⟨1145565526056830154593369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763710350704553436395579 1145565526056830154593369)
      ·
        refine ⟨859174144542622615945027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145565526056830154593369 859174144542622615945027)
        ·
          refine ⟨1288761216813933923917541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859174144542622615945027 1288761216813933923917541)
          ·
            refine ⟨241642728152612610734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1288761216813933923917541 241642728152612610734539)
            ·
              refine ⟨362464092228918916101809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241642728152612610734539 362464092228918916101809)
              ·
                refine ⟨271848069171689187076357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362464092228918916101809 271848069171689187076357)
                ·
                  refine ⟨50971512969691722576817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271848069171689187076357 50971512969691722576817)
                  ·
                    rfl

theorem cell21_223350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_223350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223350 prefixEnd_223350 := by exact prefixLift 223350
  have htrace : WordTrace (prefixWord ++ tailWord_223350) baseStart_223350 baseEnd_223350 := by
    simpa [prefixWord, tailWord_223350, baseEnd_223350] using wordTrace_append hprefix tailTrace_223350
  have hstable : (prefixWord ++ tailWord_223350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223350).length < 2 ^ (prefixWord ++ tailWord_223350).sum := by decide
  have hdescent : baseEnd_223350 < baseStart_223350 := by decide
  rcases family_descends (prefixWord ++ tailWord_223350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223468 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_223468 : Nat := 118140960795 + 223468 * 2 ^ 59
def prefixEnd_223468 : Nat := 4983230072969 + 3 ^ 40 * 223468 * 2
def baseEnd_223468 : Nat := 50998442177349739609909

theorem tailTrace_223468 : CollatzResearch.WordTrace tailWord_223468 prefixEnd_223468 50998442177349739609909 := by
  unfold tailWord_223468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075273777210538070507529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5433698369614050760676705 4075273777210538070507529)
  ·
    refine ⟨3056455332907903552880647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4075273777210538070507529 3056455332907903552880647)
    ·
      refine ⟨4584682999361855329320971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056455332907903552880647 4584682999361855329320971)
      ·
        refine ⟨6877024499042782993981457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584682999361855329320971 6877024499042782993981457)
        ·
          refine ⟨5157768374282087245486093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877024499042782993981457 5157768374282087245486093)
          ·
            refine ⟨1934163140355782717057285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5157768374282087245486093 1934163140355782717057285)
            ·
              refine ⟨362655588816709259448241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1934163140355782717057285 362655588816709259448241)
              ·
                refine ⟨271991691612531944586181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362655588816709259448241 271991691612531944586181)
                ·
                  refine ⟨50998442177349739609909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271991691612531944586181 50998442177349739609909)
                  ·
                    rfl

theorem cell21_223468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_223468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223468 prefixEnd_223468 := by exact prefixLift 223468
  have htrace : WordTrace (prefixWord ++ tailWord_223468) baseStart_223468 baseEnd_223468 := by
    simpa [prefixWord, tailWord_223468, baseEnd_223468] using wordTrace_append hprefix tailTrace_223468
  have hstable : (prefixWord ++ tailWord_223468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223468).length < 2 ^ (prefixWord ++ tailWord_223468).sum := by decide
  have hdescent : baseEnd_223468 < baseStart_223468 := by decide
  rcases family_descends (prefixWord ++ tailWord_223468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223471 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 3]
def baseStart_223471 : Nat := 118140960795 + 223471 * 2 ^ 59
def prefixEnd_223471 : Nat := 4983230072969 + 3 ^ 40 * 223471 * 2
def baseEnd_223471 : Nat := 50999126818222401059903

theorem tailTrace_223471 : CollatzResearch.WordTrace tailWord_223471 prefixEnd_223471 50999126818222401059903 := by
  unfold tailWord_223471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150656973410207653374267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5433771315606805102249511 8150656973410207653374267)
  ·
    refine ⟨12225985460115311480061401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150656973410207653374267 12225985460115311480061401)
    ·
      refine ⟨9169489095086483610046051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12225985460115311480061401 9169489095086483610046051)
      ·
        refine ⟨13754233642629725415069077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9169489095086483610046051 13754233642629725415069077)
        ·
          refine ⟨644729701998268378831363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13754233642629725415069077 644729701998268378831363)
          ·
            refine ⟨967094552997402568247045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644729701998268378831363 967094552997402568247045)
            ·
              refine ⟨181330228687012981546321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967094552997402568247045 181330228687012981546321)
              ·
                refine ⟨135997671515259736159741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181330228687012981546321 135997671515259736159741)
                ·
                  refine ⟨50999126818222401059903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135997671515259736159741 50999126818222401059903)
                  ·
                    rfl

theorem cell21_223471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].length) (baseStart_223471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223471 prefixEnd_223471 := by exact prefixLift 223471
  have htrace : WordTrace (prefixWord ++ tailWord_223471) baseStart_223471 baseEnd_223471 := by
    simpa [prefixWord, tailWord_223471, baseEnd_223471] using wordTrace_append hprefix tailTrace_223471
  have hstable : (prefixWord ++ tailWord_223471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223471).length < 2 ^ (prefixWord ++ tailWord_223471).sum := by decide
  have hdescent : baseEnd_223471 < baseStart_223471 := by decide
  rcases family_descends (prefixWord ++ tailWord_223471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223482 : List Nat := [3, 1, 1, 1, 1, 5, 3, 6]
def baseStart_223482 : Nat := 118140960795 + 223482 * 2 ^ 59
def prefixEnd_223482 : Nat := 4983230072969 + 3 ^ 40 * 223482 * 2
def baseEnd_223482 : Nat := 17000545722696275458849

theorem tailTrace_223482 : CollatzResearch.WordTrace tailWord_223482 prefixEnd_223482 17000545722696275458849 := by
  unfold tailWord_223482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037764544092589133006175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5434038784246904354683133 2037764544092589133006175)
  ·
    refine ⟨3056646816138883699509263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037764544092589133006175 3056646816138883699509263)
    ·
      refine ⟨4584970224208325549263895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056646816138883699509263 4584970224208325549263895)
      ·
        refine ⟨6877455336312488323895843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584970224208325549263895 6877455336312488323895843)
        ·
          refine ⟨10316183004468732485843765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877455336312488323895843 10316183004468732485843765)
          ·
            refine ⟨967142156668943670547853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10316183004468732485843765 967142156668943670547853)
            ·
              refine ⟨362678308750853876455445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967142156668943670547853 362678308750853876455445)
              ·
                refine ⟨17000545722696275458849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362678308750853876455445 17000545722696275458849)
                ·
                  rfl

theorem cell21_223482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_223482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223482 prefixEnd_223482 := by exact prefixLift 223482
  have htrace : WordTrace (prefixWord ++ tailWord_223482) baseStart_223482 baseEnd_223482 := by
    simpa [prefixWord, tailWord_223482, baseEnd_223482] using wordTrace_append hprefix tailTrace_223482
  have hstable : (prefixWord ++ tailWord_223482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223482).length < 2 ^ (prefixWord ++ tailWord_223482).sum := by decide
  have hdescent : baseEnd_223482 < baseStart_223482 := by decide
  rcases family_descends (prefixWord ++ tailWord_223482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223589 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_223589 : Nat := 118140960795 + 223589 * 2 ^ 59
def prefixEnd_223589 : Nat := 4983230072969 + 3 ^ 40 * 223589 * 2
def baseEnd_223589 : Nat := 51026056025880418092995

theorem tailTrace_223589 : CollatzResearch.WordTrace tailWord_223589 prefixEnd_223589 51026056025880418092995 := by
  unfold tailWord_223589
  simp only [CollatzResearch.WordTrace]
  refine ⟨8154960786982713806169821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5436640524655142537446547 8154960786982713806169821)
  ·
    refine ⟨3058110295118517677313683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8154960786982713806169821 3058110295118517677313683)
    ·
      refine ⟨4587165442677776515970525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058110295118517677313683 4587165442677776515970525)
      ·
        refine ⟨1720187041004166193488947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4587165442677776515970525 1720187041004166193488947)
        ·
          refine ⟨2580280561506249290233421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720187041004166193488947 2580280561506249290233421)
          ·
            refine ⟨967605210564843483837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2580280561506249290233421 967605210564843483837533)
            ·
              refine ⟨362851953961816306439075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967605210564843483837533 362851953961816306439075)
              ·
                refine ⟨544277930942724459658613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362851953961816306439075 544277930942724459658613)
                ·
                  refine ⟨51026056025880418092995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544277930942724459658613 51026056025880418092995)
                  ·
                    rfl

theorem cell21_223589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_223589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223589 prefixEnd_223589 := by exact prefixLift 223589
  have htrace : WordTrace (prefixWord ++ tailWord_223589) baseStart_223589 baseEnd_223589 := by
    simpa [prefixWord, tailWord_223589, baseEnd_223589] using wordTrace_append hprefix tailTrace_223589
  have hstable : (prefixWord ++ tailWord_223589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223589).length < 2 ^ (prefixWord ++ tailWord_223589).sum := by decide
  have hdescent : baseEnd_223589 < baseStart_223589 := by decide
  rcases family_descends (prefixWord ++ tailWord_223589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223603 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_223603 : Nat := 118140960795 + 223603 * 2 ^ 59
def prefixEnd_223603 : Nat := 4983230072969 + 3 ^ 40 * 223603 * 2
def baseEnd_223603 : Nat := 51029251016619504859633

theorem tailTrace_223603 : CollatzResearch.WordTrace tailWord_223603 prefixEnd_223603 51029251016619504859633 := by
  unfold tailWord_223603
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155471408931994197179463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5436980939287996131452975 8155471408931994197179463)
  ·
    refine ⟨12233207113397991295769195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155471408931994197179463 12233207113397991295769195)
    ·
      refine ⟨18349810670096986943653793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233207113397991295769195 18349810670096986943653793)
      ·
        refine ⟨13762358002572740207740345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18349810670096986943653793 13762358002572740207740345)
        ·
          refine ⟨10321768501929555155805259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13762358002572740207740345 10321768501929555155805259)
          ·
            refine ⟨15482652752894332733707889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10321768501929555155805259 15482652752894332733707889)
            ·
              refine ⟨11611989564670749550280917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15482652752894332733707889 11611989564670749550280917)
              ·
                refine ⟨272156005421970692584709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11611989564670749550280917 272156005421970692584709)
                ·
                  refine ⟨51029251016619504859633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272156005421970692584709 51029251016619504859633)
                  ·
                    rfl

theorem cell21_223603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_223603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223603 prefixEnd_223603 := by exact prefixLift 223603
  have htrace : WordTrace (prefixWord ++ tailWord_223603) baseStart_223603 baseEnd_223603 := by
    simpa [prefixWord, tailWord_223603, baseEnd_223603] using wordTrace_append hprefix tailTrace_223603
  have hstable : (prefixWord ++ tailWord_223603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223603).length < 2 ^ (prefixWord ++ tailWord_223603).sum := by decide
  have hdescent : baseEnd_223603 < baseStart_223603 := by decide
  rcases family_descends (prefixWord ++ tailWord_223603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223640 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_223640 : Nat := 118140960795 + 223640 * 2 ^ 59
def prefixEnd_223640 : Nat := 4983230072969 + 3 ^ 40 * 223640 * 2
def baseEnd_223640 : Nat := 51037694920715662742891

theorem tailTrace_223640 : CollatzResearch.WordTrace tailWord_223640 prefixEnd_223640 51037694920715662742891 := by
  unfold tailWord_223640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4078410454898974758138187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5437880606531966344184249 4078410454898974758138187)
  ·
    refine ⟨6117615682348462137207281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4078410454898974758138187 6117615682348462137207281)
    ·
      refine ⟨4588211761761346602905461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6117615682348462137207281 4588211761761346602905461)
      ·
        refine ⟨430144852665126244022387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4588211761761346602905461 430144852665126244022387)
        ·
          refine ⟨645217278997689366033581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430144852665126244022387 645217278997689366033581)
          ·
            refine ⟨241956479624133512262593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645217278997689366033581 241956479624133512262593)
            ·
              refine ⟨181467359718100134196945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241956479624133512262593 181467359718100134196945)
              ·
                refine ⟨136100519788575100647709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181467359718100134196945 136100519788575100647709)
                ·
                  refine ⟨51037694920715662742891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136100519788575100647709 51037694920715662742891)
                  ·
                    rfl

theorem cell21_223640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_223640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223640 prefixEnd_223640 := by exact prefixLift 223640
  have htrace : WordTrace (prefixWord ++ tailWord_223640) baseStart_223640 baseEnd_223640 := by
    simpa [prefixWord, tailWord_223640, baseEnd_223640] using wordTrace_append hprefix tailTrace_223640
  have hstable : (prefixWord ++ tailWord_223640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223640).length < 2 ^ (prefixWord ++ tailWord_223640).sum := by decide
  have hdescent : baseEnd_223640 < baseStart_223640 := by decide
  rcases family_descends (prefixWord ++ tailWord_223640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223665 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_223665 : Nat := 118140960795 + 223665 * 2 ^ 59
def prefixEnd_223665 : Nat := 4983230072969 + 3 ^ 40 * 223665 * 2
def baseEnd_223665 : Nat := 51043400261321174826173

theorem tailTrace_223665 : CollatzResearch.WordTrace tailWord_223665 prefixEnd_223665 51043400261321174826173 := by
  unfold tailWord_223665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157732734707378785936449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5438488489804919190624299 8157732734707378785936449)
  ·
    refine ⟨6118299551030534089452337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8157732734707378785936449 6118299551030534089452337)
    ·
      refine ⟨4588724663272900567089253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6118299551030534089452337 4588724663272900567089253)
      ·
        refine ⟨860385874363668856329235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4588724663272900567089253 860385874363668856329235)
        ·
          refine ⟨1290578811545503284493853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860385874363668856329235 1290578811545503284493853)
          ·
            refine ⟨483967054329563731685195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1290578811545503284493853 483967054329563731685195)
            ·
              refine ⟨725950581494345597527793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483967054329563731685195 725950581494345597527793)
              ·
                refine ⟨544462936120759198145845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725950581494345597527793 544462936120759198145845)
                ·
                  refine ⟨51043400261321174826173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544462936120759198145845 51043400261321174826173)
                  ·
                    rfl

theorem cell21_223665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_223665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223665 prefixEnd_223665 := by exact prefixLift 223665
  have htrace : WordTrace (prefixWord ++ tailWord_223665) baseStart_223665 baseEnd_223665 := by
    simpa [prefixWord, tailWord_223665, baseEnd_223665] using wordTrace_append hprefix tailTrace_223665
  have hstable : (prefixWord ++ tailWord_223665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223665).length < 2 ^ (prefixWord ++ tailWord_223665).sum := by decide
  have hdescent : baseEnd_223665 < baseStart_223665 := by decide
  rcases family_descends (prefixWord ++ tailWord_223665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223724 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_223724 : Nat := 118140960795 + 223724 * 2 ^ 59
def prefixEnd_223724 : Nat := 4983230072969 + 3 ^ 40 * 223724 * 2
def baseEnd_223724 : Nat := 51056864865150183342719

theorem tailTrace_223724 : CollatzResearch.WordTrace tailWord_223724 prefixEnd_223724 51056864865150183342719 := by
  unfold tailWord_223724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079942320746815931167113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5439923094329087908222817 4079942320746815931167113)
  ·
    refine ⟨3059956740560111948375335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079942320746815931167113 3059956740560111948375335)
    ·
      refine ⟨4589935110840167922563003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059956740560111948375335 4589935110840167922563003)
      ·
        refine ⟨6884902666260251883844505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589935110840167922563003 6884902666260251883844505)
        ·
          refine ⟨5163676999695188912883379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884902666260251883844505 5163676999695188912883379)
          ·
            refine ⟨7745515499542783369325069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163676999695188912883379 7745515499542783369325069)
            ·
              refine ⟨2904568312328543763496901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7745515499542783369325069 2904568312328543763496901)
              ·
                refine ⟨544606558561601955655669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2904568312328543763496901 544606558561601955655669)
                ·
                  refine ⟨51056864865150183342719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544606558561601955655669 51056864865150183342719)
                  ·
                    rfl

theorem cell21_223724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_223724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223724 prefixEnd_223724 := by exact prefixLift 223724
  have htrace : WordTrace (prefixWord ++ tailWord_223724) baseStart_223724 baseEnd_223724 := by
    simpa [prefixWord, tailWord_223724, baseEnd_223724] using wordTrace_append hprefix tailTrace_223724
  have hstable : (prefixWord ++ tailWord_223724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223724).length < 2 ^ (prefixWord ++ tailWord_223724).sum := by decide
  have hdescent : baseEnd_223724 < baseStart_223724 := by decide
  rcases family_descends (prefixWord ++ tailWord_223724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223733 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 3]
def baseStart_223733 : Nat := 118140960795 + 223733 * 2 ^ 59
def prefixEnd_223733 : Nat := 4983230072969 + 3 ^ 40 * 223733 * 2
def baseEnd_223733 : Nat := 51058918787768167692701

theorem tailTrace_223733 : CollatzResearch.WordTrace tailWord_223733 prefixEnd_223733 51058918787768167692701 := by
  unfold tailWord_223733
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160212898461026399411853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5440141932307350932941235 8160212898461026399411853)
  ·
    refine ⟨3060079836922884899779445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8160212898461026399411853 3060079836922884899779445)
    ·
      refine ⟨286882484711520459354323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3060079836922884899779445 286882484711520459354323)
      ·
        refine ⟨430323727067280689031485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286882484711520459354323 430323727067280689031485)
        ·
          refine ⟨161371397650230258386807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430323727067280689031485 161371397650230258386807)
          ·
            refine ⟨242057096475345387580211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161371397650230258386807 242057096475345387580211)
            ·
              refine ⟨363085644713018081370317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242057096475345387580211 363085644713018081370317)
              ·
                refine ⟨136157116767381780513869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363085644713018081370317 136157116767381780513869)
                ·
                  refine ⟨51058918787768167692701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136157116767381780513869 51058918787768167692701)
                  ·
                    rfl

theorem cell21_223733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_223733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223733 prefixEnd_223733 := by exact prefixLift 223733
  have htrace : WordTrace (prefixWord ++ tailWord_223733) baseStart_223733 baseEnd_223733 := by
    simpa [prefixWord, tailWord_223733, baseEnd_223733] using wordTrace_append hprefix tailTrace_223733
  have hstable : (prefixWord ++ tailWord_223733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223733).length < 2 ^ (prefixWord ++ tailWord_223733).sum := by decide
  have hdescent : baseEnd_223733 < baseStart_223733 := by decide
  rcases family_descends (prefixWord ++ tailWord_223733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223750 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_223750 : Nat := 118140960795 + 223750 * 2 ^ 59
def prefixEnd_223750 : Nat := 4983230072969 + 3 ^ 40 * 223750 * 2
def baseEnd_223750 : Nat := 51062798419379915909333

theorem tailTrace_223750 : CollatzResearch.WordTrace tailWord_223750 prefixEnd_223750 51062798419379915909333 := by
  unfold tailWord_223750
  simp only [CollatzResearch.WordTrace]
  refine ⟨255026029356232446961897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5440555292932958868520469 255026029356232446961897)
  ·
    refine ⟨191269522017174335221423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255026029356232446961897 191269522017174335221423)
    ·
      refine ⟨286904283025761502832135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191269522017174335221423 286904283025761502832135)
      ·
        refine ⟨430356424538642254248203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286904283025761502832135 430356424538642254248203)
        ·
          refine ⟨645534636807963381372305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430356424538642254248203 645534636807963381372305)
          ·
            refine ⟨484150977605972536029229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645534636807963381372305 484150977605972536029229)
            ·
              refine ⟨181556616602239701010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484150977605972536029229 181556616602239701010961)
              ·
                refine ⟨136167462451679775758221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181556616602239701010961 136167462451679775758221)
                ·
                  refine ⟨51062798419379915909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136167462451679775758221 51062798419379915909333)
                  ·
                    rfl

theorem cell21_223750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_223750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223750 prefixEnd_223750 := by exact prefixLift 223750
  have htrace : WordTrace (prefixWord ++ tailWord_223750) baseStart_223750 baseEnd_223750 := by
    simpa [prefixWord, tailWord_223750, baseEnd_223750] using wordTrace_append hprefix tailTrace_223750
  have hstable : (prefixWord ++ tailWord_223750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223750).length < 2 ^ (prefixWord ++ tailWord_223750).sum := by decide
  have hdescent : baseEnd_223750 < baseStart_223750 := by decide
  rcases family_descends (prefixWord ++ tailWord_223750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223755 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_223755 : Nat := 118140960795 + 223755 * 2 ^ 59
def prefixEnd_223755 : Nat := 4983230072969 + 3 ^ 40 * 223755 * 2
def baseEnd_223755 : Nat := 51063939487501018325989

theorem tailTrace_223755 : CollatzResearch.WordTrace tailWord_223755 prefixEnd_223755 51063939487501018325989 := by
  unfold tailWord_223755
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161015304381324156712719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5440676869587549437808479 8161015304381324156712719)
  ·
    refine ⟨12241522956571986235069079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161015304381324156712719 12241522956571986235069079)
    ·
      refine ⟨18362284434857979352603619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12241522956571986235069079 18362284434857979352603619)
      ·
        refine ⟨27543426652286969028905429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18362284434857979352603619 27543426652286969028905429)
        ·
          refine ⟨645549062162975836614971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27543426652286969028905429 645549062162975836614971)
          ·
            refine ⟨968323593244463754922457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645549062162975836614971 968323593244463754922457)
            ·
              refine ⟨726242694933347816191843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968323593244463754922457 726242694933347816191843)
              ·
                refine ⟨1089364042400021724287765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726242694933347816191843 1089364042400021724287765)
                ·
                  refine ⟨51063939487501018325989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089364042400021724287765 51063939487501018325989)
                  ·
                    rfl

theorem cell21_223755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_223755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223755 prefixEnd_223755 := by exact prefixLift 223755
  have htrace : WordTrace (prefixWord ++ tailWord_223755) baseStart_223755 baseEnd_223755 := by
    simpa [prefixWord, tailWord_223755, baseEnd_223755] using wordTrace_append hprefix tailTrace_223755
  have hstable : (prefixWord ++ tailWord_223755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223755).length < 2 ^ (prefixWord ++ tailWord_223755).sum := by decide
  have hdescent : baseEnd_223755 < baseStart_223755 := by decide
  rcases family_descends (prefixWord ++ tailWord_223755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223758 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_223758 : Nat := 118140960795 + 223758 * 2 ^ 59
def prefixEnd_223758 : Nat := 4983230072969 + 3 ^ 40 * 223758 * 2
def baseEnd_223758 : Nat := 51064624128373679775983

theorem tailTrace_223758 : CollatzResearch.WordTrace tailWord_223758 prefixEnd_223758 51064624128373679775983 := by
  unfold tailWord_223758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020140590421306958633991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5440749815580303779381285 1020140590421306958633991)
  ·
    refine ⟨1530210885631960437950987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020140590421306958633991 1530210885631960437950987)
    ·
      refine ⟨2295316328447940656926481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530210885631960437950987 2295316328447940656926481)
      ·
        refine ⟨1721487246335955492694861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295316328447940656926481 1721487246335955492694861)
        ·
          refine ⟨645557717375983309760573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1721487246335955492694861 645557717375983309760573)
          ·
            refine ⟨242084144015993741160215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645557717375983309760573 242084144015993741160215)
            ·
              refine ⟨363126216023990611740323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242084144015993741160215 363126216023990611740323)
              ·
                refine ⟨544689324035985917610485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363126216023990611740323 544689324035985917610485)
                ·
                  refine ⟨51064624128373679775983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544689324035985917610485 51064624128373679775983)
                  ·
                    rfl

theorem cell21_223758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_223758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223758 prefixEnd_223758 := by exact prefixLift 223758
  have htrace : WordTrace (prefixWord ++ tailWord_223758) baseStart_223758 baseEnd_223758 := by
    simpa [prefixWord, tailWord_223758, baseEnd_223758] using wordTrace_append hprefix tailTrace_223758
  have hstable : (prefixWord ++ tailWord_223758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223758).length < 2 ^ (prefixWord ++ tailWord_223758).sum := by decide
  have hdescent : baseEnd_223758 < baseStart_223758 := by decide
  rcases family_descends (prefixWord ++ tailWord_223758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223772 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_223772 : Nat := 118140960795 + 223772 * 2 ^ 59
def prefixEnd_223772 : Nat := 4983230072969 + 3 ^ 40 * 223772 * 2
def baseEnd_223772 : Nat := 51067819119112766542621

theorem tailTrace_223772 : CollatzResearch.WordTrace tailWord_223772 prefixEnd_223772 51067819119112766542621 := by
  unfold tailWord_223772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080817672659868030040785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5441090230213157373387713 4080817672659868030040785)
  ·
    refine ⟨3060613254494901022530589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4080817672659868030040785 3060613254494901022530589)
    ·
      refine ⟨1147729970435587883448971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3060613254494901022530589 1147729970435587883448971)
      ·
        refine ⟨1721594955653381825173457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147729970435587883448971 1721594955653381825173457)
        ·
          refine ⟨1291196216740036368880093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721594955653381825173457 1291196216740036368880093)
          ·
            refine ⟨484198581277513638330035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291196216740036368880093 484198581277513638330035)
            ·
              refine ⟨726297871916270457495053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484198581277513638330035 726297871916270457495053)
              ·
                refine ⟨272361701968601421560645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726297871916270457495053 272361701968601421560645)
                ·
                  refine ⟨51067819119112766542621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272361701968601421560645 51067819119112766542621)
                  ·
                    rfl

theorem cell21_223772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_223772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223772 prefixEnd_223772 := by exact prefixLift 223772
  have htrace : WordTrace (prefixWord ++ tailWord_223772) baseStart_223772 baseEnd_223772 := by
    simpa [prefixWord, tailWord_223772, baseEnd_223772] using wordTrace_append hprefix tailTrace_223772
  have hstable : (prefixWord ++ tailWord_223772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223772).length < 2 ^ (prefixWord ++ tailWord_223772).sum := by decide
  have hdescent : baseEnd_223772 < baseStart_223772 := by decide
  rcases family_descends (prefixWord ++ tailWord_223772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223786 : List Nat := [3, 1, 4, 1, 1, 2, 2, 7]
def baseStart_223786 : Nat := 118140960795 + 223786 * 2 ^ 59
def prefixEnd_223786 : Nat := 4983230072969 + 3 ^ 40 * 223786 * 2
def baseEnd_223786 : Nat := 17023671369950617769753

theorem tailTrace_223786 : CollatzResearch.WordTrace tailWord_223786 prefixEnd_223786 17023671369950617769753 := by
  unfold tailWord_223786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040536491817254112772803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5441430644846010967394141 2040536491817254112772803)
  ·
    refine ⟨3060804737725881169159205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2040536491817254112772803 3060804737725881169159205)
    ·
      refine ⟨573900888323602719217351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3060804737725881169159205 573900888323602719217351)
      ·
        refine ⟨860851332485404078826027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573900888323602719217351 860851332485404078826027)
        ·
          refine ⟨1291276998728106118239041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860851332485404078826027 1291276998728106118239041)
          ·
            refine ⟨968457749046079588679281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291276998728106118239041 968457749046079588679281)
            ·
              refine ⟨726343311784559691509461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968457749046079588679281 726343311784559691509461)
              ·
                refine ⟨17023671369950617769753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 726343311784559691509461 17023671369950617769753)
                ·
                  rfl

theorem cell21_223786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_223786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223786 prefixEnd_223786 := by exact prefixLift 223786
  have htrace : WordTrace (prefixWord ++ tailWord_223786) baseStart_223786 baseEnd_223786 := by
    simpa [prefixWord, tailWord_223786, baseEnd_223786] using wordTrace_append hprefix tailTrace_223786
  have hstable : (prefixWord ++ tailWord_223786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223786).length < 2 ^ (prefixWord ++ tailWord_223786).sum := by decide
  have hdescent : baseEnd_223786 < baseStart_223786 := by decide
  rcases family_descends (prefixWord ++ tailWord_223786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223806 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_223806 : Nat := 118140960795 + 223806 * 2 ^ 59
def prefixEnd_223806 : Nat := 4983230072969 + 3 ^ 40 * 223806 * 2
def baseEnd_223806 : Nat := 51075578382336262975885

theorem tailTrace_223806 : CollatzResearch.WordTrace tailWord_223806 prefixEnd_223806 51075578382336262975885 := by
  unfold tailWord_223806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020359428399569983352409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5441916951464373244546181 1020359428399569983352409)
  ·
    refine ⟨765269571299677487514307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1020359428399569983352409 765269571299677487514307)
    ·
      refine ⟨1147904356949516231271461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765269571299677487514307 1147904356949516231271461)
      ·
        refine ⟨215232066928034293363399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1147904356949516231271461 215232066928034293363399)
        ·
          refine ⟨322848100392051440045099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215232066928034293363399 322848100392051440045099)
          ·
            refine ⟨484272150588077160067649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322848100392051440045099 484272150588077160067649)
            ·
              refine ⟨363204112941057870050737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484272150588077160067649 363204112941057870050737)
              ·
                refine ⟨272403084705793402538053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363204112941057870050737 272403084705793402538053)
                ·
                  refine ⟨51075578382336262975885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272403084705793402538053 51075578382336262975885)
                  ·
                    rfl

theorem cell21_223806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_223806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223806 prefixEnd_223806 := by exact prefixLift 223806
  have htrace : WordTrace (prefixWord ++ tailWord_223806) baseStart_223806 baseEnd_223806 := by
    simpa [prefixWord, tailWord_223806, baseEnd_223806] using wordTrace_append hprefix tailTrace_223806
  have hstable : (prefixWord ++ tailWord_223806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223806).length < 2 ^ (prefixWord ++ tailWord_223806).sum := by decide
  have hdescent : baseEnd_223806 < baseStart_223806 := by decide
  rcases family_descends (prefixWord ++ tailWord_223806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223831 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_223831 : Nat := 118140960795 + 223831 * 2 ^ 59
def prefixEnd_223831 : Nat := 4983230072969 + 3 ^ 40 * 223831 * 2
def baseEnd_223831 : Nat := 51081283722941775059167

theorem tailTrace_223831 : CollatzResearch.WordTrace tailWord_223831 prefixEnd_223831 51081283722941775059167 := by
  unfold tailWord_223831
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163787252105989136479347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442524834737326090986231 8163787252105989136479347)
  ·
    refine ⟨12245680878158983704719021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163787252105989136479347 12245680878158983704719021)
    ·
      refine ⟨4592130329309618889269633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12245680878158983704719021 4592130329309618889269633)
      ·
        refine ⟨3444097746982214166952225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4592130329309618889269633 3444097746982214166952225)
        ·
          refine ⟨2583073310236660625214169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444097746982214166952225 2583073310236660625214169)
          ·
            refine ⟨1937304982677495468910627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583073310236660625214169 1937304982677495468910627)
            ·
              refine ⟨2905957474016243203365941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937304982677495468910627 2905957474016243203365941)
              ·
                refine ⟨272433513189022800315557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2905957474016243203365941 272433513189022800315557)
                ·
                  refine ⟨51081283722941775059167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272433513189022800315557 51081283722941775059167)
                  ·
                    rfl

theorem cell21_223831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_223831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223831 prefixEnd_223831 := by exact prefixLift 223831
  have htrace : WordTrace (prefixWord ++ tailWord_223831) baseStart_223831 baseEnd_223831 := by
    simpa [prefixWord, tailWord_223831, baseEnd_223831] using wordTrace_append hprefix tailTrace_223831
  have hstable : (prefixWord ++ tailWord_223831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223831).length < 2 ^ (prefixWord ++ tailWord_223831).sum := by decide
  have hdescent : baseEnd_223831 < baseStart_223831 := by decide
  rcases family_descends (prefixWord ++ tailWord_223831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223927 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 3]
def baseStart_223927 : Nat := 118140960795 + 223927 * 2 ^ 59
def prefixEnd_223927 : Nat := 4983230072969 + 3 ^ 40 * 223927 * 2
def baseEnd_223927 : Nat := 51103192230866941458971

theorem tailTrace_223927 : CollatzResearch.WordTrace tailWord_223927 prefixEnd_223927 51103192230866941458971 := by
  unfold tailWord_223927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167288659758197531974035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5444859106505465021316023 8167288659758197531974035)
  ·
    refine ⟨12250932989637296297961053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167288659758197531974035 12250932989637296297961053)
    ·
      refine ⟨4594099871113986111735395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12250932989637296297961053 4594099871113986111735395)
      ·
        refine ⟨6891149806670979167603093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594099871113986111735395 6891149806670979167603093)
        ·
          refine ⟨323022647187702148481395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6891149806670979167603093 323022647187702148481395)
          ·
            refine ⟨484533970781553222722093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323022647187702148481395 484533970781553222722093)
            ·
              refine ⟨181700239043082458520785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484533970781553222722093 181700239043082458520785)
              ·
                refine ⟨136275179282311843890589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181700239043082458520785 136275179282311843890589)
                ·
                  refine ⟨51103192230866941458971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136275179282311843890589 51103192230866941458971)
                  ·
                    rfl

theorem cell21_223927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].length) (baseStart_223927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223927 prefixEnd_223927 := by exact prefixLift 223927
  have htrace : WordTrace (prefixWord ++ tailWord_223927) baseStart_223927 baseEnd_223927 := by
    simpa [prefixWord, tailWord_223927, baseEnd_223927] using wordTrace_append hprefix tailTrace_223927
  have hstable : (prefixWord ++ tailWord_223927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223927).length < 2 ^ (prefixWord ++ tailWord_223927).sum := by decide
  have hdescent : baseEnd_223927 < baseStart_223927 := by decide
  rcases family_descends (prefixWord ++ tailWord_223927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223983 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_223983 : Nat := 118140960795 + 223983 * 2 ^ 59
def prefixEnd_223983 : Nat := 4983230072969 + 3 ^ 40 * 223983 * 2
def baseEnd_223983 : Nat := 51115972193823288525523

theorem tailTrace_223983 : CollatzResearch.WordTrace tailWord_223983 prefixEnd_223983 51115972193823288525523 := by
  unfold tailWord_223983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169331147555319096012603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446220765036879397341735 8169331147555319096012603)
  ·
    refine ⟨12253996721332978644018905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8169331147555319096012603 12253996721332978644018905)
    ·
      refine ⟨9190497540999733983014179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12253996721332978644018905 9190497540999733983014179)
      ·
        refine ⟨13785746311499600974521269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190497540999733983014179 13785746311499600974521269)
        ·
          refine ⟨1292413716703087591361369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13785746311499600974521269 1292413716703087591361369)
          ·
            refine ⟨969310287527315693521027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292413716703087591361369 969310287527315693521027)
            ·
              refine ⟨1453965431290973540281541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969310287527315693521027 1453965431290973540281541)
              ·
                refine ⟨272618518367057538802789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1453965431290973540281541 272618518367057538802789)
                ·
                  refine ⟨51115972193823288525523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272618518367057538802789 51115972193823288525523)
                  ·
                    rfl

theorem cell21_223983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_223983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223983 prefixEnd_223983 := by exact prefixLift 223983
  have htrace : WordTrace (prefixWord ++ tailWord_223983) baseStart_223983 baseEnd_223983 := by
    simpa [prefixWord, tailWord_223983, baseEnd_223983] using wordTrace_append hprefix tailTrace_223983
  have hstable : (prefixWord ++ tailWord_223983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223983).length < 2 ^ (prefixWord ++ tailWord_223983).sum := by decide
  have hdescent : baseEnd_223983 < baseStart_223983 := by decide
  rcases family_descends (prefixWord ++ tailWord_223983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223986 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_223986 : Nat := 118140960795 + 223986 * 2 ^ 59
def prefixEnd_223986 : Nat := 4983230072969 + 3 ^ 40 * 223986 * 2
def baseEnd_223986 : Nat := 51116656834695949975517

theorem tailTrace_223986 : CollatzResearch.WordTrace tailWord_223986 prefixEnd_223986 51116656834695949975517 := by
  unfold tailWord_223986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042360141636112652092953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5446293711029633738914541 2042360141636112652092953)
  ·
    refine ⟨1531770106227084489069715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2042360141636112652092953 1531770106227084489069715)
    ·
      refine ⟨2297655159340626733604573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531770106227084489069715 2297655159340626733604573)
      ·
        refine ⟨861620684752735025101715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2297655159340626733604573 861620684752735025101715)
        ·
          refine ⟨1292431027129102537652573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861620684752735025101715 1292431027129102537652573)
          ·
            refine ⟨484661635173413451619715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292431027129102537652573 484661635173413451619715)
            ·
              refine ⟨726992452760120177429573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484661635173413451619715 726992452760120177429573)
              ·
                refine ⟨136311084892522533268045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726992452760120177429573 136311084892522533268045)
                ·
                  refine ⟨51116656834695949975517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136311084892522533268045 51116656834695949975517)
                  ·
                    rfl

theorem cell21_223986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_223986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223986 prefixEnd_223986 := by exact prefixLift 223986
  have htrace : WordTrace (prefixWord ++ tailWord_223986) baseStart_223986 baseEnd_223986 := by
    simpa [prefixWord, tailWord_223986, baseEnd_223986] using wordTrace_append hprefix tailTrace_223986
  have hstable : (prefixWord ++ tailWord_223986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223986).length < 2 ^ (prefixWord ++ tailWord_223986).sum := by decide
  have hdescent : baseEnd_223986 < baseStart_223986 := by decide
  rcases family_descends (prefixWord ++ tailWord_223986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223989 : List Nat := [1, 3, 6, 1, 1, 2, 1, 6]
def baseStart_223989 : Nat := 118140960795 + 223989 * 2 ^ 59
def prefixEnd_223989 : Nat := 4983230072969 + 3 ^ 40 * 223989 * 2
def baseEnd_223989 : Nat := 17039113825189537141837

theorem tailTrace_223989 : CollatzResearch.WordTrace tailWord_223989 prefixEnd_223989 17039113825189537141837 := by
  unfold tailWord_223989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169549985533582120731021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446366657022388080487347 8169549985533582120731021)
  ·
    refine ⟨3063581244575093295274133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8169549985533582120731021 3063581244575093295274133)
    ·
      refine ⟨143605370839457498215975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3063581244575093295274133 143605370839457498215975)
      ·
        refine ⟨215408056259186247323963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143605370839457498215975 215408056259186247323963)
        ·
          refine ⟨323112084388779370985945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215408056259186247323963 323112084388779370985945)
          ·
            refine ⟨242334063291584528239459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323112084388779370985945 242334063291584528239459)
            ·
              refine ⟨363501094937376792359189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242334063291584528239459 363501094937376792359189)
              ·
                refine ⟨17039113825189537141837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363501094937376792359189 17039113825189537141837)
                ·
                  rfl

theorem cell21_223989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].length) (baseStart_223989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_223989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_223989 prefixEnd_223989 := by exact prefixLift 223989
  have htrace : WordTrace (prefixWord ++ tailWord_223989) baseStart_223989 baseEnd_223989 := by
    simpa [prefixWord, tailWord_223989, baseEnd_223989] using wordTrace_append hprefix tailTrace_223989
  have hstable : (prefixWord ++ tailWord_223989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223989).length < 2 ^ (prefixWord ++ tailWord_223989).sum := by decide
  have hdescent : baseEnd_223989 < baseStart_223989 := by decide
  rcases family_descends (prefixWord ++ tailWord_223989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224065 : List Nat := [1, 2, 5, 3, 2, 1, 2, 5]
def baseStart_224065 : Nat := 118140960795 + 224065 * 2 ^ 59
def prefixEnd_224065 : Nat := 4983230072969 + 3 ^ 40 * 224065 * 2
def baseEnd_224065 : Nat := 17044895237003122719563

theorem tailTrace_224065 : CollatzResearch.WordTrace tailWord_224065 prefixEnd_224065 17044895237003122719563 := by
  unfold tailWord_224065
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172321933258247100497649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5448214622172164733665099 8172321933258247100497649)
  ·
    refine ⟨6129241449943685325373237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8172321933258247100497649 6129241449943685325373237)
    ·
      refine ⟨574616385932220499253741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6129241449943685325373237 574616385932220499253741)
      ·
        refine ⟨215481144724582687220153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574616385932220499253741 215481144724582687220153)
        ·
          refine ⟨161610858543437015415115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215481144724582687220153 161610858543437015415115)
          ·
            refine ⟨242416287815155523122673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161610858543437015415115 242416287815155523122673)
            ·
              refine ⟨181812215861366642342005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242416287815155523122673 181812215861366642342005)
              ·
                refine ⟨17044895237003122719563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181812215861366642342005 17044895237003122719563)
                ·
                  rfl

theorem cell21_224065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].length) (baseStart_224065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224065 prefixEnd_224065 := by exact prefixLift 224065
  have htrace : WordTrace (prefixWord ++ tailWord_224065) baseStart_224065 baseEnd_224065 := by
    simpa [prefixWord, tailWord_224065, baseEnd_224065] using wordTrace_append hprefix tailTrace_224065
  have hstable : (prefixWord ++ tailWord_224065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224065).length < 2 ^ (prefixWord ++ tailWord_224065).sum := by decide
  have hdescent : baseEnd_224065 < baseStart_224065 := by decide
  rcases family_descends (prefixWord ++ tailWord_224065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224073 : List Nat := [1, 2, 1, 1, 2, 6, 1, 7]
def baseStart_224073 : Nat := 118140960795 + 224073 * 2 ^ 59
def prefixEnd_224073 : Nat := 4983230072969 + 3 ^ 40 * 224073 * 2
def baseEnd_224073 : Nat := 17045503806667710675113

theorem tailTrace_224073 : CollatzResearch.WordTrace tailWord_224073 prefixEnd_224073 17045503806667710675113 := by
  unfold tailWord_224073
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172613717229264466788873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5448409144819509644525915 8172613717229264466788873)
  ·
    refine ⟨6129460287921948350091655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8172613717229264466788873 6129460287921948350091655)
    ·
      refine ⟨9194190431882922525137483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129460287921948350091655 9194190431882922525137483)
      ·
        refine ⟨13791285647824383787706225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9194190431882922525137483 13791285647824383787706225)
        ·
          refine ⟨10343464235868287840779669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13791285647824383787706225 10343464235868287840779669)
          ·
            refine ⟨484849886056325992536547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10343464235868287840779669 484849886056325992536547)
            ·
              refine ⟨727274829084488988804821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484849886056325992536547 727274829084488988804821)
              ·
                refine ⟨17045503806667710675113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 727274829084488988804821 17045503806667710675113)
                ·
                  rfl

theorem cell21_224073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_224073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224073 prefixEnd_224073 := by exact prefixLift 224073
  have htrace : WordTrace (prefixWord ++ tailWord_224073) baseStart_224073 baseEnd_224073 := by
    simpa [prefixWord, tailWord_224073, baseEnd_224073] using wordTrace_append hprefix tailTrace_224073
  have hstable : (prefixWord ++ tailWord_224073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224073).length < 2 ^ (prefixWord ++ tailWord_224073).sum := by decide
  have hdescent : baseEnd_224073 < baseStart_224073 := by decide
  rcases family_descends (prefixWord ++ tailWord_224073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224110 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_224110 : Nat := 118140960795 + 224110 * 2 ^ 59
def prefixEnd_224110 : Nat := 4983230072969 + 3 ^ 40 * 224110 * 2
def baseEnd_224110 : Nat := 51144955324099289908597

theorem tailTrace_224110 : CollatzResearch.WordTrace tailWord_224110 prefixEnd_224110 51144955324099289908597 := by
  unfold tailWord_224110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021745402261902473235723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5449308812063479857257189 1021745402261902473235723)
  ·
    refine ⟨1532618103392853709853585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1021745402261902473235723 1532618103392853709853585)
    ·
      refine ⟨1149463577544640282390189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1532618103392853709853585 1149463577544640282390189)
      ·
        refine ⟨431048841579240105896321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1149463577544640282390189 431048841579240105896321)
        ·
          refine ⟨323286631184430079422241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431048841579240105896321 323286631184430079422241)
          ·
            refine ⟨242464973388322559566681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323286631184430079422241 242464973388322559566681)
            ·
              refine ⟨181848730041241919675011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242464973388322559566681 181848730041241919675011)
              ·
                refine ⟨272773095061862879512517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181848730041241919675011 272773095061862879512517)
                ·
                  refine ⟨51144955324099289908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272773095061862879512517 51144955324099289908597)
                  ·
                    rfl

theorem cell21_224110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_224110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224110 prefixEnd_224110 := by exact prefixLift 224110
  have htrace : WordTrace (prefixWord ++ tailWord_224110) baseStart_224110 baseEnd_224110 := by
    simpa [prefixWord, tailWord_224110, baseEnd_224110] using wordTrace_append hprefix tailTrace_224110
  have hstable : (prefixWord ++ tailWord_224110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224110).length < 2 ^ (prefixWord ++ tailWord_224110).sum := by decide
  have hdescent : baseEnd_224110 < baseStart_224110 := by decide
  rcases family_descends (prefixWord ++ tailWord_224110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224214 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_224214 : Nat := 118140960795 + 224214 * 2 ^ 59
def prefixEnd_224214 : Nat := 4983230072969 + 3 ^ 40 * 224214 * 2
def baseEnd_224214 : Nat := 51168689541018220175051

theorem tailTrace_224214 : CollatzResearch.WordTrace tailWord_224214 prefixEnd_224214 51168689541018220175051 := by
  unfold tailWord_224214
  simp only [CollatzResearch.WordTrace]
  refine ⟨511109775607402846729481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5451837606478963698447797 511109775607402846729481)
  ·
    refine ⟨383332331705552135047111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 511109775607402846729481 383332331705552135047111)
    ·
      refine ⟨574998497558328202570667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383332331705552135047111 574998497558328202570667)
      ·
        refine ⟨862497746337492303856001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574998497558328202570667 862497746337492303856001)
        ·
          refine ⟨646873309753119227892001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862497746337492303856001 646873309753119227892001)
          ·
            refine ⟨485154982314839420919001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646873309753119227892001 485154982314839420919001)
            ·
              refine ⟨363866236736129565689251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485154982314839420919001 363866236736129565689251)
              ·
                refine ⟨545799355104194348533877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363866236736129565689251 545799355104194348533877)
                ·
                  refine ⟨51168689541018220175051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 545799355104194348533877 51168689541018220175051)
                  ·
                    rfl

theorem cell21_224214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_224214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224214 prefixEnd_224214 := by exact prefixLift 224214
  have htrace : WordTrace (prefixWord ++ tailWord_224214) baseStart_224214 baseEnd_224214 := by
    simpa [prefixWord, tailWord_224214, baseEnd_224214] using wordTrace_append hprefix tailTrace_224214
  have hstable : (prefixWord ++ tailWord_224214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224214).length < 2 ^ (prefixWord ++ tailWord_224214).sum := by decide
  have hdescent : baseEnd_224214 < baseStart_224214 := by decide
  rcases family_descends (prefixWord ++ tailWord_224214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224287 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_224287 : Nat := 118140960795 + 224287 * 2 ^ 59
def prefixEnd_224287 : Nat := 4983230072969 + 3 ^ 40 * 224287 * 2
def baseEnd_224287 : Nat := 51185349135586315458235

theorem tailTrace_224287 : CollatzResearch.WordTrace tailWord_224287 prefixEnd_224287 51185349135586315458235 := by
  unfold tailWord_224287
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180418938453979015079115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5453612625635986010052743 8180418938453979015079115)
  ·
    refine ⟨12270628407680968522618673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8180418938453979015079115 12270628407680968522618673)
    ·
      refine ⟨9202971305760726391964005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12270628407680968522618673 9202971305760726391964005)
      ·
        refine ⟨1725557119830136198493251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9202971305760726391964005 1725557119830136198493251)
        ·
          refine ⟨2588335679745204297739877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725557119830136198493251 2588335679745204297739877)
          ·
            refine ⟨485312939952225805826227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2588335679745204297739877 485312939952225805826227)
            ·
              refine ⟨727969409928338708739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485312939952225805826227 727969409928338708739341)
              ·
                refine ⟨272988528723127015777253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727969409928338708739341 272988528723127015777253)
                ·
                  refine ⟨51185349135586315458235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272988528723127015777253 51185349135586315458235)
                  ·
                    rfl

theorem cell21_224287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_224287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224287 prefixEnd_224287 := by exact prefixLift 224287
  have htrace : WordTrace (prefixWord ++ tailWord_224287) baseStart_224287 baseEnd_224287 := by
    simpa [prefixWord, tailWord_224287, baseEnd_224287] using wordTrace_append hprefix tailTrace_224287
  have hstable : (prefixWord ++ tailWord_224287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224287).length < 2 ^ (prefixWord ++ tailWord_224287).sum := by decide
  have hdescent : baseEnd_224287 < baseStart_224287 := by decide
  rcases family_descends (prefixWord ++ tailWord_224287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224366 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_224366 : Nat := 118140960795 + 224366 * 2 ^ 59
def prefixEnd_224366 : Nat := 4983230072969 + 3 ^ 40 * 224366 * 2
def baseEnd_224366 : Nat := 51203378011899733641407

theorem tailTrace_224366 : CollatzResearch.WordTrace tailWord_224366 prefixEnd_224366 51203378011899733641407 := by
  unfold tailWord_224366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022912538145971938400619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5455533536778517004803301 1022912538145971938400619)
  ·
    refine ⟨1534368807218957907600929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022912538145971938400619 1534368807218957907600929)
    ·
      refine ⟨1150776605414218430700697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534368807218957907600929 1150776605414218430700697)
      ·
        refine ⟨863082454060663823025523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1150776605414218430700697 863082454060663823025523)
        ·
          refine ⟨1294623681090995734538285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863082454060663823025523 1294623681090995734538285)
          ·
            refine ⟨485483880409123400451857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294623681090995734538285 485483880409123400451857)
            ·
              refine ⟨364112910306842550338893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485483880409123400451857 364112910306842550338893)
              ·
                refine ⟨136542341365065956377085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364112910306842550338893 136542341365065956377085)
                ·
                  refine ⟨51203378011899733641407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136542341365065956377085 51203378011899733641407)
                  ·
                    rfl

theorem cell21_224366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_224366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224366 prefixEnd_224366 := by exact prefixLift 224366
  have htrace : WordTrace (prefixWord ++ tailWord_224366) baseStart_224366 baseEnd_224366 := by
    simpa [prefixWord, tailWord_224366, baseEnd_224366] using wordTrace_append hprefix tailTrace_224366
  have hstable : (prefixWord ++ tailWord_224366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224366).length < 2 ^ (prefixWord ++ tailWord_224366).sum := by decide
  have hdescent : baseEnd_224366 < baseStart_224366 := by decide
  rcases family_descends (prefixWord ++ tailWord_224366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224377 : List Nat := [1, 2, 1, 3, 5, 1, 8]
def baseStart_224377 : Nat := 118140960795 + 224377 * 2 ^ 59
def prefixEnd_224377 : Nat := 4983230072969 + 3 ^ 40 * 224377 * 2
def baseEnd_224377 : Nat := 5689543151307350995339

theorem tailTrace_224377 : CollatzResearch.WordTrace tailWord_224377 prefixEnd_224377 5689543151307350995339 := by
  unfold tailWord_224377
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183701508127924385855385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5455801005418616257236923 8183701508127924385855385)
  ·
    refine ⟨6137776131095943289391539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8183701508127924385855385 6137776131095943289391539)
    ·
      refine ⟨9206664196643914934087309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137776131095943289391539 9206664196643914934087309)
      ·
        refine ⟨3452499073741468100282741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9206664196643914934087309 3452499073741468100282741)
        ·
          refine ⟨323671788163262634401507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3452499073741468100282741 323671788163262634401507)
          ·
            refine ⟨485507682244893951602261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323671788163262634401507 485507682244893951602261)
            ·
              refine ⟨5689543151307350995339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 485507682244893951602261 5689543151307350995339)
              ·
                rfl

theorem cell21_224377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 8].length) (baseStart_224377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224377 prefixEnd_224377 := by exact prefixLift 224377
  have htrace : WordTrace (prefixWord ++ tailWord_224377) baseStart_224377 baseEnd_224377 := by
    simpa [prefixWord, tailWord_224377, baseEnd_224377] using wordTrace_append hprefix tailTrace_224377
  have hstable : (prefixWord ++ tailWord_224377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224377).length < 2 ^ (prefixWord ++ tailWord_224377).sum := by decide
  have hdescent : baseEnd_224377 < baseStart_224377 := by decide
  rcases family_descends (prefixWord ++ tailWord_224377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224408 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_224408 : Nat := 118140960795 + 224408 * 2 ^ 59
def prefixEnd_224408 : Nat := 4983230072969 + 3 ^ 40 * 224408 * 2
def baseEnd_224408 : Nat := 51212962984116993941321

theorem tailTrace_224408 : CollatzResearch.WordTrace tailWord_224408 prefixEnd_224408 51212962984116993941321 := by
  unfold tailWord_224408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092416085507808340116939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5456554780677077786822585 4092416085507808340116939)
  ·
    refine ⟨6138624128261712510175409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092416085507808340116939 6138624128261712510175409)
    ·
      refine ⟨4603968096196284382631557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6138624128261712510175409 4603968096196284382631557)
      ·
        refine ⟨863244018036803321743417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4603968096196284382631557 863244018036803321743417)
        ·
          refine ⟨647433013527602491307563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863244018036803321743417 647433013527602491307563)
          ·
            refine ⟨971149520291403736961345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647433013527602491307563 971149520291403736961345)
            ·
              refine ⟨728362140218552802721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971149520291403736961345 728362140218552802721009)
              ·
                refine ⟨546271605163914602040757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728362140218552802721009 546271605163914602040757)
                ·
                  refine ⟨51212962984116993941321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546271605163914602040757 51212962984116993941321)
                  ·
                    rfl

theorem cell21_224408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_224408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224408 prefixEnd_224408 := by exact prefixLift 224408
  have htrace : WordTrace (prefixWord ++ tailWord_224408) baseStart_224408 baseEnd_224408 := by
    simpa [prefixWord, tailWord_224408, baseEnd_224408] using wordTrace_append hprefix tailTrace_224408
  have hstable : (prefixWord ++ tailWord_224408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224408).length < 2 ^ (prefixWord ++ tailWord_224408).sum := by decide
  have hdescent : baseEnd_224408 < baseStart_224408 := by decide
  rcases family_descends (prefixWord ++ tailWord_224408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224529 : List Nat := [1, 2, 2, 1, 1, 4, 5, 5]
def baseStart_224529 : Nat := 118140960795 + 224529 * 2 ^ 59
def prefixEnd_224529 : Nat := 4983230072969 + 3 ^ 40 * 224529 * 2
def baseEnd_224529 : Nat := 17080192277549224141469

theorem tailTrace_224529 : CollatzResearch.WordTrace tailWord_224529 prefixEnd_224529 17080192277549224141469 := by
  unfold tailWord_224529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189245403577254345388641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459496935718169563592427 8189245403577254345388641)
  ·
    refine ⟨6141934052682940759041481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8189245403577254345388641 6141934052682940759041481)
    ·
      refine ⟨4606450539512205569281111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6141934052682940759041481 4606450539512205569281111)
      ·
        refine ⟨6909675809268308353921667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606450539512205569281111 6909675809268308353921667)
        ·
          refine ⟨10364513713902462530882501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909675809268308353921667 10364513713902462530882501)
          ·
            refine ⟨1943346321356711724540469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10364513713902462530882501 1943346321356711724540469)
            ·
              refine ⟨182188717627191724175669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1943346321356711724540469 182188717627191724175669)
              ·
                refine ⟨17080192277549224141469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182188717627191724175669 17080192277549224141469)
                ·
                  rfl

theorem cell21_224529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].length) (baseStart_224529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224529 prefixEnd_224529 := by exact prefixLift 224529
  have htrace : WordTrace (prefixWord ++ tailWord_224529) baseStart_224529 baseEnd_224529 := by
    simpa [prefixWord, tailWord_224529, baseEnd_224529] using wordTrace_append hprefix tailTrace_224529
  have hstable : (prefixWord ++ tailWord_224529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224529).length < 2 ^ (prefixWord ++ tailWord_224529).sum := by decide
  have hdescent : baseEnd_224529 < baseStart_224529 := by decide
  rcases family_descends (prefixWord ++ tailWord_224529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224560 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_224560 : Nat := 118140960795 + 224560 * 2 ^ 59
def prefixEnd_224560 : Nat := 4983230072969 + 3 ^ 40 * 224560 * 2
def baseEnd_224560 : Nat := 51247651454998507407677

theorem tailTrace_224560 : CollatzResearch.WordTrace tailWord_224560 prefixEnd_224560 51247651454998507407677 := by
  unfold tailWord_224560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4095188033232473319883567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5460250710976631093178089 4095188033232473319883567)
  ·
    refine ⟨6142782049848709979825351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4095188033232473319883567 6142782049848709979825351)
    ·
      refine ⟨9214173074773064969738027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142782049848709979825351 9214173074773064969738027)
      ·
        refine ⟨13821259612159597454607041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214173074773064969738027 13821259612159597454607041)
        ·
          refine ⟨10365944709119698090955281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13821259612159597454607041 10365944709119698090955281)
          ·
            refine ⟨7774458531839773568216461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365944709119698090955281 7774458531839773568216461)
            ·
              refine ⟨2915421949439915088081173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7774458531839773568216461 2915421949439915088081173)
              ·
                refine ⟨136660403879996019753805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2915421949439915088081173 136660403879996019753805)
                ·
                  refine ⟨51247651454998507407677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136660403879996019753805 51247651454998507407677)
                  ·
                    rfl

theorem cell21_224560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_224560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224560 prefixEnd_224560 := by exact prefixLift 224560
  have htrace : WordTrace (prefixWord ++ tailWord_224560) baseStart_224560 baseEnd_224560 := by
    simpa [prefixWord, tailWord_224560, baseEnd_224560] using wordTrace_append hprefix tailTrace_224560
  have hstable : (prefixWord ++ tailWord_224560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224560).length < 2 ^ (prefixWord ++ tailWord_224560).sum := by decide
  have hdescent : baseEnd_224560 < baseStart_224560 := by decide
  rcases family_descends (prefixWord ++ tailWord_224560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224566 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_224566 : Nat := 118140960795 + 224566 * 2 ^ 59
def prefixEnd_224566 : Nat := 4983230072969 + 3 ^ 40 * 224566 * 2
def baseEnd_224566 : Nat := 51249020736743830307665

theorem tailTrace_224566 : CollatzResearch.WordTrace tailWord_224566 prefixEnd_224566 51249020736743830307665 := by
  unfold tailWord_224566
  simp only [CollatzResearch.WordTrace]
  refine ⟨511912181527700604030347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5460396602962139776323701 511912181527700604030347)
  ·
    refine ⟨767868272291550906045521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511912181527700604030347 767868272291550906045521)
    ·
      refine ⟨575901204218663179534141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 767868272291550906045521 575901204218663179534141)
      ·
        refine ⟨215962951581998692325303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575901204218663179534141 215962951581998692325303)
        ·
          refine ⟨323944427372998038487955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215962951581998692325303 323944427372998038487955)
          ·
            refine ⟨485916641059497057731933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323944427372998038487955 485916641059497057731933)
            ·
              refine ⟨182218740397311396649475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485916641059497057731933 182218740397311396649475)
              ·
                refine ⟨273328110595967094974213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182218740397311396649475 273328110595967094974213)
                ·
                  refine ⟨51249020736743830307665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273328110595967094974213 51249020736743830307665)
                  ·
                    rfl

theorem cell21_224566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_224566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224566 prefixEnd_224566 := by exact prefixLift 224566
  have htrace : WordTrace (prefixWord ++ tailWord_224566) baseStart_224566 baseEnd_224566 := by
    simpa [prefixWord, tailWord_224566, baseEnd_224566] using wordTrace_append hprefix tailTrace_224566
  have hstable : (prefixWord ++ tailWord_224566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224566).length < 2 ^ (prefixWord ++ tailWord_224566).sum := by decide
  have hdescent : baseEnd_224566 < baseStart_224566 := by decide
  rcases family_descends (prefixWord ++ tailWord_224566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224664 : List Nat := [2, 1, 2, 5, 11]
def baseStart_224664 : Nat := 118140960795 + 224664 * 2 ^ 59
def prefixEnd_224664 : Nat := 4983230072969 + 3 ^ 40 * 224664 * 2
def baseEnd_224664 : Nat := 632980070023672070051

theorem tailTrace_224664 : CollatzResearch.WordTrace tailWord_224664 prefixEnd_224664 632980070023672070051 := by
  unfold tailWord_224664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097084629044086200776523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5462779505392114934368697 4097084629044086200776523)
  ·
    refine ⟨6145626943566129301164785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097084629044086200776523 6145626943566129301164785)
    ·
      refine ⟨4609220207674596975873589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6145626943566129301164785 4609220207674596975873589)
      ·
        refine ⟨432114394469493466488149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4609220207674596975873589 432114394469493466488149)
        ·
          refine ⟨632980070023672070051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 432114394469493466488149 632980070023672070051)
          ·
            rfl

theorem cell21_224664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 11].length) (baseStart_224664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224664 prefixEnd_224664 := by exact prefixLift 224664
  have htrace : WordTrace (prefixWord ++ tailWord_224664) baseStart_224664 baseEnd_224664 := by
    simpa [prefixWord, tailWord_224664, baseEnd_224664] using wordTrace_append hprefix tailTrace_224664
  have hstable : (prefixWord ++ tailWord_224664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224664).length < 2 ^ (prefixWord ++ tailWord_224664).sum := by decide
  have hdescent : baseEnd_224664 < baseStart_224664 := by decide
  rcases family_descends (prefixWord ++ tailWord_224664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224695 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_224695 : Nat := 118140960795 + 224695 * 2 ^ 59
def prefixEnd_224695 : Nat := 4983230072969 + 3 ^ 40 * 224695 * 2
def baseEnd_224695 : Nat := 51278460294268272657401

theorem tailTrace_224695 : CollatzResearch.WordTrace tailWord_224695 prefixEnd_224695 51278460294268272657401 := by
  unfold tailWord_224695
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195299920975864695931539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5463533280650576463954359 8195299920975864695931539)
  ·
    refine ⟨12292949881463797043897309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195299920975864695931539 12292949881463797043897309)
    ·
      refine ⟨4609856205548923891461491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12292949881463797043897309 4609856205548923891461491)
      ·
        refine ⟨6914784308323385837192237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609856205548923891461491 6914784308323385837192237)
        ·
          refine ⟨2593044115621269688947089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6914784308323385837192237 2593044115621269688947089)
          ·
            refine ⟨1944783086715952266710317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593044115621269688947089 1944783086715952266710317)
            ·
              refine ⟨729293657518482100016369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1944783086715952266710317 729293657518482100016369)
              ·
                refine ⟨546970243138861575012277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729293657518482100016369 546970243138861575012277)
                ·
                  refine ⟨51278460294268272657401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546970243138861575012277 51278460294268272657401)
                  ·
                    rfl

theorem cell21_224695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_224695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224695 prefixEnd_224695 := by exact prefixLift 224695
  have htrace : WordTrace (prefixWord ++ tailWord_224695) baseStart_224695 baseEnd_224695 := by
    simpa [prefixWord, tailWord_224695, baseEnd_224695] using wordTrace_append hprefix tailTrace_224695
  have hstable : (prefixWord ++ tailWord_224695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224695).length < 2 ^ (prefixWord ++ tailWord_224695).sum := by decide
  have hdescent : baseEnd_224695 < baseStart_224695 := by decide
  rcases family_descends (prefixWord ++ tailWord_224695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224785 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_224785 : Nat := 118140960795 + 224785 * 2 ^ 59
def prefixEnd_224785 : Nat := 4983230072969 + 3 ^ 40 * 224785 * 2
def baseEnd_224785 : Nat := 51298999520448116157217

theorem tailTrace_224785 : CollatzResearch.WordTrace tailWord_224785 prefixEnd_224785 51298999520448116157217 := by
  unfold tailWord_224785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8198582490649810066707809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5465721660433206711138539 8198582490649810066707809)
  ·
    refine ⟨6148936867987357550030857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8198582490649810066707809 6148936867987357550030857)
    ·
      refine ⟨4611702650990518162523143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6148936867987357550030857 4611702650990518162523143)
      ·
        refine ⟨6917553976485777243784715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611702650990518162523143 6917553976485777243784715)
        ·
          refine ⟨10376330964728665865677073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917553976485777243784715 10376330964728665865677073)
          ·
            refine ⟨7782248223546499399257805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10376330964728665865677073 7782248223546499399257805)
            ·
              refine ⟨2918343083829937274721677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7782248223546499399257805 2918343083829937274721677)
              ·
                refine ⟨1094378656436226478020629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2918343083829937274721677 1094378656436226478020629)
                ·
                  refine ⟨51298999520448116157217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1094378656436226478020629 51298999520448116157217)
                  ·
                    rfl

theorem cell21_224785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_224785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224785 prefixEnd_224785 := by exact prefixLift 224785
  have htrace : WordTrace (prefixWord ++ tailWord_224785) baseStart_224785 baseEnd_224785 := by
    simpa [prefixWord, tailWord_224785, baseEnd_224785] using wordTrace_append hprefix tailTrace_224785
  have hstable : (prefixWord ++ tailWord_224785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224785).length < 2 ^ (prefixWord ++ tailWord_224785).sum := by decide
  have hdescent : baseEnd_224785 < baseStart_224785 := by decide
  rcases family_descends (prefixWord ++ tailWord_224785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224839 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 3]
def baseStart_224839 : Nat := 118140960795 + 224839 * 2 ^ 59
def prefixEnd_224839 : Nat := 4983230072969 + 3 ^ 40 * 224839 * 2
def baseEnd_224839 : Nat := 51311323056156022257107

theorem tailTrace_224839 : CollatzResearch.WordTrace tailWord_224839 prefixEnd_224839 51311323056156022257107 := by
  unfold tailWord_224839
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200552032454177289173571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5467034688302784859449047 8200552032454177289173571)
  ·
    refine ⟨12300828048681265933760357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8200552032454177289173571 12300828048681265933760357)
    ·
      refine ⟨2306405259127737362580067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12300828048681265933760357 2306405259127737362580067)
      ·
        refine ⟨3459607888691606043870101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306405259127737362580067 3459607888691606043870101)
        ·
          refine ⟨162169119782419033306411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3459607888691606043870101 162169119782419033306411)
          ·
            refine ⟨243253679673628549959617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162169119782419033306411 243253679673628549959617)
            ·
              refine ⟨182440259755221412469713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243253679673628549959617 182440259755221412469713)
              ·
                refine ⟨136830194816416059352285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182440259755221412469713 136830194816416059352285)
                ·
                  refine ⟨51311323056156022257107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136830194816416059352285 51311323056156022257107)
                  ·
                    rfl

theorem cell21_224839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].length) (baseStart_224839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224839 prefixEnd_224839 := by exact prefixLift 224839
  have htrace : WordTrace (prefixWord ++ tailWord_224839) baseStart_224839 baseEnd_224839 := by
    simpa [prefixWord, tailWord_224839, baseEnd_224839] using wordTrace_append hprefix tailTrace_224839
  have hstable : (prefixWord ++ tailWord_224839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224839).length < 2 ^ (prefixWord ++ tailWord_224839).sum := by decide
  have hdescent : baseEnd_224839 < baseStart_224839 := by decide
  rcases family_descends (prefixWord ++ tailWord_224839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224926 : List Nat := [4, 3, 1, 1, 1, 2, 4, 5]
def baseStart_224926 : Nat := 118140960795 + 224926 * 2 ^ 59
def prefixEnd_224926 : Nat := 4983230072969 + 3 ^ 40 * 224926 * 2
def baseEnd_224926 : Nat := 17110392547154401435643

theorem tailTrace_224926 : CollatzResearch.WordTrace tailWord_224926 prefixEnd_224926 17110392547154401435643 := by
  unfold tailWord_224926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025465647892373893448829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5469150122092660765060421 1025465647892373893448829)
  ·
    refine ⟨384549617959640210043311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1025465647892373893448829 384549617959640210043311)
    ·
      refine ⟨576824426939460315064967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384549617959640210043311 576824426939460315064967)
      ·
        refine ⟨865236640409190472597451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576824426939460315064967 865236640409190472597451)
        ·
          refine ⟨1297854960613785708896177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865236640409190472597451 1297854960613785708896177)
          ·
            refine ⟨973391220460339281672133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297854960613785708896177 973391220460339281672133)
            ·
              refine ⟨182510853836313615313525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 973391220460339281672133 182510853836313615313525)
              ·
                refine ⟨17110392547154401435643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182510853836313615313525 17110392547154401435643)
                ·
                  rfl

theorem cell21_224926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_224926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224926 prefixEnd_224926 := by exact prefixLift 224926
  have htrace : WordTrace (prefixWord ++ tailWord_224926) baseStart_224926 baseEnd_224926 := by
    simpa [prefixWord, tailWord_224926, baseEnd_224926] using wordTrace_append hprefix tailTrace_224926
  have hstable : (prefixWord ++ tailWord_224926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224926).length < 2 ^ (prefixWord ++ tailWord_224926).sum := by decide
  have hdescent : baseEnd_224926 < baseStart_224926 := by decide
  rcases family_descends (prefixWord ++ tailWord_224926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224957 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 3]
def baseStart_224957 : Nat := 118140960795 + 224957 * 2 ^ 59
def prefixEnd_224957 : Nat := 4983230072969 + 3 ^ 40 * 224957 * 2
def baseEnd_224957 : Nat := 51338252263814039290199

theorem tailTrace_224957 : CollatzResearch.WordTrace tailWord_224957 prefixEnd_224957 51338252263814039290199 := by
  unfold tailWord_224957
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204855846026683441969125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5469903897351122294646083 8204855846026683441969125)
  ·
    refine ⟨1538410471130003145369211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8204855846026683441969125 1538410471130003145369211)
    ·
      refine ⟨2307615706695004718053817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538410471130003145369211 2307615706695004718053817)
      ·
        refine ⟨1730711780021253538540363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307615706695004718053817 1730711780021253538540363)
        ·
          refine ⟨2596067670031880307810545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730711780021253538540363 2596067670031880307810545)
          ·
            refine ⟨1947050752523910230857909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596067670031880307810545 1947050752523910230857909)
            ·
              refine ⟨182536008049116584142929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1947050752523910230857909 182536008049116584142929)
              ·
                refine ⟨136902006036837438107197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182536008049116584142929 136902006036837438107197)
                ·
                  refine ⟨51338252263814039290199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136902006036837438107197 51338252263814039290199)
                  ·
                    rfl

theorem cell21_224957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_224957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224957 prefixEnd_224957 := by exact prefixLift 224957
  have htrace : WordTrace (prefixWord ++ tailWord_224957) baseStart_224957 baseEnd_224957 := by
    simpa [prefixWord, tailWord_224957, baseEnd_224957] using wordTrace_append hprefix tailTrace_224957
  have hstable : (prefixWord ++ tailWord_224957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224957).length < 2 ^ (prefixWord ++ tailWord_224957).sum := by decide
  have hdescent : baseEnd_224957 < baseStart_224957 := by decide
  rcases family_descends (prefixWord ++ tailWord_224957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224968 : List Nat := [2, 1, 3, 1, 2, 2, 4, 6]
def baseStart_224968 : Nat := 118140960795 + 224968 * 2 ^ 59
def prefixEnd_224968 : Nat := 4983230072969 + 3 ^ 40 * 224968 * 2
def baseEnd_224968 : Nat := 17113587537893488202281

theorem tailTrace_224968 : CollatzResearch.WordTrace tailWord_224968 prefixEnd_224968 17113587537893488202281 := by
  unfold tailWord_224968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102628524493416160309779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5470171365991221547079705 4102628524493416160309779)
  ·
    refine ⟨6153942786740124240464669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102628524493416160309779 6153942786740124240464669)
    ·
      refine ⟨2307728545027546590174251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6153942786740124240464669 2307728545027546590174251)
      ·
        refine ⟨3461592817541319885261377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307728545027546590174251 3461592817541319885261377)
        ·
          refine ⟨2596194613155989913946033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461592817541319885261377 2596194613155989913946033)
          ·
            refine ⟨1947145959866992435459525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596194613155989913946033 1947145959866992435459525)
            ·
              refine ⟨365089867475061081648661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1947145959866992435459525 365089867475061081648661)
              ·
                refine ⟨17113587537893488202281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365089867475061081648661 17113587537893488202281)
                ·
                  rfl

theorem cell21_224968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_224968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_224968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_224968 prefixEnd_224968 := by exact prefixLift 224968
  have htrace : WordTrace (prefixWord ++ tailWord_224968) baseStart_224968 baseEnd_224968 := by
    simpa [prefixWord, tailWord_224968, baseEnd_224968] using wordTrace_append hprefix tailTrace_224968
  have hstable : (prefixWord ++ tailWord_224968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224968).length < 2 ^ (prefixWord ++ tailWord_224968).sum := by decide
  have hdescent : baseEnd_224968 < baseStart_224968 := by decide
  rcases family_descends (prefixWord ++ tailWord_224968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225109 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 3]
def baseStart_225109 : Nat := 118140960795 + 225109 * 2 ^ 59
def prefixEnd_225109 : Nat := 4983230072969 + 3 ^ 40 * 225109 * 2
def baseEnd_225109 : Nat := 51372940734695552756555

theorem tailTrace_225109 : CollatzResearch.WordTrace tailWord_225109 prefixEnd_225109 51372940734695552756555 := by
  unfold tailWord_225109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8210399741476013401502381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5473599827650675601001587 8210399741476013401502381)
  ·
    refine ⟨3078899903053505025563393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8210399741476013401502381 3078899903053505025563393)
    ·
      refine ⟨2309174927290128769172545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3078899903053505025563393 2309174927290128769172545)
      ·
        refine ⟨1731881195467596576879409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309174927290128769172545 1731881195467596576879409)
        ·
          refine ⟨1298910896600697432659557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731881195467596576879409 1298910896600697432659557)
          ·
            refine ⟨243545793112630768623667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1298910896600697432659557 243545793112630768623667)
            ·
              refine ⟨365318689668946152935501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243545793112630768623667 365318689668946152935501)
              ·
                refine ⟨136994508625854807350813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365318689668946152935501 136994508625854807350813)
                ·
                  refine ⟨51372940734695552756555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136994508625854807350813 51372940734695552756555)
                  ·
                    rfl

theorem cell21_225109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_225109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225109 prefixEnd_225109 := by exact prefixLift 225109
  have htrace : WordTrace (prefixWord ++ tailWord_225109) baseStart_225109 baseEnd_225109 := by
    simpa [prefixWord, tailWord_225109, baseEnd_225109] using wordTrace_append hprefix tailTrace_225109
  have hstable : (prefixWord ++ tailWord_225109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225109).length < 2 ^ (prefixWord ++ tailWord_225109).sum := by decide
  have hdescent : baseEnd_225109 < baseStart_225109 := by decide
  rcases family_descends (prefixWord ++ tailWord_225109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225120 : List Nat := [2, 1, 1, 3, 3, 4, 7]
def baseStart_225120 : Nat := 118140960795 + 225120 * 2 ^ 59
def prefixEnd_225120 : Nat := 4983230072969 + 3 ^ 40 * 225120 * 2
def baseEnd_225120 : Nat := 5708383453840219785911

theorem tailTrace_225120 : CollatzResearch.WordTrace tailWord_225120 prefixEnd_225120 5708383453840219785911 := by
  unfold tailWord_225120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105400472218081140076407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5473867296290774853435209 4105400472218081140076407)
  ·
    refine ⟨6158100708327121710114611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105400472218081140076407 6158100708327121710114611)
    ·
      refine ⟨9237151062490682565171917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158100708327121710114611 9237151062490682565171917)
      ·
        refine ⟨3463931648434005961939469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9237151062490682565171917 3463931648434005961939469)
        ·
          refine ⟨1298974368162752235727301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3463931648434005961939469 1298974368162752235727301)
          ·
            refine ⟨243557694030516044198869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1298974368162752235727301 243557694030516044198869)
            ·
              refine ⟨5708383453840219785911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243557694030516044198869 5708383453840219785911)
              ·
                rfl

theorem cell21_225120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 7].length) (baseStart_225120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225120 prefixEnd_225120 := by exact prefixLift 225120
  have htrace : WordTrace (prefixWord ++ tailWord_225120) baseStart_225120 baseEnd_225120 := by
    simpa [prefixWord, tailWord_225120, baseEnd_225120] using wordTrace_append hprefix tailTrace_225120
  have hstable : (prefixWord ++ tailWord_225120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225120).length < 2 ^ (prefixWord ++ tailWord_225120).sum := by decide
  have hdescent : baseEnd_225120 < baseStart_225120 := by decide
  rcases family_descends (prefixWord ++ tailWord_225120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225185 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 3]
def baseStart_225185 : Nat := 118140960795 + 225185 * 2 ^ 59
def prefixEnd_225185 : Nat := 4983230072969 + 3 ^ 40 * 225185 * 2
def baseEnd_225185 : Nat := 51390284970136309489733

theorem tailTrace_225185 : CollatzResearch.WordTrace tailWord_225185 prefixEnd_225185 51390284970136309489733 := by
  unfold tailWord_225185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213171689200678381269009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5475447792800452254179339 8213171689200678381269009)
  ·
    refine ⟨6159878766900508785951757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8213171689200678381269009 6159878766900508785951757)
    ·
      refine ⟨2309954537587690794731909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6159878766900508785951757 2309954537587690794731909)
      ·
        refine ⟨433116475797692024012233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2309954537587690794731909 433116475797692024012233)
        ·
          refine ⟨324837356848269018009175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433116475797692024012233 324837356848269018009175)
          ·
            refine ⟨487256035272403527013763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324837356848269018009175 487256035272403527013763)
            ·
              refine ⟨730884052908605290520645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487256035272403527013763 730884052908605290520645)
              ·
                refine ⟨137040759920363491972621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730884052908605290520645 137040759920363491972621)
                ·
                  refine ⟨51390284970136309489733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137040759920363491972621 51390284970136309489733)
                  ·
                    rfl

theorem cell21_225185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_225185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225185 prefixEnd_225185 := by exact prefixLift 225185
  have htrace : WordTrace (prefixWord ++ tailWord_225185) baseStart_225185 baseEnd_225185 := by
    simpa [prefixWord, tailWord_225185, baseEnd_225185] using wordTrace_append hprefix tailTrace_225185
  have hstable : (prefixWord ++ tailWord_225185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225185).length < 2 ^ (prefixWord ++ tailWord_225185).sum := by decide
  have hdescent : baseEnd_225185 < baseStart_225185 := by decide
  rcases family_descends (prefixWord ++ tailWord_225185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225213 : List Nat := [1, 4, 1, 2, 3, 2, 3, 5]
def baseStart_225213 : Nat := 118140960795 + 225213 * 2 ^ 59
def prefixEnd_225213 : Nat := 4983230072969 + 3 ^ 40 * 225213 * 2
def baseEnd_225213 : Nat := 17132224983871494341003

theorem tailTrace_225213 : CollatzResearch.WordTrace tailWord_225213 prefixEnd_225213 17132224983871494341003 := by
  unfold tailWord_225213
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214192933099239163288293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5476128622066159442192195 8214192933099239163288293)
  ·
    refine ⟨1540161174956107343116555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8214192933099239163288293 1540161174956107343116555)
    ·
      refine ⟨2310241762434161014674833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540161174956107343116555 2310241762434161014674833)
      ·
        refine ⟨1732681321825620761006125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2310241762434161014674833 1732681321825620761006125)
        ·
          refine ⟨649755495684607785377297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1732681321825620761006125 649755495684607785377297)
          ·
            refine ⟨487316621763455839032973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649755495684607785377297 487316621763455839032973)
            ·
              refine ⟨182743733161295939637365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487316621763455839032973 182743733161295939637365)
              ·
                refine ⟨17132224983871494341003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182743733161295939637365 17132224983871494341003)
                ·
                  rfl

theorem cell21_225213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].length) (baseStart_225213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225213 prefixEnd_225213 := by exact prefixLift 225213
  have htrace : WordTrace (prefixWord ++ tailWord_225213) baseStart_225213 baseEnd_225213 := by
    simpa [prefixWord, tailWord_225213, baseEnd_225213] using wordTrace_append hprefix tailTrace_225213
  have hstable : (prefixWord ++ tailWord_225213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225213).length < 2 ^ (prefixWord ++ tailWord_225213).sum := by decide
  have hdescent : baseEnd_225213 < baseStart_225213 := by decide
  rcases family_descends (prefixWord ++ tailWord_225213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225272 : List Nat := [2, 1, 2, 1, 1, 3, 6, 5]
def baseStart_225272 : Nat := 118140960795 + 225272 * 2 ^ 59
def prefixEnd_225272 : Nat := 4983230072969 + 3 ^ 40 * 225272 * 2
def baseEnd_225272 : Nat := 17136713185147830513185

theorem tailTrace_225272 : CollatzResearch.WordTrace tailWord_225272 prefixEnd_225272 17136713185147830513185 := by
  unfold tailWord_225272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108172419942746119843035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5477563226590328159790713 4108172419942746119843035)
  ·
    refine ⟨6162258629914119179764553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4108172419942746119843035 6162258629914119179764553)
    ·
      refine ⟨4621693972435589384823415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162258629914119179764553 4621693972435589384823415)
      ·
        refine ⟨6932540958653384077235123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621693972435589384823415 6932540958653384077235123)
        ·
          refine ⟨10398811437980076115852685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932540958653384077235123 10398811437980076115852685)
          ·
            refine ⟨3899554289242528543444757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10398811437980076115852685 3899554289242528543444757)
            ·
              refine ⟨182791607308243525473973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3899554289242528543444757 182791607308243525473973)
              ·
                refine ⟨17136713185147830513185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182791607308243525473973 17136713185147830513185)
                ·
                  rfl

theorem cell21_225272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_225272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225272 prefixEnd_225272 := by exact prefixLift 225272
  have htrace : WordTrace (prefixWord ++ tailWord_225272) baseStart_225272 baseEnd_225272 := by
    simpa [prefixWord, tailWord_225272, baseEnd_225272] using wordTrace_append hprefix tailTrace_225272
  have hstable : (prefixWord ++ tailWord_225272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225272).length < 2 ^ (prefixWord ++ tailWord_225272).sum := by decide
  have hdescent : baseEnd_225272 < baseStart_225272 := by decide
  rcases family_descends (prefixWord ++ tailWord_225272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225278 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_225278 : Nat := 118140960795 + 225278 * 2 ^ 59
def prefixEnd_225278 : Nat := 4983230072969 + 3 ^ 40 * 225278 * 2
def baseEnd_225278 : Nat := 51411508837188814439543

theorem tailTrace_225278 : CollatzResearch.WordTrace tailWord_225278 prefixEnd_225278 51411508837188814439543 := by
  unfold tailWord_225278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027070459732969408050561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5477709118575836842936325 1027070459732969408050561)
  ·
    refine ⟨770302844799727056037921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1027070459732969408050561 770302844799727056037921)
    ·
      refine ⟨577727133599795292028441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770302844799727056037921 577727133599795292028441)
      ·
        refine ⟨433295350199846469021331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577727133599795292028441 433295350199846469021331)
        ·
          refine ⟨649943025299769703531997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433295350199846469021331 649943025299769703531997)
          ·
            refine ⟨243728634487413638824499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649943025299769703531997 243728634487413638824499)
            ·
              refine ⟨365592951731120458236749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243728634487413638824499 365592951731120458236749)
              ·
                refine ⟨137097356899170171838781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365592951731120458236749 137097356899170171838781)
                ·
                  refine ⟨51411508837188814439543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137097356899170171838781 51411508837188814439543)
                  ·
                    rfl

theorem cell21_225278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_225278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225278 prefixEnd_225278 := by exact prefixLift 225278
  have htrace : WordTrace (prefixWord ++ tailWord_225278) baseStart_225278 baseEnd_225278 := by
    simpa [prefixWord, tailWord_225278, baseEnd_225278] using wordTrace_append hprefix tailTrace_225278
  have hstable : (prefixWord ++ tailWord_225278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225278).length < 2 ^ (prefixWord ++ tailWord_225278).sum := by decide
  have hdescent : baseEnd_225278 < baseStart_225278 := by decide
  rcases family_descends (prefixWord ++ tailWord_225278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225331 : List Nat := [1, 1, 1, 2, 4, 1, 4, 7]
def baseStart_225331 : Nat := 118140960795 + 225331 * 2 ^ 59
def prefixEnd_225331 : Nat := 4983230072969 + 3 ^ 40 * 225331 * 2
def baseEnd_225331 : Nat := 17141201386424166685367

theorem tailTrace_225331 : CollatzResearch.WordTrace tailWord_225331 prefixEnd_225331 17141201386424166685367 := by
  unfold tailWord_225331
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218496746671745316083847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478997831114496877389231 8218496746671745316083847)
  ·
    refine ⟨12327745120007617974125771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218496746671745316083847 12327745120007617974125771)
    ·
      refine ⟨18491617680011426961188657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327745120007617974125771 18491617680011426961188657)
      ·
        refine ⟨13868713260008570220891493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18491617680011426961188657 13868713260008570220891493)
        ·
          refine ⟨2600383736251606916417155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13868713260008570220891493 2600383736251606916417155)
          ·
            refine ⟨3900575604377410374625733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600383736251606916417155 3900575604377410374625733)
            ·
              refine ⟨731357925820764445242325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3900575604377410374625733 731357925820764445242325)
              ·
                refine ⟨17141201386424166685367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 731357925820764445242325 17141201386424166685367)
                ·
                  rfl

theorem cell21_225331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_225331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225331 prefixEnd_225331 := by exact prefixLift 225331
  have htrace : WordTrace (prefixWord ++ tailWord_225331) baseStart_225331 baseEnd_225331 := by
    simpa [prefixWord, tailWord_225331, baseEnd_225331] using wordTrace_append hprefix tailTrace_225331
  have hstable : (prefixWord ++ tailWord_225331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225331).length < 2 ^ (prefixWord ++ tailWord_225331).sum := by decide
  have hdescent : baseEnd_225331 < baseStart_225331 := by decide
  rcases family_descends (prefixWord ++ tailWord_225331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225441 : List Nat := [1, 2, 3, 3, 1, 4, 2, 5]
def baseStart_225441 : Nat := 118140960795 + 225441 * 2 ^ 59
def prefixEnd_225441 : Nat := 4983230072969 + 3 ^ 40 * 225441 * 2
def baseEnd_225441 : Nat := 17149569219312251074181

theorem tailTrace_225441 : CollatzResearch.WordTrace tailWord_225441 prefixEnd_225441 17149569219312251074181 := by
  unfold tailWord_225441
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222508776273234102588177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481672517515489401725451 8222508776273234102588177)
  ·
    refine ⟨6166881582204925576941133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8222508776273234102588177 6166881582204925576941133)
    ·
      refine ⟨2312580593326847091352925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6166881582204925576941133 2312580593326847091352925)
      ·
        refine ⟨867217722497567659257347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2312580593326847091352925 867217722497567659257347)
        ·
          refine ⟨1300826583746351488886021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867217722497567659257347 1300826583746351488886021)
          ·
            refine ⟨243904984452440904166129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1300826583746351488886021 243904984452440904166129)
            ·
              refine ⟨182928738339330678124597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243904984452440904166129 182928738339330678124597)
              ·
                refine ⟨17149569219312251074181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182928738339330678124597 17149569219312251074181)
                ·
                  rfl

theorem cell21_225441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].length) (baseStart_225441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225441 prefixEnd_225441 := by exact prefixLift 225441
  have htrace : WordTrace (prefixWord ++ tailWord_225441) baseStart_225441 baseEnd_225441 := by
    simpa [prefixWord, tailWord_225441, baseEnd_225441] using wordTrace_append hprefix tailTrace_225441
  have hstable : (prefixWord ++ tailWord_225441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225441).length < 2 ^ (prefixWord ++ tailWord_225441).sum := by decide
  have hdescent : baseEnd_225441 < baseStart_225441 := by decide
  rcases family_descends (prefixWord ++ tailWord_225441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225469 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_225469 : Nat := 118140960795 + 225469 * 2 ^ 59
def prefixEnd_225469 : Nat := 4983230072969 + 3 ^ 40 * 225469 * 2
def baseEnd_225469 : Nat := 51455097639414926755819

theorem tailTrace_225469 : CollatzResearch.WordTrace tailWord_225469 prefixEnd_225469 51455097639414926755819 := by
  unfold tailWord_225469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223530020171794884607461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5482353346781196589738307 8223530020171794884607461)
  ·
    refine ⟨1541911878782211540863899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8223530020171794884607461 1541911878782211540863899)
    ·
      refine ⟨2312867818173317311295849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541911878782211540863899 2312867818173317311295849)
      ·
        refine ⟨1734650863629987983471887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2312867818173317311295849 1734650863629987983471887)
        ·
          refine ⟨2601976295444981975207831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734650863629987983471887 2601976295444981975207831)
          ·
            refine ⟨3902964443167472962811747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601976295444981975207831 3902964443167472962811747)
            ·
              refine ⟨5854446664751209444217621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902964443167472962811747 5854446664751209444217621)
              ·
                refine ⟨274427187410212942697701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5854446664751209444217621 274427187410212942697701)
                ·
                  refine ⟨51455097639414926755819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274427187410212942697701 51455097639414926755819)
                  ·
                    rfl

theorem cell21_225469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_225469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225469 prefixEnd_225469 := by exact prefixLift 225469
  have htrace : WordTrace (prefixWord ++ tailWord_225469) baseStart_225469 baseEnd_225469 := by
    simpa [prefixWord, tailWord_225469, baseEnd_225469] using wordTrace_append hprefix tailTrace_225469
  have hstable : (prefixWord ++ tailWord_225469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225469).length < 2 ^ (prefixWord ++ tailWord_225469).sum := by decide
  have hdescent : baseEnd_225469 < baseStart_225469 := by decide
  rcases family_descends (prefixWord ++ tailWord_225469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225483 : List Nat := [1, 1, 1, 1, 3, 2, 6, 6]
def baseStart_225483 : Nat := 118140960795 + 225483 * 2 ^ 59
def prefixEnd_225483 : Nat := 4983230072969 + 3 ^ 40 * 225483 * 2
def baseEnd_225483 : Nat := 17152764210051337840819

theorem tailTrace_225483 : CollatzResearch.WordTrace tailWord_225483 prefixEnd_225483 17152764210051337840819 := by
  unfold tailWord_225483
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224040642121075275617103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5482693761414050183744735 8224040642121075275617103)
  ·
    refine ⟨12336060963181612913425655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8224040642121075275617103 12336060963181612913425655)
    ·
      refine ⟨18504091444772419370138483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336060963181612913425655 18504091444772419370138483)
      ·
        refine ⟨27756137167158629055207725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504091444772419370138483 27756137167158629055207725)
        ·
          refine ⟨10408551437684485895702897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27756137167158629055207725 10408551437684485895702897)
          ·
            refine ⟨7806413578263364421777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408551437684485895702897 7806413578263364421777173)
            ·
              refine ⟨365925636481095207270805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7806413578263364421777173 365925636481095207270805)
              ·
                refine ⟨17152764210051337840819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365925636481095207270805 17152764210051337840819)
                ·
                  rfl

theorem cell21_225483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_225483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225483 prefixEnd_225483 := by exact prefixLift 225483
  have htrace : WordTrace (prefixWord ++ tailWord_225483) baseStart_225483 baseEnd_225483 := by
    simpa [prefixWord, tailWord_225483, baseEnd_225483] using wordTrace_append hprefix tailTrace_225483
  have hstable : (prefixWord ++ tailWord_225483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225483).length < 2 ^ (prefixWord ++ tailWord_225483).sum := by decide
  have hdescent : baseEnd_225483 < baseStart_225483 := by decide
  rcases family_descends (prefixWord ++ tailWord_225483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225486 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_225486 : Nat := 118140960795 + 225486 * 2 ^ 59
def prefixEnd_225486 : Nat := 4983230072969 + 3 ^ 40 * 225486 * 2
def baseEnd_225486 : Nat := 51458977271026674972451

theorem tailTrace_225486 : CollatzResearch.WordTrace tailWord_225486 prefixEnd_225486 51458977271026674972451 := by
  unfold tailWord_225486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028018757638775848497039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5482766707406804525317541 1028018757638775848497039)
  ·
    refine ⟨1542028136458163772745559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028018757638775848497039 1542028136458163772745559)
    ·
      refine ⟨2313042204687245659118339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542028136458163772745559 2313042204687245659118339)
      ·
        refine ⟨3469563307030868488677509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313042204687245659118339 3469563307030868488677509)
        ·
          refine ⟨650543120068287841627033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3469563307030868488677509 650543120068287841627033)
          ·
            refine ⟨487907340051215881220275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650543120068287841627033 487907340051215881220275)
            ·
              refine ⟨731861010076823821830413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487907340051215881220275 731861010076823821830413)
              ·
                refine ⟨274447878778808933186405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731861010076823821830413 274447878778808933186405)
                ·
                  refine ⟨51458977271026674972451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274447878778808933186405 51458977271026674972451)
                  ·
                    rfl

theorem cell21_225486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_225486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225486 prefixEnd_225486 := by exact prefixLift 225486
  have htrace : WordTrace (prefixWord ++ tailWord_225486) baseStart_225486 baseEnd_225486 := by
    simpa [prefixWord, tailWord_225486, baseEnd_225486] using wordTrace_append hprefix tailTrace_225486
  have hstable : (prefixWord ++ tailWord_225486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225486).length < 2 ^ (prefixWord ++ tailWord_225486).sum := by decide
  have hdescent : baseEnd_225486 < baseStart_225486 := by decide
  rcases family_descends (prefixWord ++ tailWord_225486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225528 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_225528 : Nat := 118140960795 + 225528 * 2 ^ 59
def prefixEnd_225528 : Nat := 4983230072969 + 3 ^ 40 * 225528 * 2
def baseEnd_225528 : Nat := 51468562243243935272365

theorem tailTrace_225528 : CollatzResearch.WordTrace tailWord_225528 prefixEnd_225528 51468562243243935272365 := by
  unfold tailWord_225528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112840963479023980502619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5483787951305365307336825 4112840963479023980502619)
  ·
    refine ⟨6169261445218535970753929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4112840963479023980502619 6169261445218535970753929)
    ·
      refine ⟨4626946083913901978065447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6169261445218535970753929 4626946083913901978065447)
      ·
        refine ⟨6940419125870852967098171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626946083913901978065447 6940419125870852967098171)
        ·
          refine ⟨10410628688806279450647257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940419125870852967098171 10410628688806279450647257)
          ·
            refine ⟨7807971516604709587985443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10410628688806279450647257 7807971516604709587985443)
            ·
              refine ⟨11711957274907064381978165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807971516604709587985443 11711957274907064381978165)
              ·
                refine ⟨1097995994522537285810453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11711957274907064381978165 1097995994522537285810453)
                ·
                  refine ⟨51468562243243935272365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1097995994522537285810453 51468562243243935272365)
                  ·
                    rfl

theorem cell21_225528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_225528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225528 prefixEnd_225528 := by exact prefixLift 225528
  have htrace : WordTrace (prefixWord ++ tailWord_225528) baseStart_225528 baseEnd_225528 := by
    simpa [prefixWord, tailWord_225528, baseEnd_225528] using wordTrace_append hprefix tailTrace_225528
  have hstable : (prefixWord ++ tailWord_225528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225528).length < 2 ^ (prefixWord ++ tailWord_225528).sum := by decide
  have hdescent : baseEnd_225528 < baseStart_225528 := by decide
  rcases family_descends (prefixWord ++ tailWord_225528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225545 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_225545 : Nat := 118140960795 + 225545 * 2 ^ 59
def prefixEnd_225545 : Nat := 4983230072969 + 3 ^ 40 * 225545 * 2
def baseEnd_225545 : Nat := 51472441874855683488997

theorem tailTrace_225545 : CollatzResearch.WordTrace tailWord_225545 prefixEnd_225545 51472441874855683488997 := by
  unfold tailWord_225545
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226301967896459864374089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484201311930973242916059 8226301967896459864374089)
  ·
    refine ⟨6169726475922344898280567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8226301967896459864374089 6169726475922344898280567)
    ·
      refine ⟨9254589713883517347420851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169726475922344898280567 9254589713883517347420851)
      ·
        refine ⟨13881884570825276021131277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9254589713883517347420851 13881884570825276021131277)
        ·
          refine ⟨5205706714059478507924229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13881884570825276021131277 5205706714059478507924229)
          ·
            refine ⟨976070008886152220235793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5205706714059478507924229 976070008886152220235793)
            ·
              refine ⟨732052506664614165176845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976070008886152220235793 732052506664614165176845)
              ·
                refine ⟨274519689999230311941317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732052506664614165176845 274519689999230311941317)
                ·
                  refine ⟨51472441874855683488997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274519689999230311941317 51472441874855683488997)
                  ·
                    rfl

theorem cell21_225545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_225545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225545 prefixEnd_225545 := by exact prefixLift 225545
  have htrace : WordTrace (prefixWord ++ tailWord_225545) baseStart_225545 baseEnd_225545 := by
    simpa [prefixWord, tailWord_225545, baseEnd_225545] using wordTrace_append hprefix tailTrace_225545
  have hstable : (prefixWord ++ tailWord_225545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225545).length < 2 ^ (prefixWord ++ tailWord_225545).sum := by decide
  have hdescent : baseEnd_225545 < baseStart_225545 := by decide
  rcases family_descends (prefixWord ++ tailWord_225545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225565 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 3]
def baseStart_225565 : Nat := 118140960795 + 225565 * 2 ^ 59
def prefixEnd_225565 : Nat := 4983230072969 + 3 ^ 40 * 225565 * 2
def baseEnd_225565 : Nat := 51477006147340093155623

theorem tailTrace_225565 : CollatzResearch.WordTrace tailWord_225565 prefixEnd_225565 51477006147340093155623 := by
  unfold tailWord_225565
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227031427824003280102149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484687618549335520068099 8227031427824003280102149)
  ·
    refine ⟨1542568392717000615019153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8227031427824003280102149 1542568392717000615019153)
    ·
      refine ⟨1156926294537750461264365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542568392717000615019153 1156926294537750461264365)
      ·
        refine ⟨433847360451656422974137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1156926294537750461264365 433847360451656422974137)
        ·
          refine ⟨325385520338742317230603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433847360451656422974137 325385520338742317230603)
          ·
            refine ⟨488078280508113475845905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325385520338742317230603 488078280508113475845905)
            ·
              refine ⟨366058710381085106884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488078280508113475845905 366058710381085106884429)
              ·
                refine ⟨137272016392906915081661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366058710381085106884429 137272016392906915081661)
                ·
                  refine ⟨51477006147340093155623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137272016392906915081661 51477006147340093155623)
                  ·
                    rfl

theorem cell21_225565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_225565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225565 prefixEnd_225565 := by exact prefixLift 225565
  have htrace : WordTrace (prefixWord ++ tailWord_225565) baseStart_225565 baseEnd_225565 := by
    simpa [prefixWord, tailWord_225565, baseEnd_225565] using wordTrace_append hprefix tailTrace_225565
  have hstable : (prefixWord ++ tailWord_225565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225565).length < 2 ^ (prefixWord ++ tailWord_225565).sum := by decide
  have hdescent : baseEnd_225565 < baseStart_225565 := by decide
  rcases family_descends (prefixWord ++ tailWord_225565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225576 : List Nat := [2, 1, 5, 1, 3, 1, 8]
def baseStart_225576 : Nat := 118140960795 + 225576 * 2 ^ 59
def prefixEnd_225576 : Nat := 4983230072969 + 3 ^ 40 * 225576 * 2
def baseEnd_225576 : Nat := 5719946277467390941363

theorem tailTrace_225576 : CollatzResearch.WordTrace tailWord_225576 prefixEnd_225576 5719946277467390941363 := by
  unfold tailWord_225576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113716315392076079376291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5484955087189434772501721 4113716315392076079376291)
  ·
    refine ⟨6170574473088114119064437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113716315392076079376291 6170574473088114119064437)
    ·
      refine ⟨578491356852010698662291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6170574473088114119064437 578491356852010698662291)
      ·
        refine ⟨867737035278016047993437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578491356852010698662291 867737035278016047993437)
        ·
          refine ⟨325401388229256017997539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 867737035278016047993437 325401388229256017997539)
          ·
            refine ⟨488102082343884026996309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325401388229256017997539 488102082343884026996309)
            ·
              refine ⟨5719946277467390941363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 488102082343884026996309 5719946277467390941363)
              ·
                rfl

theorem cell21_225576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 8].length) (baseStart_225576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225576 prefixEnd_225576 := by exact prefixLift 225576
  have htrace : WordTrace (prefixWord ++ tailWord_225576) baseStart_225576 baseEnd_225576 := by
    simpa [prefixWord, tailWord_225576, baseEnd_225576] using wordTrace_append hprefix tailTrace_225576
  have hstable : (prefixWord ++ tailWord_225576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225576).length < 2 ^ (prefixWord ++ tailWord_225576).sum := by decide
  have hdescent : baseEnd_225576 < baseStart_225576 := by decide
  rcases family_descends (prefixWord ++ tailWord_225576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225686 : List Nat := [5, 3, 1, 2, 1, 9]
def baseStart_225686 : Nat := 118140960795 + 225686 * 2 ^ 59
def prefixEnd_225686 : Nat := 4983230072969 + 3 ^ 40 * 225686 * 2
def baseEnd_225686 : Nat := 1907578518365584134767

theorem tailTrace_225686 : CollatzResearch.WordTrace tailWord_225686 prefixEnd_225686 1907578518365584134767 := by
  unfold tailWord_225686
  simp only [CollatzResearch.WordTrace]
  refine ⟨514465291274102559078557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5487629773590427296837941 514465291274102559078557)
  ·
    refine ⟨192924484227788459654459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 514465291274102559078557 192924484227788459654459)
    ·
      refine ⟨289386726341682689481689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192924484227788459654459 289386726341682689481689)
      ·
        refine ⟨217040044756262017111267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289386726341682689481689 217040044756262017111267)
        ·
          refine ⟨325560067134393025666901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217040044756262017111267 325560067134393025666901)
          ·
            refine ⟨1907578518365584134767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 325560067134393025666901 1907578518365584134767)
            ·
              rfl

theorem cell21_225686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 9].length) (baseStart_225686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225686 prefixEnd_225686 := by exact prefixLift 225686
  have htrace : WordTrace (prefixWord ++ tailWord_225686) baseStart_225686 baseEnd_225686 := by
    simpa [prefixWord, tailWord_225686, baseEnd_225686] using wordTrace_append hprefix tailTrace_225686
  have hstable : (prefixWord ++ tailWord_225686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225686).length < 2 ^ (prefixWord ++ tailWord_225686).sum := by decide
  have hdescent : baseEnd_225686 < baseStart_225686 := by decide
  rcases family_descends (prefixWord ++ tailWord_225686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225700 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_225700 : Nat := 118140960795 + 225700 * 2 ^ 59
def prefixEnd_225700 : Nat := 4983230072969 + 3 ^ 40 * 225700 * 2
def baseEnd_225700 : Nat := 51507814986609858405347

theorem tailTrace_225700 : CollatzResearch.WordTrace tailWord_225700 prefixEnd_225700 51507814986609858405347 := by
  unfold tailWord_225700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115977641167460668133277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5487970188223280890844369 4115977641167460668133277)
  ·
    refine ⟨1543491615437797750549979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4115977641167460668133277 1543491615437797750549979)
    ·
      refine ⟨2315237423156696625824969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1543491615437797750549979 2315237423156696625824969)
      ·
        refine ⟨1736428067367522469368727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2315237423156696625824969 1736428067367522469368727)
        ·
          refine ⟨2604642101051283704053091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736428067367522469368727 2604642101051283704053091)
          ·
            refine ⟨3906963151576925556079637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604642101051283704053091 3906963151576925556079637)
            ·
              refine ⟨183138897730168385441233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3906963151576925556079637 183138897730168385441233)
              ·
                refine ⟨137354173297626289080925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183138897730168385441233 137354173297626289080925)
                ·
                  refine ⟨51507814986609858405347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137354173297626289080925 51507814986609858405347)
                  ·
                    rfl

theorem cell21_225700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_225700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225700 prefixEnd_225700 := by exact prefixLift 225700
  have htrace : WordTrace (prefixWord ++ tailWord_225700) baseStart_225700 baseEnd_225700 := by
    simpa [prefixWord, tailWord_225700, baseEnd_225700] using wordTrace_append hprefix tailTrace_225700
  have hstable : (prefixWord ++ tailWord_225700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225700).length < 2 ^ (prefixWord ++ tailWord_225700).sum := by decide
  have hdescent : baseEnd_225700 < baseStart_225700 := by decide
  rcases family_descends (prefixWord ++ tailWord_225700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225759 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 3]
def baseStart_225759 : Nat := 118140960795 + 225759 * 2 ^ 59
def prefixEnd_225759 : Nat := 4983230072969 + 3 ^ 40 * 225759 * 2
def baseEnd_225759 : Nat := 51521279590438866921893

theorem tailTrace_225759 : CollatzResearch.WordTrace tailWord_225759 prefixEnd_225759 51521279590438866921893 := by
  unfold tailWord_225759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234107189121174412664331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5489404792747449608442887 8234107189121174412664331)
  ·
    refine ⟨12351160783681761618996497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8234107189121174412664331 12351160783681761618996497)
    ·
      refine ⟨9263370587761321214247373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12351160783681761618996497 9263370587761321214247373)
      ·
        refine ⟨3473763970410495455342765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9263370587761321214247373 3473763970410495455342765)
        ·
          refine ⟨1302661488903935795753537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3473763970410495455342765 1302661488903935795753537)
          ·
            refine ⟨976996116677951846815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302661488903935795753537 976996116677951846815153)
            ·
              refine ⟨732747087508463885111365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976996116677951846815153 732747087508463885111365)
              ·
                refine ⟨137390078907836978458381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732747087508463885111365 137390078907836978458381)
                ·
                  refine ⟨51521279590438866921893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137390078907836978458381 51521279590438866921893)
                  ·
                    rfl

theorem cell21_225759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].length) (baseStart_225759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225759 prefixEnd_225759 := by exact prefixLift 225759
  have htrace : WordTrace (prefixWord ++ tailWord_225759) baseStart_225759 baseEnd_225759 := by
    simpa [prefixWord, tailWord_225759, baseEnd_225759] using wordTrace_append hprefix tailTrace_225759
  have hstable : (prefixWord ++ tailWord_225759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225759).length < 2 ^ (prefixWord ++ tailWord_225759).sum := by decide
  have hdescent : baseEnd_225759 < baseStart_225759 := by decide
  rcases family_descends (prefixWord ++ tailWord_225759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225818 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_225818 : Nat := 118140960795 + 225818 * 2 ^ 59
def prefixEnd_225818 : Nat := 4983230072969 + 3 ^ 40 * 225818 * 2
def baseEnd_225818 : Nat := 51534744194267875438439

theorem tailTrace_225818 : CollatzResearch.WordTrace tailWord_225818 prefixEnd_225818 51534744194267875438439 := by
  unfold tailWord_225818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059064773976856872265527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5490839397271618326041405 2059064773976856872265527)
  ·
    refine ⟨3088597160965285308398291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2059064773976856872265527 3088597160965285308398291)
    ·
      refine ⟨4632895741447927962597437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088597160965285308398291 4632895741447927962597437)
      ·
        refine ⟨1737335903042972985974039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4632895741447927962597437 1737335903042972985974039)
        ·
          refine ⟨2606003854564459478961059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737335903042972985974039 2606003854564459478961059)
          ·
            refine ⟨3909005781846689218441589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606003854564459478961059 3909005781846689218441589)
            ·
              refine ⟨366469292048127114228899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3909005781846689218441589 366469292048127114228899)
              ·
                refine ⟨549703938072190671343349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366469292048127114228899 549703938072190671343349)
                ·
                  refine ⟨51534744194267875438439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 549703938072190671343349 51534744194267875438439)
                  ·
                    rfl

theorem cell21_225818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_225818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225818 prefixEnd_225818 := by exact prefixLift 225818
  have htrace : WordTrace (prefixWord ++ tailWord_225818) baseStart_225818 baseEnd_225818 := by
    simpa [prefixWord, tailWord_225818, baseEnd_225818] using wordTrace_append hprefix tailTrace_225818
  have hstable : (prefixWord ++ tailWord_225818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225818).length < 2 ^ (prefixWord ++ tailWord_225818).sum := by decide
  have hdescent : baseEnd_225818 < baseStart_225818 := by decide
  rcases family_descends (prefixWord ++ tailWord_225818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225824 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_225824 : Nat := 118140960795 + 225824 * 2 ^ 59
def prefixEnd_225824 : Nat := 4983230072969 + 3 ^ 40 * 225824 * 2
def baseEnd_225824 : Nat := 51536113476013198338427

theorem tailTrace_225824 : CollatzResearch.WordTrace tailWord_225824 prefixEnd_225824 51536113476013198338427 := by
  unfold tailWord_225824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118238966942845256890263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5490985289257127009187017 4118238966942845256890263)
  ·
    refine ⟨6177358450414267885335395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4118238966942845256890263 6177358450414267885335395)
    ·
      refine ⟨9266037675621401828003093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177358450414267885335395 9266037675621401828003093)
      ·
        refine ⟨434345516044753210687645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9266037675621401828003093 434345516044753210687645)
        ·
          refine ⟨162879568516782454007867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434345516044753210687645 162879568516782454007867)
          ·
            refine ⟨244319352775173681011801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162879568516782454007867 244319352775173681011801)
            ·
              refine ⟨183239514581380260758851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244319352775173681011801 183239514581380260758851)
              ·
                refine ⟨274859271872070391138277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183239514581380260758851 274859271872070391138277)
                ·
                  refine ⟨51536113476013198338427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274859271872070391138277 51536113476013198338427)
                  ·
                    rfl

theorem cell21_225824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_225824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225824 prefixEnd_225824 := by exact prefixLift 225824
  have htrace : WordTrace (prefixWord ++ tailWord_225824) baseStart_225824 baseEnd_225824 := by
    simpa [prefixWord, tailWord_225824, baseEnd_225824] using wordTrace_append hprefix tailTrace_225824
  have hstable : (prefixWord ++ tailWord_225824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225824).length < 2 ^ (prefixWord ++ tailWord_225824).sum := by decide
  have hdescent : baseEnd_225824 < baseStart_225824 := by decide
  rcases family_descends (prefixWord ++ tailWord_225824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225869 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 3]
def baseStart_225869 : Nat := 118140960795 + 225869 * 2 ^ 59
def prefixEnd_225869 : Nat := 4983230072969 + 3 ^ 40 * 225869 * 2
def baseEnd_225869 : Nat := 51546383089103120088335

theorem tailTrace_225869 : CollatzResearch.WordTrace tailWord_225869 prefixEnd_225869 51546383089103120088335 := by
  unfold tailWord_225869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238119218722663199168661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5492079479148442132779107 8238119218722663199168661)
  ·
    refine ⟨386161838377624837461031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8238119218722663199168661 386161838377624837461031)
    ·
      refine ⟨579242757566437256191547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386161838377624837461031 579242757566437256191547)
      ·
        refine ⟨868864136349655884287321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579242757566437256191547 868864136349655884287321)
        ·
          refine ⟨651648102262241913215491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868864136349655884287321 651648102262241913215491)
          ·
            refine ⟨977472153393362869823237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651648102262241913215491 977472153393362869823237)
            ·
              refine ⟨183276028761255538091857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 977472153393362869823237 183276028761255538091857)
              ·
                refine ⟨137457021570941653568893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183276028761255538091857 137457021570941653568893)
                ·
                  refine ⟨51546383089103120088335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137457021570941653568893 51546383089103120088335)
                  ·
                    rfl

theorem cell21_225869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_225869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225869 prefixEnd_225869 := by exact prefixLift 225869
  have htrace : WordTrace (prefixWord ++ tailWord_225869) baseStart_225869 baseEnd_225869 := by
    simpa [prefixWord, tailWord_225869, baseEnd_225869] using wordTrace_append hprefix tailTrace_225869
  have hstable : (prefixWord ++ tailWord_225869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225869).length < 2 ^ (prefixWord ++ tailWord_225869).sum := by decide
  have hdescent : baseEnd_225869 < baseStart_225869 := by decide
  rcases family_descends (prefixWord ++ tailWord_225869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225925 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_225925 : Nat := 118140960795 + 225925 * 2 ^ 59
def prefixEnd_225925 : Nat := 4983230072969 + 3 ^ 40 * 225925 * 2
def baseEnd_225925 : Nat := 51559163052059467154887

theorem tailTrace_225925 : CollatzResearch.WordTrace tailWord_225925 prefixEnd_225925 51559163052059467154887 := by
  unfold tailWord_225925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240161706519784763207229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5493441137679856508804819 8240161706519784763207229)
  ·
    refine ⟨3090060639944919286202711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8240161706519784763207229 3090060639944919286202711)
    ·
      refine ⟨4635090959917378929304067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090060639944919286202711 4635090959917378929304067)
      ·
        refine ⟨6952636439876068393956101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635090959917378929304067 6952636439876068393956101)
        ·
          refine ⟨1303619332476762823866769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6952636439876068393956101 1303619332476762823866769)
          ·
            refine ⟨977714499357572117900077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303619332476762823866769 977714499357572117900077)
            ·
              refine ⟨366642937259089544212529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 977714499357572117900077 366642937259089544212529)
              ·
                refine ⟨274982202944317158159397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366642937259089544212529 274982202944317158159397)
                ·
                  refine ⟨51559163052059467154887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274982202944317158159397 51559163052059467154887)
                  ·
                    rfl

theorem cell21_225925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_225925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225925 prefixEnd_225925 := by exact prefixLift 225925
  have htrace : WordTrace (prefixWord ++ tailWord_225925) baseStart_225925 baseEnd_225925 := by
    simpa [prefixWord, tailWord_225925, baseEnd_225925] using wordTrace_append hprefix tailTrace_225925
  have hstable : (prefixWord ++ tailWord_225925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225925).length < 2 ^ (prefixWord ++ tailWord_225925).sum := by decide
  have hdescent : baseEnd_225925 < baseStart_225925 := by decide
  rcases family_descends (prefixWord ++ tailWord_225925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225962 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_225962 : Nat := 118140960795 + 225962 * 2 ^ 59
def prefixEnd_225962 : Nat := 4983230072969 + 3 ^ 40 * 225962 * 2
def baseEnd_225962 : Nat := 51567606956155625038145

theorem tailTrace_225962 : CollatzResearch.WordTrace tailWord_225962 prefixEnd_225962 51567606956155625038145 := by
  unfold tailWord_225962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060377801846435020576035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5494340804923826721536093 2060377801846435020576035)
  ·
    refine ⟨3090566702769652530864053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060377801846435020576035 3090566702769652530864053)
    ·
      refine ⟨289740628384654924768505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3090566702769652530864053 289740628384654924768505)
      ·
        refine ⟨217305471288491193576379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289740628384654924768505 217305471288491193576379)
        ·
          refine ⟨325958206932736790364569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217305471288491193576379 325958206932736790364569)
          ·
            refine ⟨244468655199552592773427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325958206932736790364569 244468655199552592773427)
            ·
              refine ⟨366702982799328889160141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244468655199552592773427 366702982799328889160141)
              ·
                refine ⟨137513618549748333435053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366702982799328889160141 137513618549748333435053)
                ·
                  refine ⟨51567606956155625038145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137513618549748333435053 51567606956155625038145)
                  ·
                    rfl

theorem cell21_225962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_225962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225962 prefixEnd_225962 := by exact prefixLift 225962
  have htrace : WordTrace (prefixWord ++ tailWord_225962) baseStart_225962 baseEnd_225962 := by
    simpa [prefixWord, tailWord_225962, baseEnd_225962] using wordTrace_append hprefix tailTrace_225962
  have hstable : (prefixWord ++ tailWord_225962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225962).length < 2 ^ (prefixWord ++ tailWord_225962).sum := by decide
  have hdescent : baseEnd_225962 < baseStart_225962 := by decide
  rcases family_descends (prefixWord ++ tailWord_225962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225984 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_225984 : Nat := 118140960795 + 225984 * 2 ^ 59
def prefixEnd_225984 : Nat := 4983230072969 + 3 ^ 40 * 225984 * 2
def baseEnd_225984 : Nat := 51572627655888475671433

theorem tailTrace_225984 : CollatzResearch.WordTrace tailWord_225984 prefixEnd_225984 51572627655888475671433 := by
  unfold tailWord_225984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121156806653018919802503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5494875742204025226403337 4121156806653018919802503)
  ·
    refine ⟨6181735209979528379703755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4121156806653018919802503 6181735209979528379703755)
    ·
      refine ⟨9272602814969292569555633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181735209979528379703755 9272602814969292569555633)
      ·
        refine ⟨6954452111226969427166725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9272602814969292569555633 6954452111226969427166725)
        ·
          refine ⟨1303959770855056767593761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6954452111226969427166725 1303959770855056767593761)
          ·
            refine ⟨977969828141292575695321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303959770855056767593761 977969828141292575695321)
            ·
              refine ⟨733477371105969431771491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977969828141292575695321 733477371105969431771491)
              ·
                refine ⟨1100216056658954147657237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733477371105969431771491 1100216056658954147657237)
                ·
                  refine ⟨51572627655888475671433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1100216056658954147657237 51572627655888475671433)
                  ·
                    rfl

theorem cell21_225984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_225984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225984 prefixEnd_225984 := by exact prefixLift 225984
  have htrace : WordTrace (prefixWord ++ tailWord_225984) baseStart_225984 baseEnd_225984 := by
    simpa [prefixWord, tailWord_225984, baseEnd_225984] using wordTrace_append hprefix tailTrace_225984
  have hstable : (prefixWord ++ tailWord_225984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225984).length < 2 ^ (prefixWord ++ tailWord_225984).sum := by decide
  have hdescent : baseEnd_225984 < baseStart_225984 := by decide
  rcases family_descends (prefixWord ++ tailWord_225984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225990 : List Nat := [6, 1, 2, 1, 2, 1, 2, 6]
def baseStart_225990 : Nat := 118140960795 + 225990 * 2 ^ 59
def prefixEnd_225990 : Nat := 4983230072969 + 3 ^ 40 * 225990 * 2
def baseEnd_225990 : Nat := 17191332312544599523807

theorem tailTrace_225990 : CollatzResearch.WordTrace tailWord_225990 prefixEnd_225990 17191332312544599523807 := by
  unfold tailWord_225990
  simp only [CollatzResearch.WordTrace]
  refine ⟨257579139102634402010107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5495021634189533909548949 257579139102634402010107)
  ·
    refine ⟨386368708653951603015161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257579139102634402010107 386368708653951603015161)
    ·
      refine ⟨289776531490463702261371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386368708653951603015161 289776531490463702261371)
      ·
        refine ⟨434664797235695553392057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289776531490463702261371 434664797235695553392057)
        ·
          refine ⟨325998597926771665044043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434664797235695553392057 325998597926771665044043)
          ·
            refine ⟨488997896890157497566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325998597926771665044043 488997896890157497566065)
            ·
              refine ⟨366748422667618123174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488997896890157497566065 366748422667618123174549)
              ·
                refine ⟨17191332312544599523807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 366748422667618123174549 17191332312544599523807)
                ·
                  rfl

theorem cell21_225990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_225990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_225990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_225990 prefixEnd_225990 := by exact prefixLift 225990
  have htrace : WordTrace (prefixWord ++ tailWord_225990) baseStart_225990 baseEnd_225990 := by
    simpa [prefixWord, tailWord_225990, baseEnd_225990] using wordTrace_append hprefix tailTrace_225990
  have hstable : (prefixWord ++ tailWord_225990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225990).length < 2 ^ (prefixWord ++ tailWord_225990).sum := by decide
  have hdescent : baseEnd_225990 < baseStart_225990 := by decide
  rcases family_descends (prefixWord ++ tailWord_225990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226043 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_226043 : Nat := 118140960795 + 226043 * 2 ^ 59
def prefixEnd_226043 : Nat := 4983230072969 + 3 ^ 40 * 226043 * 2
def baseEnd_226043 : Nat := 51586092259717484187979

theorem tailTrace_226043 : CollatzResearch.WordTrace tailWord_226043 prefixEnd_226043 51586092259717484187979 := by
  unfold tailWord_226043
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244465520092290916002783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5496310346728193944001855 8244465520092290916002783)
  ·
    refine ⟨12366698280138436374004175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8244465520092290916002783 12366698280138436374004175)
    ·
      refine ⟨18550047420207654561006263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12366698280138436374004175 18550047420207654561006263)
      ·
        refine ⟨27825071130311481841509395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18550047420207654561006263 27825071130311481841509395)
        ·
          refine ⟨41737606695467222762264093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27825071130311481841509395 41737606695467222762264093)
          ·
            refine ⟨15651602510800208535849035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41737606695467222762264093 15651602510800208535849035)
            ·
              refine ⟨23477403766200312803773553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651602510800208535849035 23477403766200312803773553)
              ·
                refine ⟨17608052824650234602830165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23477403766200312803773553 17608052824650234602830165)
                ·
                  refine ⟨51586092259717484187979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17608052824650234602830165 51586092259717484187979)
                  ·
                    rfl

theorem cell21_226043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_226043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226043 prefixEnd_226043 := by exact prefixLift 226043
  have htrace : WordTrace (prefixWord ++ tailWord_226043) baseStart_226043 baseEnd_226043 := by
    simpa [prefixWord, tailWord_226043, baseEnd_226043] using wordTrace_append hprefix tailTrace_226043
  have hstable : (prefixWord ++ tailWord_226043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226043).length < 2 ^ (prefixWord ++ tailWord_226043).sum := by decide
  have hdescent : baseEnd_226043 < baseStart_226043 := by decide
  rcases family_descends (prefixWord ++ tailWord_226043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226094 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_226094 : Nat := 118140960795 + 226094 * 2 ^ 59
def prefixEnd_226094 : Nat := 4983230072969 + 3 ^ 40 * 226094 * 2
def baseEnd_226094 : Nat := 51597731154552728837875

theorem tailTrace_226094 : CollatzResearch.WordTrace tailWord_226094 prefixEnd_226094 51597731154552728837875 := by
  unfold tailWord_226094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030790705363440828263667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5497550428605017750739557 1030790705363440828263667)
  ·
    refine ⟨1546186058045161242395501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030790705363440828263667 1546186058045161242395501)
    ·
      refine ⟨579819771766935465898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1546186058045161242395501 579819771766935465898313)
      ·
        refine ⟨434864828825201599423735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579819771766935465898313 434864828825201599423735)
        ·
          refine ⟨652297243237802399135603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434864828825201599423735 652297243237802399135603)
          ·
            refine ⟨978445864856703598703405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652297243237802399135603 978445864856703598703405)
            ·
              refine ⟨366917199321263849513777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978445864856703598703405 366917199321263849513777)
              ·
                refine ⟨275187899490947887135333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366917199321263849513777 275187899490947887135333)
                ·
                  refine ⟨51597731154552728837875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275187899490947887135333 51597731154552728837875)
                  ·
                    rfl

theorem cell21_226094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_226094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226094 prefixEnd_226094 := by exact prefixLift 226094
  have htrace : WordTrace (prefixWord ++ tailWord_226094) baseStart_226094 baseEnd_226094 := by
    simpa [prefixWord, tailWord_226094, baseEnd_226094] using wordTrace_append hprefix tailTrace_226094
  have hstable : (prefixWord ++ tailWord_226094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226094).length < 2 ^ (prefixWord ++ tailWord_226094).sum := by decide
  have hdescent : baseEnd_226094 < baseStart_226094 := by decide
  rcases family_descends (prefixWord ++ tailWord_226094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226195 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_226195 : Nat := 118140960795 + 226195 * 2 ^ 59
def prefixEnd_226195 : Nat := 4983230072969 + 3 ^ 40 * 226195 * 2
def baseEnd_226195 : Nat := 51620780730598997654335

theorem tailTrace_226195 : CollatzResearch.WordTrace tailWord_226195 prefixEnd_226195 51620780730598997654335 := by
  unfold tailWord_226195
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250009415541620875536039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500006277027747250357359 8250009415541620875536039)
  ·
    refine ⟨12375014123312431313304059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8250009415541620875536039 12375014123312431313304059)
    ·
      refine ⟨18562521184968646969956089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375014123312431313304059 18562521184968646969956089)
      ·
        refine ⟨13921890888726485227467067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18562521184968646969956089 13921890888726485227467067)
        ·
          refine ⟨20882836333089727841200601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13921890888726485227467067 20882836333089727841200601)
          ·
            refine ⟨15662127249817295880900451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20882836333089727841200601 15662127249817295880900451)
            ·
              refine ⟨23493190874725943821350677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662127249817295880900451 23493190874725943821350677)
              ·
                refine ⟨1101243322252778616625813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23493190874725943821350677 1101243322252778616625813)
                ·
                  refine ⟨51620780730598997654335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1101243322252778616625813 51620780730598997654335)
                  ·
                    rfl

theorem cell21_226195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_226195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226195 prefixEnd_226195 := by exact prefixLift 226195
  have htrace : WordTrace (prefixWord ++ tailWord_226195) baseStart_226195 baseEnd_226195 := by
    simpa [prefixWord, tailWord_226195, baseEnd_226195] using wordTrace_append hprefix tailTrace_226195
  have hstable : (prefixWord ++ tailWord_226195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226195).length < 2 ^ (prefixWord ++ tailWord_226195).sum := by decide
  have hdescent : baseEnd_226195 < baseStart_226195 := by decide
  rcases family_descends (prefixWord ++ tailWord_226195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226336 : List Nat := [2, 1, 1, 7, 1, 1, 2, 6]
def baseStart_226336 : Nat := 118140960795 + 226336 * 2 ^ 59
def prefixEnd_226336 : Nat := 4983230072969 + 3 ^ 40 * 226336 * 2
def baseEnd_226336 : Nat := 17217652950538028601349

theorem tailTrace_226336 : CollatzResearch.WordTrace tailWord_226336 prefixEnd_226336 17217652950538028601349 := by
  unfold tailWord_226336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127576054015400978209431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5503434738687201304279241 4127576054015400978209431)
  ·
    refine ⟨6191364081023101467314147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127576054015400978209431 6191364081023101467314147)
    ·
      refine ⟨9287046121534652200971221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191364081023101467314147 9287046121534652200971221)
      ·
        refine ⟨217665143473468410960263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9287046121534652200971221 217665143473468410960263)
        ·
          refine ⟨326497715210202616440395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217665143473468410960263 326497715210202616440395)
          ·
            refine ⟨489746572815303924660593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326497715210202616440395 489746572815303924660593)
            ·
              refine ⟨367309929611477943495445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489746572815303924660593 367309929611477943495445)
              ·
                refine ⟨17217652950538028601349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367309929611477943495445 17217652950538028601349)
                ·
                  rfl

theorem cell21_226336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_226336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226336 prefixEnd_226336 := by exact prefixLift 226336
  have htrace : WordTrace (prefixWord ++ tailWord_226336) baseStart_226336 baseEnd_226336 := by
    simpa [prefixWord, tailWord_226336, baseEnd_226336] using wordTrace_append hprefix tailTrace_226336
  have hstable : (prefixWord ++ tailWord_226336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226336).length < 2 ^ (prefixWord ++ tailWord_226336).sum := by decide
  have hdescent : baseEnd_226336 < baseStart_226336 := by decide
  rcases family_descends (prefixWord ++ tailWord_226336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226381 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_226381 : Nat := 118140960795 + 226381 * 2 ^ 59
def prefixEnd_226381 : Nat := 4983230072969 + 3 ^ 40 * 226381 * 2
def baseEnd_226381 : Nat := 51663228464704007553955

theorem tailTrace_226381 : CollatzResearch.WordTrace tailWord_226381 prefixEnd_226381 51663228464704007553955 := by
  unfold tailWord_226381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8256793392867774641806997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5504528928578516427871331 8256793392867774641806997)
  ·
    refine ⟨387037190290676936334703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8256793392867774641806997 387037190290676936334703)
    ·
      refine ⟨580555785436015404502055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387037190290676936334703 580555785436015404502055)
      ·
        refine ⟨870833678154023106753083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580555785436015404502055 870833678154023106753083)
        ·
          refine ⟨1306250517231034660129625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870833678154023106753083 1306250517231034660129625)
          ·
            refine ⟨979687887923275995097219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306250517231034660129625 979687887923275995097219)
            ·
              refine ⟨1469531831884913992645829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979687887923275995097219 1469531831884913992645829)
              ·
                refine ⟨275537218478421373621093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1469531831884913992645829 275537218478421373621093)
                ·
                  refine ⟨51663228464704007553955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275537218478421373621093 51663228464704007553955)
                  ·
                    rfl

theorem cell21_226381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_226381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226381 prefixEnd_226381 := by exact prefixLift 226381
  have htrace : WordTrace (prefixWord ++ tailWord_226381) baseStart_226381 baseEnd_226381 := by
    simpa [prefixWord, tailWord_226381, baseEnd_226381] using wordTrace_append hprefix tailTrace_226381
  have hstable : (prefixWord ++ tailWord_226381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226381).length < 2 ^ (prefixWord ++ tailWord_226381).sum := by decide
  have hdescent : baseEnd_226381 < baseStart_226381 := by decide
  rcases family_descends (prefixWord ++ tailWord_226381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226409 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_226409 : Nat := 118140960795 + 226409 * 2 ^ 59
def prefixEnd_226409 : Nat := 4983230072969 + 3 ^ 40 * 226409 * 2
def baseEnd_226409 : Nat := 51669618446182181087231

theorem tailTrace_226409 : CollatzResearch.WordTrace tailWord_226409 prefixEnd_226409 51669618446182181087231 := by
  unfold tailWord_226409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257814636766335423826281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505209757844223615884187 8257814636766335423826281)
  ·
    refine ⟨6193360977574751567869711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8257814636766335423826281 6193360977574751567869711)
    ·
      refine ⟨9290041466362127351804567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193360977574751567869711 9290041466362127351804567)
      ·
        refine ⟨13935062199543191027706851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9290041466362127351804567 13935062199543191027706851)
        ·
          refine ⟨20902593299314786541560277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13935062199543191027706851 20902593299314786541560277)
          ·
            refine ⟨489904530452690309567819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20902593299314786541560277 489904530452690309567819)
            ·
              refine ⟨734856795679035464351729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489904530452690309567819 734856795679035464351729)
              ·
                refine ⟨551142596759276598263797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734856795679035464351729 551142596759276598263797)
                ·
                  refine ⟨51669618446182181087231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551142596759276598263797 51669618446182181087231)
                  ·
                    rfl

theorem cell21_226409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_226409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226409 prefixEnd_226409 := by exact prefixLift 226409
  have htrace : WordTrace (prefixWord ++ tailWord_226409) baseStart_226409 baseEnd_226409 := by
    simpa [prefixWord, tailWord_226409, baseEnd_226409] using wordTrace_append hprefix tailTrace_226409
  have hstable : (prefixWord ++ tailWord_226409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226409).length < 2 ^ (prefixWord ++ tailWord_226409).sum := by decide
  have hdescent : baseEnd_226409 < baseStart_226409 := by decide
  rcases family_descends (prefixWord ++ tailWord_226409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226423 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_226423 : Nat := 118140960795 + 226423 * 2 ^ 59
def prefixEnd_226423 : Nat := 4983230072969 + 3 ^ 40 * 226423 * 2
def baseEnd_226423 : Nat := 51672813436921267853869

theorem tailTrace_226423 : CollatzResearch.WordTrace tailWord_226423 prefixEnd_226423 51672813436921267853869 := by
  unfold tailWord_226423
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258325258715615814835923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505550172477077209890615 8258325258715615814835923)
  ·
    refine ⟨12387487888073423722253885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8258325258715615814835923 12387487888073423722253885)
    ·
      refine ⟨4645307958027533895845207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12387487888073423722253885 4645307958027533895845207)
      ·
        refine ⟨6967961937041300843767811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645307958027533895845207 6967961937041300843767811)
        ·
          refine ⟨10451942905561951265651717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967961937041300843767811 10451942905561951265651717)
          ·
            refine ⟨1959739294792865862309697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10451942905561951265651717 1959739294792865862309697)
            ·
              refine ⟨1469804471094649396732273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959739294792865862309697 1469804471094649396732273)
              ·
                refine ⟨1102353353320987047549205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469804471094649396732273 1102353353320987047549205)
                ·
                  refine ⟨51672813436921267853869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1102353353320987047549205 51672813436921267853869)
                  ·
                    rfl

theorem cell21_226423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_226423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226423 prefixEnd_226423 := by exact prefixLift 226423
  have htrace : WordTrace (prefixWord ++ tailWord_226423) baseStart_226423 baseEnd_226423 := by
    simpa [prefixWord, tailWord_226423, baseEnd_226423] using wordTrace_append hprefix tailTrace_226423
  have hstable : (prefixWord ++ tailWord_226423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226423).length < 2 ^ (prefixWord ++ tailWord_226423).sum := by decide
  have hdescent : baseEnd_226423 < baseStart_226423 := by decide
  rcases family_descends (prefixWord ++ tailWord_226423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226471 : List Nat := [1, 1, 6, 2, 1, 2, 1, 7]
def baseStart_226471 : Nat := 118140960795 + 226471 * 2 ^ 59
def prefixEnd_226471 : Nat := 4983230072969 + 3 ^ 40 * 226471 * 2
def baseEnd_226471 : Nat := 17227922563627950351257

theorem tailTrace_226471 : CollatzResearch.WordTrace tailWord_226471 prefixEnd_226471 17227922563627950351257 := by
  unfold tailWord_226471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260075962541720012583267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5506717308361146675055511 8260075962541720012583267)
  ·
    refine ⟨12390113943812580018874901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260075962541720012583267 12390113943812580018874901)
    ·
      refine ⟨580786591116214688384761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12390113943812580018874901 580786591116214688384761)
      ·
        refine ⟨435589943337161016288571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580786591116214688384761 435589943337161016288571)
        ·
          refine ⟨653384915005741524432857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435589943337161016288571 653384915005741524432857)
          ·
            refine ⟨490038686254306143324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653384915005741524432857 490038686254306143324643)
            ·
              refine ⟨735058029381459214986965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490038686254306143324643 735058029381459214986965)
              ·
                refine ⟨17227922563627950351257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 735058029381459214986965 17227922563627950351257)
                ·
                  rfl

theorem cell21_226471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_226471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226471 prefixEnd_226471 := by exact prefixLift 226471
  have htrace : WordTrace (prefixWord ++ tailWord_226471) baseStart_226471 baseEnd_226471 := by
    simpa [prefixWord, tailWord_226471, baseEnd_226471] using wordTrace_append hprefix tailTrace_226471
  have hstable : (prefixWord ++ tailWord_226471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226471).length < 2 ^ (prefixWord ++ tailWord_226471).sum := by decide
  have hdescent : baseEnd_226471 < baseStart_226471 := by decide
  rcases family_descends (prefixWord ++ tailWord_226471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226477 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 3]
def baseStart_226477 : Nat := 118140960795 + 226477 * 2 ^ 59
def prefixEnd_226477 : Nat := 4983230072969 + 3 ^ 40 * 226477 * 2
def baseEnd_226477 : Nat := 51685136972629173953759

theorem tailTrace_226477 : CollatzResearch.WordTrace tailWord_226477 prefixEnd_226477 51685136972629173953759 := by
  unfold tailWord_226477
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260294800519983037301685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5506863200346655358201123 8260294800519983037301685)
  ·
    refine ⟨774402637548748409747033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8260294800519983037301685 774402637548748409747033)
    ·
      refine ⟨580801978161561307310275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774402637548748409747033 580801978161561307310275)
      ·
        refine ⟨871202967242341960965413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580801978161561307310275 871202967242341960965413)
        ·
          refine ⟨163350556357939117681015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 871202967242341960965413 163350556357939117681015)
          ·
            refine ⟨245025834536908676521523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163350556357939117681015 245025834536908676521523)
            ·
              refine ⟨367538751805363014782285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245025834536908676521523 367538751805363014782285)
              ·
                refine ⟨137827031927011130543357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367538751805363014782285 137827031927011130543357)
                ·
                  refine ⟨51685136972629173953759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137827031927011130543357 51685136972629173953759)
                  ·
                    rfl

theorem cell21_226477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_226477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226477 prefixEnd_226477 := by exact prefixLift 226477
  have htrace : WordTrace (prefixWord ++ tailWord_226477) baseStart_226477 baseEnd_226477 := by
    simpa [prefixWord, tailWord_226477, baseEnd_226477] using wordTrace_append hprefix tailTrace_226477
  have hstable : (prefixWord ++ tailWord_226477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226477).length < 2 ^ (prefixWord ++ tailWord_226477).sum := by decide
  have hdescent : baseEnd_226477 < baseStart_226477 := by decide
  rcases family_descends (prefixWord ++ tailWord_226477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226609 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_226609 : Nat := 118140960795 + 226609 * 2 ^ 59
def prefixEnd_226609 : Nat := 4983230072969 + 3 ^ 40 * 226609 * 2
def baseEnd_226609 : Nat := 51715261171026277753489

theorem tailTrace_226609 : CollatzResearch.WordTrace tailWord_226609 prefixEnd_226609 51715261171026277753489 := by
  unfold tailWord_226609
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265109236041769581106881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5510072824027846387404587 8265109236041769581106881)
  ·
    refine ⟨6198831927031327185830161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8265109236041769581106881 6198831927031327185830161)
    ·
      refine ⟨4649123945273495389372621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6198831927031327185830161 4649123945273495389372621)
      ·
        refine ⟨1743421479477560771014733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4649123945273495389372621 1743421479477560771014733)
        ·
          refine ⟨653783054804085289130525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1743421479477560771014733 653783054804085289130525)
          ·
            refine ⟨245168645551531983423947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 653783054804085289130525 245168645551531983423947)
            ·
              refine ⟨367752968327297975135921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245168645551531983423947 367752968327297975135921)
              ·
                refine ⟨275814726245473481351941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367752968327297975135921 275814726245473481351941)
                ·
                  refine ⟨51715261171026277753489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275814726245473481351941 51715261171026277753489)
                  ·
                    rfl

theorem cell21_226609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_226609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226609 prefixEnd_226609 := by exact prefixLift 226609
  have htrace : WordTrace (prefixWord ++ tailWord_226609) baseStart_226609 baseEnd_226609 := by
    simpa [prefixWord, tailWord_226609, baseEnd_226609] using wordTrace_append hprefix tailTrace_226609
  have hstable : (prefixWord ++ tailWord_226609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226609).length < 2 ^ (prefixWord ++ tailWord_226609).sum := by decide
  have hdescent : baseEnd_226609 < baseStart_226609 := by decide
  rcases family_descends (prefixWord ++ tailWord_226609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226789 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_226789 : Nat := 118140960795 + 226789 * 2 ^ 59
def prefixEnd_226789 : Nat := 4983230072969 + 3 ^ 40 * 226789 * 2
def baseEnd_226789 : Nat := 51756339623385964753121

theorem tailTrace_226789 : CollatzResearch.WordTrace tailWord_226789 prefixEnd_226789 51756339623385964753121 := by
  unfold tailWord_226789
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271674375389660322659421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5514449583593106881772947 8271674375389660322659421)
  ·
    refine ⟨3101877890771122620997283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8271674375389660322659421 3101877890771122620997283)
    ·
      refine ⟨4652816836156683931495925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101877890771122620997283 4652816836156683931495925)
      ·
        refine ⟨436201578389689118577743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4652816836156683931495925 436201578389689118577743)
        ·
          refine ⟨654302367584533677866615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436201578389689118577743 654302367584533677866615)
          ·
            refine ⟨981453551376800516799923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654302367584533677866615 981453551376800516799923)
            ·
              refine ⟨1472180327065200775199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981453551376800516799923 1472180327065200775199885)
              ·
                refine ⟨552067622649450290699957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472180327065200775199885 552067622649450290699957)
                ·
                  refine ⟨51756339623385964753121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552067622649450290699957 51756339623385964753121)
                  ·
                    rfl

theorem cell21_226789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_226789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226789 prefixEnd_226789 := by exact prefixLift 226789
  have htrace : WordTrace (prefixWord ++ tailWord_226789) baseStart_226789 baseEnd_226789 := by
    simpa [prefixWord, tailWord_226789, baseEnd_226789] using wordTrace_append hprefix tailTrace_226789
  have hstable : (prefixWord ++ tailWord_226789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226789).length < 2 ^ (prefixWord ++ tailWord_226789).sum := by decide
  have hdescent : baseEnd_226789 < baseStart_226789 := by decide
  rcases family_descends (prefixWord ++ tailWord_226789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226823 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 3]
def baseStart_226823 : Nat := 118140960795 + 226823 * 2 ^ 59
def prefixEnd_226823 : Nat := 4983230072969 + 3 ^ 40 * 226823 * 2
def baseEnd_226823 : Nat := 51764098886609461186385

theorem tailTrace_226823 : CollatzResearch.WordTrace tailWord_226823 prefixEnd_226823 51764098886609461186385 := by
  unfold tailWord_226823
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272914457266484129397123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5515276304844322752931415 8272914457266484129397123)
  ·
    refine ⟨12409371685899726194095685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272914457266484129397123 12409371685899726194095685)
    ·
      refine ⟨2326757191106198661392941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12409371685899726194095685 2326757191106198661392941)
      ·
        refine ⟨872533946664824498022353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2326757191106198661392941 872533946664824498022353)
        ·
          refine ⟨654400459998618373516765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872533946664824498022353 654400459998618373516765)
          ·
            refine ⟨245400172499481890068787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654400459998618373516765 245400172499481890068787)
            ·
              refine ⟨368100258749222835103181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245400172499481890068787 368100258749222835103181)
              ·
                refine ⟨138037597030958563163693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368100258749222835103181 138037597030958563163693)
                ·
                  refine ⟨51764098886609461186385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138037597030958563163693 51764098886609461186385)
                  ·
                    rfl

theorem cell21_226823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].length) (baseStart_226823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226823 prefixEnd_226823 := by exact prefixLift 226823
  have htrace : WordTrace (prefixWord ++ tailWord_226823) baseStart_226823 baseEnd_226823 := by
    simpa [prefixWord, tailWord_226823, baseEnd_226823] using wordTrace_append hprefix tailTrace_226823
  have hstable : (prefixWord ++ tailWord_226823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226823).length < 2 ^ (prefixWord ++ tailWord_226823).sum := by decide
  have hdescent : baseEnd_226823 < baseStart_226823 := by decide
  rcases family_descends (prefixWord ++ tailWord_226823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226902 : List Nat := [5, 2, 2, 2, 2, 1, 1, 6]
def baseStart_226902 : Nat := 118140960795 + 226902 * 2 ^ 59
def prefixEnd_226902 : Nat := 4983230072969 + 3 ^ 40 * 226902 * 2
def baseEnd_226902 : Nat := 17260709254307626456519

theorem tailTrace_226902 : CollatzResearch.WordTrace tailWord_226902 prefixEnd_226902 17260709254307626456519 := by
  unfold tailWord_226902
  simp only [CollatzResearch.WordTrace]
  refine ⟨517237238998767538845185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5517197215986853747681973 517237238998767538845185)
  ·
    refine ⟨387927929249075654133889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 517237238998767538845185 387927929249075654133889)
    ·
      refine ⟨290945946936806740600417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387927929249075654133889 290945946936806740600417)
      ·
        refine ⟨218209460202605055450313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290945946936806740600417 218209460202605055450313)
        ·
          refine ⟨163657095151953791587735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218209460202605055450313 163657095151953791587735)
          ·
            refine ⟨245485642727930687381603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163657095151953791587735 245485642727930687381603)
            ·
              refine ⟨368228464091896031072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245485642727930687381603 368228464091896031072405)
              ·
                refine ⟨17260709254307626456519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368228464091896031072405 17260709254307626456519)
                ·
                  rfl

theorem cell21_226902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_226902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226902 prefixEnd_226902 := by exact prefixLift 226902
  have htrace : WordTrace (prefixWord ++ tailWord_226902) baseStart_226902 baseEnd_226902 := by
    simpa [prefixWord, tailWord_226902, baseEnd_226902] using wordTrace_append hprefix tailTrace_226902
  have hstable : (prefixWord ++ tailWord_226902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226902).length < 2 ^ (prefixWord ++ tailWord_226902).sum := by decide
  have hdescent : baseEnd_226902 < baseStart_226902 := by decide
  rcases family_descends (prefixWord ++ tailWord_226902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226958 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_226958 : Nat := 118140960795 + 226958 * 2 ^ 59
def prefixEnd_226958 : Nat := 4983230072969 + 3 ^ 40 * 226958 * 2
def baseEnd_226958 : Nat := 51794907725879226436109

theorem tailTrace_226958 : CollatzResearch.WordTrace tailWord_226958 prefixEnd_226958 51794907725879226436109 := by
  unfold tailWord_226958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034729788972175273195191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5518558874518268123707685 1034729788972175273195191)
  ·
    refine ⟨1552094683458262909792787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034729788972175273195191 1552094683458262909792787)
    ·
      refine ⟨2328142025187394364689181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552094683458262909792787 2328142025187394364689181)
      ·
        refine ⟨873053259445272886758443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2328142025187394364689181 873053259445272886758443)
        ·
          refine ⟨1309579889167909330137665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873053259445272886758443 1309579889167909330137665)
          ·
            refine ⟨982184916875931997603249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309579889167909330137665 982184916875931997603249)
            ·
              refine ⟨736638687656948998202437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982184916875931997603249 736638687656948998202437)
              ·
                refine ⟨138119753935677937162957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736638687656948998202437 138119753935677937162957)
                ·
                  refine ⟨51794907725879226436109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138119753935677937162957 51794907725879226436109)
                  ·
                    rfl

theorem cell21_226958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_226958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_226958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_226958 prefixEnd_226958 := by exact prefixLift 226958
  have htrace : WordTrace (prefixWord ++ tailWord_226958) baseStart_226958 baseEnd_226958 := by
    simpa [prefixWord, tailWord_226958, baseEnd_226958] using wordTrace_append hprefix tailTrace_226958
  have hstable : (prefixWord ++ tailWord_226958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226958).length < 2 ^ (prefixWord ++ tailWord_226958).sum := by decide
  have hdescent : baseEnd_226958 < baseStart_226958 := by decide
  rcases family_descends (prefixWord ++ tailWord_226958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227031 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_227031 : Nat := 118140960795 + 227031 * 2 ^ 59
def prefixEnd_227031 : Nat := 4983230072969 + 3 ^ 40 * 227031 * 2
def baseEnd_227031 : Nat := 51811567320447321719293

theorem tailTrace_227031 : CollatzResearch.WordTrace tailWord_227031 prefixEnd_227031 51811567320447321719293 := by
  unfold tailWord_227031
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280500840512935652968947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520333893675290435312631 8280500840512935652968947)
  ·
    refine ⟨12420751260769403479453421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280500840512935652968947 12420751260769403479453421)
    ·
      refine ⟨4657781722788526304795033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12420751260769403479453421 4657781722788526304795033)
      ·
        refine ⟨3493336292091394728596275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4657781722788526304795033 3493336292091394728596275)
        ·
          refine ⟨5240004438137092092894413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493336292091394728596275 5240004438137092092894413)
          ·
            refine ⟨1965001664301409534835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5240004438137092092894413 1965001664301409534835405)
            ·
              refine ⟨736875624113028575563277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1965001664301409534835405 736875624113028575563277)
              ·
                refine ⟨276328359042385715836229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736875624113028575563277 276328359042385715836229)
                ·
                  refine ⟨51811567320447321719293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276328359042385715836229 51811567320447321719293)
                  ·
                    rfl

theorem cell21_227031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_227031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227031 prefixEnd_227031 := by exact prefixLift 227031
  have htrace : WordTrace (prefixWord ++ tailWord_227031) baseStart_227031 baseEnd_227031 := by
    simpa [prefixWord, tailWord_227031, baseEnd_227031] using wordTrace_append hprefix tailTrace_227031
  have hstable : (prefixWord ++ tailWord_227031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227031).length < 2 ^ (prefixWord ++ tailWord_227031).sum := by decide
  have hdescent : baseEnd_227031 < baseStart_227031 := by decide
  rcases family_descends (prefixWord ++ tailWord_227031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227045 : List Nat := [1, 3, 1, 4, 1, 1, 1, 9]
def baseStart_227045 : Nat := 118140960795 + 227045 * 2 ^ 59
def prefixEnd_227045 : Nat := 4983230072969 + 3 ^ 40 * 227045 * 2
def baseEnd_227045 : Nat := 17271587437062136161977

theorem tailTrace_227045 : CollatzResearch.WordTrace tailWord_227045 prefixEnd_227045 17271587437062136161977 := by
  unfold tailWord_227045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281011462462216043978589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520674308308144029319059 8281011462462216043978589)
  ·
    refine ⟨3105379298423331016491971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8281011462462216043978589 3105379298423331016491971)
    ·
      refine ⟨4658068947634996524737957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105379298423331016491971 4658068947634996524737957)
      ·
        refine ⟨873387927681561848388367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4658068947634996524737957 873387927681561848388367)
        ·
          refine ⟨1310081891522342772582551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873387927681561848388367 1310081891522342772582551)
          ·
            refine ⟨1965122837283514158873827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310081891522342772582551 1965122837283514158873827)
            ·
              refine ⟨2947684255925271238310741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965122837283514158873827 2947684255925271238310741)
              ·
                refine ⟨17271587437062136161977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2947684255925271238310741 17271587437062136161977)
                ·
                  rfl

theorem cell21_227045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_227045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227045 prefixEnd_227045 := by exact prefixLift 227045
  have htrace : WordTrace (prefixWord ++ tailWord_227045) baseStart_227045 baseEnd_227045 := by
    simpa [prefixWord, tailWord_227045, baseEnd_227045] using wordTrace_append hprefix tailTrace_227045
  have hstable : (prefixWord ++ tailWord_227045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227045).length < 2 ^ (prefixWord ++ tailWord_227045).sum := by decide
  have hdescent : baseEnd_227045 < baseStart_227045 := by decide
  rcases family_descends (prefixWord ++ tailWord_227045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227079 : List Nat := [1, 1, 4, 4, 2, 2, 1, 6]
def baseStart_227079 : Nat := 118140960795 + 227079 * 2 ^ 59
def prefixEnd_227079 : Nat := 4983230072969 + 3 ^ 40 * 227079 * 2
def baseEnd_227079 : Nat := 17274173858136634973065

theorem tailTrace_227079 : CollatzResearch.WordTrace tailWord_227079 prefixEnd_227079 17274173858136634973065 := by
  unfold tailWord_227079
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282251544339039850716291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5521501029559359900477527 8282251544339039850716291)
  ·
    refine ⟨12423377316508559776074437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282251544339039850716291 12423377316508559776074437)
    ·
      refine ⟨2329383246845354958013957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12423377316508559776074437 2329383246845354958013957)
      ·
        refine ⟨436759358783504054627617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2329383246845354958013957 436759358783504054627617)
        ·
          refine ⟨327569519087628040970713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436759358783504054627617 327569519087628040970713)
          ·
            refine ⟨245677139315721030728035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327569519087628040970713 245677139315721030728035)
            ·
              refine ⟨368515708973581546092053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245677139315721030728035 368515708973581546092053)
              ·
                refine ⟨17274173858136634973065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368515708973581546092053 17274173858136634973065)
                ·
                  rfl

theorem cell21_227079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_227079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227079 prefixEnd_227079 := by exact prefixLift 227079
  have htrace : WordTrace (prefixWord ++ tailWord_227079) baseStart_227079 baseEnd_227079 := by
    simpa [prefixWord, tailWord_227079, baseEnd_227079] using wordTrace_append hprefix tailTrace_227079
  have hstable : (prefixWord ++ tailWord_227079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227079).length < 2 ^ (prefixWord ++ tailWord_227079).sum := by decide
  have hdescent : baseEnd_227079 < baseStart_227079 := by decide
  rcases family_descends (prefixWord ++ tailWord_227079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227121 : List Nat := [1, 2, 2, 3, 2, 3, 8]
def baseStart_227121 : Nat := 118140960795 + 227121 * 2 ^ 59
def prefixEnd_227121 : Nat := 4983230072969 + 3 ^ 40 * 227121 * 2
def baseEnd_227121 : Nat := 5759122949625240579901

theorem tailTrace_227121 : CollatzResearch.WordTrace tailWord_227121 prefixEnd_227121 5759122949625240579901 := by
  unfold tailWord_227121
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283783410186881023745217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5522522273457920682496811 8283783410186881023745217)
  ·
    refine ⟨6212837557640160767808913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8283783410186881023745217 6212837557640160767808913)
    ·
      refine ⟨4659628168230120575856685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6212837557640160767808913 4659628168230120575856685)
      ·
        refine ⟨1747360563086295215946257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4659628168230120575856685 1747360563086295215946257)
        ·
          refine ⟨1310520422314721411959693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747360563086295215946257 1310520422314721411959693)
          ·
            refine ⟨491445158368020529484885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1310520422314721411959693 491445158368020529484885)
            ·
              refine ⟨5759122949625240579901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 491445158368020529484885 5759122949625240579901)
              ·
                rfl

theorem cell21_227121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 8].length) (baseStart_227121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227121 prefixEnd_227121 := by exact prefixLift 227121
  have htrace : WordTrace (prefixWord ++ tailWord_227121) baseStart_227121 baseEnd_227121 := by
    simpa [prefixWord, tailWord_227121, baseEnd_227121] using wordTrace_append hprefix tailTrace_227121
  have hstable : (prefixWord ++ tailWord_227121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227121).length < 2 ^ (prefixWord ++ tailWord_227121).sum := by decide
  have hdescent : baseEnd_227121 < baseStart_227121 := by decide
  rcases family_descends (prefixWord ++ tailWord_227121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227124 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_227124 : Nat := 118140960795 + 227124 * 2 ^ 59
def prefixEnd_227124 : Nat := 4983230072969 + 3 ^ 40 * 227124 * 2
def baseEnd_227124 : Nat := 51832791187499826669103

theorem tailTrace_227124 : CollatzResearch.WordTrace tailWord_227124 prefixEnd_227124 51832791187499826669103 := by
  unfold tailWord_227124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141946414588006268052213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5522595219450675024069617 4141946414588006268052213)
  ·
    refine ⟨388307476367625587629895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4141946414588006268052213 388307476367625587629895)
    ·
      refine ⟨582461214551438381444843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388307476367625587629895 582461214551438381444843)
      ·
        refine ⟨873691821827157572167265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582461214551438381444843 873691821827157572167265)
        ·
          refine ⟨655268866370368179125449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873691821827157572167265 655268866370368179125449)
          ·
            refine ⟨491451649777776134344087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655268866370368179125449 491451649777776134344087)
            ·
              refine ⟨737177474666664201516131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491451649777776134344087 737177474666664201516131)
              ·
                refine ⟨1105766211999996302274197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737177474666664201516131 1105766211999996302274197)
                ·
                  refine ⟨51832791187499826669103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1105766211999996302274197 51832791187499826669103)
                  ·
                    rfl

theorem cell21_227124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_227124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227124 prefixEnd_227124 := by exact prefixLift 227124
  have htrace : WordTrace (prefixWord ++ tailWord_227124) baseStart_227124 baseEnd_227124 := by
    simpa [prefixWord, tailWord_227124, baseEnd_227124] using wordTrace_append hprefix tailTrace_227124
  have hstable : (prefixWord ++ tailWord_227124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227124).length < 2 ^ (prefixWord ++ tailWord_227124).sum := by decide
  have hdescent : baseEnd_227124 < baseStart_227124 := by decide
  rcases family_descends (prefixWord ++ tailWord_227124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227211 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_227211 : Nat := 118140960795 + 227211 * 2 ^ 59
def prefixEnd_227211 : Nat := 4983230072969 + 3 ^ 40 * 227211 * 2
def baseEnd_227211 : Nat := 51852645772807008718925

theorem tailTrace_227211 : CollatzResearch.WordTrace tailWord_227211 prefixEnd_227211 51852645772807008718925 := by
  unfold tailWord_227211
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287065979860826394521487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5524710653240550929680991 8287065979860826394521487)
  ·
    refine ⟨12430598969791239591782231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287065979860826394521487 12430598969791239591782231)
    ·
      refine ⟨18645898454686859387673347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430598969791239591782231 18645898454686859387673347)
      ·
        refine ⟨27968847682030289081510021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645898454686859387673347 27968847682030289081510021)
        ·
          refine ⟨5244158940380679202783129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27968847682030289081510021 5244158940380679202783129)
          ·
            refine ⟨3933119205285509402087347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244158940380679202783129 3933119205285509402087347)
            ·
              refine ⟨5899678807928264103131021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933119205285509402087347 5899678807928264103131021)
              ·
                refine ⟨2212379552973099038674133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899678807928264103131021 2212379552973099038674133)
                ·
                  refine ⟨51852645772807008718925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2212379552973099038674133 51852645772807008718925)
                  ·
                    rfl

theorem cell21_227211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_227211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227211 prefixEnd_227211 := by exact prefixLift 227211
  have htrace : WordTrace (prefixWord ++ tailWord_227211) baseStart_227211 baseEnd_227211 := by
    simpa [prefixWord, tailWord_227211, baseEnd_227211] using wordTrace_append hprefix tailTrace_227211
  have hstable : (prefixWord ++ tailWord_227211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227211).length < 2 ^ (prefixWord ++ tailWord_227211).sum := by decide
  have hdescent : baseEnd_227211 < baseStart_227211 := by decide
  rcases family_descends (prefixWord ++ tailWord_227211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227287 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_227287 : Nat := 118140960795 + 227287 * 2 ^ 59
def prefixEnd_227287 : Nat := 4983230072969 + 3 ^ 40 * 227287 * 2
def baseEnd_227287 : Nat := 51869990008247765452103

theorem tailTrace_227287 : CollatzResearch.WordTrace tailWord_227287 prefixEnd_227287 51869990008247765452103 := by
  unfold tailWord_227287
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289837927585491374288115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5526558618390327582858743 8289837927585491374288115)
  ·
    refine ⟨12434756891378237061432173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289837927585491374288115 12434756891378237061432173)
    ·
      refine ⟨4663033834266838898037065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12434756891378237061432173 4663033834266838898037065)
      ·
        refine ⟨3497275375700129173527799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4663033834266838898037065 3497275375700129173527799)
        ·
          refine ⟨5245913063550193760291699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497275375700129173527799 5245913063550193760291699)
          ·
            refine ⟨7868869595325290640437549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245913063550193760291699 7868869595325290640437549)
            ·
              refine ⟨2950826098246983990164081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7868869595325290640437549 2950826098246983990164081)
              ·
                refine ⟨2213119573685237992623061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950826098246983990164081 2213119573685237992623061)
                ·
                  refine ⟨51869990008247765452103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2213119573685237992623061 51869990008247765452103)
                  ·
                    rfl

theorem cell21_227287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_227287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227287 prefixEnd_227287 := by exact prefixLift 227287
  have htrace : WordTrace (prefixWord ++ tailWord_227287) baseStart_227287 baseEnd_227287 := by
    simpa [prefixWord, tailWord_227287, baseEnd_227287] using wordTrace_append hprefix tailTrace_227287
  have hstable : (prefixWord ++ tailWord_227287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227287).length < 2 ^ (prefixWord ++ tailWord_227287).sum := by decide
  have hdescent : baseEnd_227287 < baseStart_227287 := by decide
  rcases family_descends (prefixWord ++ tailWord_227287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227293 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_227293 : Nat := 118140960795 + 227293 * 2 ^ 59
def prefixEnd_227293 : Nat := 4983230072969 + 3 ^ 40 * 227293 * 2
def baseEnd_227293 : Nat := 51871359289993088352091

theorem tailTrace_227293 : CollatzResearch.WordTrace tailWord_227293 prefixEnd_227293 51871359289993088352091 := by
  unfold tailWord_227293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290056765563754399006533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5526704510375836266004355 8290056765563754399006533)
  ·
    refine ⟨1554385643543203949813725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8290056765563754399006533 1554385643543203949813725)
    ·
      refine ⟨582894616328701481180147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1554385643543203949813725 582894616328701481180147)
      ·
        refine ⟨874341924493052221770221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582894616328701481180147 874341924493052221770221)
        ·
          refine ⟨327878221684894583163833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874341924493052221770221 327878221684894583163833)
          ·
            refine ⟨245908666263670937372875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327878221684894583163833 245908666263670937372875)
            ·
              refine ⟨368862999395506406059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245908666263670937372875 368862999395506406059313)
              ·
                refine ⟨276647249546629804544485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368862999395506406059313 276647249546629804544485)
                ·
                  refine ⟨51871359289993088352091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276647249546629804544485 51871359289993088352091)
                  ·
                    rfl

theorem cell21_227293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_227293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227293 prefixEnd_227293 := by exact prefixLift 227293
  have htrace : WordTrace (prefixWord ++ tailWord_227293) baseStart_227293 baseEnd_227293 := by
    simpa [prefixWord, tailWord_227293, baseEnd_227293] using wordTrace_append hprefix tailTrace_227293
  have hstable : (prefixWord ++ tailWord_227293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227293).length < 2 ^ (prefixWord ++ tailWord_227293).sum := by decide
  have hdescent : baseEnd_227293 < baseStart_227293 := by decide
  rcases family_descends (prefixWord ++ tailWord_227293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227341 : List Nat := [1, 7, 1, 2, 2, 1, 7]
def baseStart_227341 : Nat := 118140960795 + 227341 * 2 ^ 59
def prefixEnd_227341 : Nat := 4983230072969 + 3 ^ 40 * 227341 * 2
def baseEnd_227341 : Nat := 5764701504883963505777

theorem tailTrace_227341 : CollatzResearch.WordTrace tailWord_227341 prefixEnd_227341 5764701504883963505777 := by
  unfold tailWord_227341
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291807469389858596753877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5527871646259905731169251 8291807469389858596753877)
  ·
    refine ⟨194339237563824810861419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8291807469389858596753877 194339237563824810861419)
    ·
      refine ⟨291508856345737216292129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194339237563824810861419 291508856345737216292129)
      ·
        refine ⟨218631642259302912219097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291508856345737216292129 218631642259302912219097)
        ·
          refine ⟨163973731694477184164323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218631642259302912219097 163973731694477184164323)
          ·
            refine ⟨245960597541715776246485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163973731694477184164323 245960597541715776246485)
            ·
              refine ⟨5764701504883963505777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245960597541715776246485 5764701504883963505777)
              ·
                rfl

theorem cell21_227341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 7].length) (baseStart_227341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227341 prefixEnd_227341 := by exact prefixLift 227341
  have htrace : WordTrace (prefixWord ++ tailWord_227341) baseStart_227341 baseEnd_227341 := by
    simpa [prefixWord, tailWord_227341, baseEnd_227341] using wordTrace_append hprefix tailTrace_227341
  have hstable : (prefixWord ++ tailWord_227341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227341).length < 2 ^ (prefixWord ++ tailWord_227341).sum := by decide
  have hdescent : baseEnd_227341 < baseStart_227341 := by decide
  rcases family_descends (prefixWord ++ tailWord_227341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227439 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_227439 : Nat := 118140960795 + 227439 * 2 ^ 59
def prefixEnd_227439 : Nat := 4983230072969 + 3 ^ 40 * 227439 * 2
def baseEnd_227439 : Nat := 51904678479129278918459

theorem tailTrace_227439 : CollatzResearch.WordTrace tailWord_227439 prefixEnd_227439 51904678479129278918459 := by
  unfold tailWord_227439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295381823034821333821371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5530254548689880889214247 8295381823034821333821371)
  ·
    refine ⟨12443072734552232000732057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295381823034821333821371 12443072734552232000732057)
    ·
      refine ⟨9332304550914174000549043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12443072734552232000732057 9332304550914174000549043)
      ·
        refine ⟨13998456826371261000823565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332304550914174000549043 13998456826371261000823565)
        ·
          refine ⟨5249421309889222875308837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13998456826371261000823565 5249421309889222875308837)
          ·
            refine ⟨984266495604229289120407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5249421309889222875308837 984266495604229289120407)
            ·
              refine ⟨1476399743406343933680611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984266495604229289120407 1476399743406343933680611)
              ·
                refine ⟨2214599615109515900520917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476399743406343933680611 2214599615109515900520917)
                ·
                  refine ⟨51904678479129278918459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2214599615109515900520917 51904678479129278918459)
                  ·
                    rfl

theorem cell21_227439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_227439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227439 prefixEnd_227439 := by exact prefixLift 227439
  have htrace : WordTrace (prefixWord ++ tailWord_227439) baseStart_227439 baseEnd_227439 := by
    simpa [prefixWord, tailWord_227439, baseEnd_227439] using wordTrace_append hprefix tailTrace_227439
  have hstable : (prefixWord ++ tailWord_227439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227439).length < 2 ^ (prefixWord ++ tailWord_227439).sum := by decide
  have hdescent : baseEnd_227439 < baseStart_227439 := by decide
  rcases family_descends (prefixWord ++ tailWord_227439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227442 : List Nat := [3, 2, 1, 2, 2, 3, 3, 5]
def baseStart_227442 : Nat := 118140960795 + 227442 * 2 ^ 59
def prefixEnd_227442 : Nat := 4983230072969 + 3 ^ 40 * 227442 * 2
def baseEnd_227442 : Nat := 17301787706667313456151

theorem tailTrace_227442 : CollatzResearch.WordTrace tailWord_227442 prefixEnd_227442 17301787706667313456151 := by
  unfold tailWord_227442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073872810505988211545145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5530327494682635230787053 2073872810505988211545145)
  ·
    refine ⟨1555404607879491158658859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2073872810505988211545145 1555404607879491158658859)
    ·
      refine ⟨2333106911819236737988289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555404607879491158658859 2333106911819236737988289)
      ·
        refine ⟨1749830183864427553491217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333106911819236737988289 1749830183864427553491217)
        ·
          refine ⟨1312372637898320665118413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749830183864427553491217 1312372637898320665118413)
          ·
            refine ⟨492139739211870249419405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312372637898320665118413 492139739211870249419405)
            ·
              refine ⟨184552402204451343532277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492139739211870249419405 184552402204451343532277)
              ·
                refine ⟨17301787706667313456151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184552402204451343532277 17301787706667313456151)
                ·
                  rfl

theorem cell21_227442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_227442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227442 prefixEnd_227442 := by exact prefixLift 227442
  have htrace : WordTrace (prefixWord ++ tailWord_227442) baseStart_227442 baseEnd_227442 := by
    simpa [prefixWord, tailWord_227442, baseEnd_227442] using wordTrace_append hprefix tailTrace_227442
  have hstable : (prefixWord ++ tailWord_227442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227442).length < 2 ^ (prefixWord ++ tailWord_227442).sum := by decide
  have hdescent : baseEnd_227442 < baseStart_227442 := by decide
  rcases family_descends (prefixWord ++ tailWord_227442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227518 : List Nat := [4, 2, 1, 1, 4, 2, 7]
def baseStart_227518 : Nat := 118140960795 + 227518 * 2 ^ 59
def prefixEnd_227518 : Nat := 4983230072969 + 3 ^ 40 * 227518 * 2
def baseEnd_227518 : Nat := 5769189706160299677959

theorem tailTrace_227518 : CollatzResearch.WordTrace tailWord_227518 prefixEnd_227518 5769189706160299677959 := by
  unfold tailWord_227518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037282898718577228243401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5532175459832411883964805 1037282898718577228243401)
  ·
    refine ⟨777962174038932921182551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037282898718577228243401 777962174038932921182551)
    ·
      refine ⟨1166943261058399381773827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777962174038932921182551 1166943261058399381773827)
      ·
        refine ⟨1750414891587599072660741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166943261058399381773827 1750414891587599072660741)
        ·
          refine ⟨328202792172674826123889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1750414891587599072660741 328202792172674826123889)
          ·
            refine ⟨246152094129506119592917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328202792172674826123889 246152094129506119592917)
            ·
              refine ⟨5769189706160299677959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 246152094129506119592917 5769189706160299677959)
              ·
                rfl

theorem cell21_227518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 7].length) (baseStart_227518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227518 prefixEnd_227518 := by exact prefixLift 227518
  have htrace : WordTrace (prefixWord ++ tailWord_227518) baseStart_227518 baseEnd_227518 := by
    simpa [prefixWord, tailWord_227518, baseEnd_227518] using wordTrace_append hprefix tailTrace_227518
  have hstable : (prefixWord ++ tailWord_227518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227518).length < 2 ^ (prefixWord ++ tailWord_227518).sum := by decide
  have hdescent : baseEnd_227518 < baseStart_227518 := by decide
  rcases family_descends (prefixWord ++ tailWord_227518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227676 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_227676 : Nat := 118140960795 + 227676 * 2 ^ 59
def prefixEnd_227676 : Nat := 4983230072969 + 3 ^ 40 * 227676 * 2
def baseEnd_227676 : Nat := 51958765108069533467975

theorem tailTrace_227676 : CollatzResearch.WordTrace tailWord_227676 prefixEnd_227676 51958765108069533467975 := by
  unfold tailWord_227676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152012961588105405099441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5536017282117473873465921 4152012961588105405099441)
  ·
    refine ⟨3114009721191079053824581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4152012961588105405099441 3114009721191079053824581)
    ·
      refine ⟨583876822723327322592109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3114009721191079053824581 583876822723327322592109)
      ·
        refine ⟨218953808521247745972041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583876822723327322592109 218953808521247745972041)
        ·
          refine ⟨164215356390935809479031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218953808521247745972041 164215356390935809479031)
          ·
            refine ⟨246323034586403714218547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164215356390935809479031 246323034586403714218547)
            ·
              refine ⟨369484551879605571327821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246323034586403714218547 369484551879605571327821)
              ·
                refine ⟨138556706954852089247933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369484551879605571327821 138556706954852089247933)
                ·
                  refine ⟨51958765108069533467975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138556706954852089247933 51958765108069533467975)
                  ·
                    rfl

theorem cell21_227676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_227676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227676 prefixEnd_227676 := by exact prefixLift 227676
  have htrace : WordTrace (prefixWord ++ tailWord_227676) baseStart_227676 baseEnd_227676 := by
    simpa [prefixWord, tailWord_227676, baseEnd_227676] using wordTrace_append hprefix tailTrace_227676
  have hstable : (prefixWord ++ tailWord_227676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227676).length < 2 ^ (prefixWord ++ tailWord_227676).sum := by decide
  have hdescent : baseEnd_227676 < baseStart_227676 := by decide
  rcases family_descends (prefixWord ++ tailWord_227676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227698 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_227698 : Nat := 118140960795 + 227698 * 2 ^ 59
def prefixEnd_227698 : Nat := 4983230072969 + 3 ^ 40 * 227698 * 2
def baseEnd_227698 : Nat := 51963785807802384101263

theorem tailTrace_227698 : CollatzResearch.WordTrace tailWord_227698 prefixEnd_227698 51963785807802384101263 := by
  unfold tailWord_227698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076207082274127141874937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5536552219397672378333165 2076207082274127141874937)
  ·
    refine ⟨1557155311705595356406203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2076207082274127141874937 1557155311705595356406203)
    ·
      refine ⟨2335732967558393034609305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1557155311705595356406203 2335732967558393034609305)
      ·
        refine ⟨1751799725668794775956979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335732967558393034609305 1751799725668794775956979)
        ·
          refine ⟨2627699588503192163935469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751799725668794775956979 2627699588503192163935469)
          ·
            refine ⟨985387345688697061475801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2627699588503192163935469 985387345688697061475801)
            ·
              refine ⟨739040509266522796106851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985387345688697061475801 739040509266522796106851)
              ·
                refine ⟨1108560763899784194160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739040509266522796106851 1108560763899784194160277)
                ·
                  refine ⟨51963785807802384101263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1108560763899784194160277 51963785807802384101263)
                  ·
                    rfl

theorem cell21_227698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_227698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227698 prefixEnd_227698 := by exact prefixLift 227698
  have htrace : WordTrace (prefixWord ++ tailWord_227698) baseStart_227698 baseEnd_227698 := by
    simpa [prefixWord, tailWord_227698, baseEnd_227698] using wordTrace_append hprefix tailTrace_227698
  have hstable : (prefixWord ++ tailWord_227698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227698).length < 2 ^ (prefixWord ++ tailWord_227698).sum := by decide
  have hdescent : baseEnd_227698 < baseStart_227698 := by decide
  rcases family_descends (prefixWord ++ tailWord_227698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227701 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_227701 : Nat := 118140960795 + 227701 * 2 ^ 59
def prefixEnd_227701 : Nat := 4983230072969 + 3 ^ 40 * 227701 * 2
def baseEnd_227701 : Nat := 51964470448675045551257

theorem tailTrace_227701 : CollatzResearch.WordTrace tailWord_227701 prefixEnd_227701 51964470448675045551257 := by
  unfold tailWord_227701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304937748085640079858957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5536625165390426719905971 8304937748085640079858957)
  ·
    refine ⟨3114351655532115029947109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8304937748085640079858957 3114351655532115029947109)
    ·
      refine ⟨583940935412271568115083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3114351655532115029947109 583940935412271568115083)
      ·
        refine ⟨875911403118407352172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583940935412271568115083 875911403118407352172625)
        ·
          refine ⟨656933552338805514129469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875911403118407352172625 656933552338805514129469)
          ·
            refine ⟨246350082127052067798551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656933552338805514129469 246350082127052067798551)
            ·
              refine ⟨369525123190578101697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246350082127052067798551 369525123190578101697827)
              ·
                refine ⟨554287684785867152546741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369525123190578101697827 554287684785867152546741)
                ·
                  refine ⟨51964470448675045551257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554287684785867152546741 51964470448675045551257)
                  ·
                    rfl

theorem cell21_227701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_227701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227701 prefixEnd_227701 := by exact prefixLift 227701
  have htrace : WordTrace (prefixWord ++ tailWord_227701) baseStart_227701 baseEnd_227701 := by
    simpa [prefixWord, tailWord_227701, baseEnd_227701] using wordTrace_append hprefix tailTrace_227701
  have hstable : (prefixWord ++ tailWord_227701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227701).length < 2 ^ (prefixWord ++ tailWord_227701).sum := by decide
  have hdescent : baseEnd_227701 < baseStart_227701 := by decide
  rcases family_descends (prefixWord ++ tailWord_227701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227715 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_227715 : Nat := 118140960795 + 227715 * 2 ^ 59
def prefixEnd_227715 : Nat := 4983230072969 + 3 ^ 40 * 227715 * 2
def baseEnd_227715 : Nat := 51967665439414132317895

theorem tailTrace_227715 : CollatzResearch.WordTrace tailWord_227715 prefixEnd_227715 51967665439414132317895 := by
  unfold tailWord_227715
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305448370034920470868599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5536965580023280313912399 8305448370034920470868599)
  ·
    refine ⟨12458172555052380706302899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305448370034920470868599 12458172555052380706302899)
    ·
      refine ⟨18687258832578571059454349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458172555052380706302899 18687258832578571059454349)
      ·
        refine ⟨7007722062216964147295381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18687258832578571059454349 7007722062216964147295381)
        ·
          refine ⟨328486971666420194404471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7007722062216964147295381 328486971666420194404471)
          ·
            refine ⟨492730457499630291606707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328486971666420194404471 492730457499630291606707)
            ·
              refine ⟨739095686249445437410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492730457499630291606707 739095686249445437410061)
              ·
                refine ⟨277160882343542039028773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739095686249445437410061 277160882343542039028773)
                ·
                  refine ⟨51967665439414132317895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277160882343542039028773 51967665439414132317895)
                  ·
                    rfl

theorem cell21_227715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_227715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227715 prefixEnd_227715 := by exact prefixLift 227715
  have htrace : WordTrace (prefixWord ++ tailWord_227715) baseStart_227715 baseEnd_227715 := by
    simpa [prefixWord, tailWord_227715, baseEnd_227715] using wordTrace_append hprefix tailTrace_227715
  have hstable : (prefixWord ++ tailWord_227715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227715).length < 2 ^ (prefixWord ++ tailWord_227715).sum := by decide
  have hdescent : baseEnd_227715 < baseStart_227715 := by decide
  rcases family_descends (prefixWord ++ tailWord_227715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227819 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_227819 : Nat := 118140960795 + 227819 * 2 ^ 59
def prefixEnd_227819 : Nat := 4983230072969 + 3 ^ 40 * 227819 * 2
def baseEnd_227819 : Nat := 51991399656333062584349

theorem tailTrace_227819 : CollatzResearch.WordTrace tailWord_227819 prefixEnd_227819 51991399656333062584349 := by
  unfold tailWord_227819
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309241561658146232654511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5539494374438764155103007 8309241561658146232654511)
  ·
    refine ⟨12463862342487219348981767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309241561658146232654511 12463862342487219348981767)
    ·
      refine ⟨18695793513730829023472651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12463862342487219348981767 18695793513730829023472651)
      ·
        refine ⟨28043690270596243535208977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18695793513730829023472651 28043690270596243535208977)
        ·
          refine ⟨21032767702947182651406733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28043690270596243535208977 21032767702947182651406733)
          ·
            refine ⟨7887287888605193494277525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21032767702947182651406733 7887287888605193494277525)
            ·
              refine ⟨369716619778368445044259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7887287888605193494277525 369716619778368445044259)
              ·
                refine ⟨554574929667552667566389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369716619778368445044259 554574929667552667566389)
                ·
                  refine ⟨51991399656333062584349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554574929667552667566389 51991399656333062584349)
                  ·
                    rfl

theorem cell21_227819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_227819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227819 prefixEnd_227819 := by exact prefixLift 227819
  have htrace : WordTrace (prefixWord ++ tailWord_227819) baseStart_227819 baseEnd_227819 := by
    simpa [prefixWord, tailWord_227819, baseEnd_227819] using wordTrace_append hprefix tailTrace_227819
  have hstable : (prefixWord ++ tailWord_227819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227819).length < 2 ^ (prefixWord ++ tailWord_227819).sum := by decide
  have hdescent : baseEnd_227819 < baseStart_227819 := by decide
  rcases family_descends (prefixWord ++ tailWord_227819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227864 : List Nat := [2, 1, 2, 3, 3, 1, 9]
def baseStart_227864 : Nat := 118140960795 + 227864 * 2 ^ 59
def prefixEnd_227864 : Nat := 4983230072969 + 3 ^ 40 * 227864 * 2
def baseEnd_227864 : Nat := 5777963252158109370473

theorem tailTrace_227864 : CollatzResearch.WordTrace tailWord_227864 prefixEnd_227864 5777963252158109370473 := by
  unfold tailWord_227864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155441423247559459021323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5540588564330079278695097 4155441423247559459021323)
  ·
    refine ⟨6233162134871339188531985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155441423247559459021323 6233162134871339188531985)
    ·
      refine ⟨4674871601153504391398989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6233162134871339188531985 4674871601153504391398989)
      ·
        refine ⟨1753076850432564146774621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4674871601153504391398989 1753076850432564146774621)
        ·
          refine ⟨657403818912211555040483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1753076850432564146774621 657403818912211555040483)
          ·
            refine ⟨986105728368317332560725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657403818912211555040483 986105728368317332560725)
            ·
              refine ⟨5777963252158109370473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 986105728368317332560725 5777963252158109370473)
              ·
                rfl

theorem cell21_227864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 9].length) (baseStart_227864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227864 prefixEnd_227864 := by exact prefixLift 227864
  have htrace : WordTrace (prefixWord ++ tailWord_227864) baseStart_227864 baseEnd_227864 := by
    simpa [prefixWord, tailWord_227864, baseEnd_227864] using wordTrace_append hprefix tailTrace_227864
  have hstable : (prefixWord ++ tailWord_227864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227864).length < 2 ^ (prefixWord ++ tailWord_227864).sum := by decide
  have hdescent : baseEnd_227864 < baseStart_227864 := by decide
  rcases family_descends (prefixWord ++ tailWord_227864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227988 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_227988 : Nat := 118140960795 + 227988 * 2 ^ 59
def prefixEnd_227988 : Nat := 4983230072969 + 3 ^ 40 * 227988 * 2
def baseEnd_227988 : Nat := 52029967758826324267337

theorem tailTrace_227988 : CollatzResearch.WordTrace tailWord_227988 prefixEnd_227988 52029967758826324267337 := by
  unfold tailWord_227988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157702749022944047778309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5543603665363925397037745 4157702749022944047778309)
  ·
    refine ⟨779569265441802008958433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4157702749022944047778309 779569265441802008958433)
    ·
      refine ⟨584676949081351506718825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 779569265441802008958433 584676949081351506718825)
      ·
        refine ⟨438507711811013630039119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584676949081351506718825 438507711811013630039119)
        ·
          refine ⟨657761567716520445058679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438507711811013630039119 657761567716520445058679)
          ·
            refine ⟨986642351574780667588019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657761567716520445058679 986642351574780667588019)
            ·
              refine ⟨1479963527362171001382029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986642351574780667588019 1479963527362171001382029)
              ·
                refine ⟨554986322760814125518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479963527362171001382029 554986322760814125518261)
                ·
                  refine ⟨52029967758826324267337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554986322760814125518261 52029967758826324267337)
                  ·
                    rfl

theorem cell21_227988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_227988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_227988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_227988 prefixEnd_227988 := by exact prefixLift 227988
  have htrace : WordTrace (prefixWord ++ tailWord_227988) baseStart_227988 baseEnd_227988 := by
    simpa [prefixWord, tailWord_227988, baseEnd_227988] using wordTrace_append hprefix tailTrace_227988
  have hstable : (prefixWord ++ tailWord_227988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227988).length < 2 ^ (prefixWord ++ tailWord_227988).sum := by decide
  have hdescent : baseEnd_227988 < baseStart_227988 := by decide
  rcases family_descends (prefixWord ++ tailWord_227988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228053 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 4]
def baseStart_228053 : Nat := 118140960795 + 228053 * 2 ^ 59
def prefixEnd_228053 : Nat := 4983230072969 + 3 ^ 40 * 228053 * 2
def baseEnd_228053 : Nat := 52044801644400655683871

theorem tailTrace_228053 : CollatzResearch.WordTrace tailWord_228053 prefixEnd_228053 52044801644400655683871 := by
  unfold tailWord_228053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317776242810404196672813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5545184161873602797781875 8317776242810404196672813)
  ·
    refine ⟨3119166091053901573752305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8317776242810404196672813 3119166091053901573752305)
    ·
      refine ⟨2339374568290426180314229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119166091053901573752305 2339374568290426180314229)
      ·
        refine ⟨219316365777227454404459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2339374568290426180314229 219316365777227454404459)
        ·
          refine ⟨328974548665841181606689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219316365777227454404459 328974548665841181606689)
          ·
            refine ⟨246730911499380886205017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328974548665841181606689 246730911499380886205017)
            ·
              refine ⟨185048183624535664653763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246730911499380886205017 185048183624535664653763)
              ·
                refine ⟨277572275436803496980645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185048183624535664653763 277572275436803496980645)
                ·
                  refine ⟨52044801644400655683871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277572275436803496980645 52044801644400655683871)
                  ·
                    rfl

theorem cell21_228053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_228053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228053 prefixEnd_228053 := by exact prefixLift 228053
  have htrace : WordTrace (prefixWord ++ tailWord_228053) baseStart_228053 baseEnd_228053 := by
    simpa [prefixWord, tailWord_228053, baseEnd_228053] using wordTrace_append hprefix tailTrace_228053
  have hstable : (prefixWord ++ tailWord_228053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228053).length < 2 ^ (prefixWord ++ tailWord_228053).sum := by decide
  have hdescent : baseEnd_228053 < baseStart_228053 := by decide
  rcases family_descends (prefixWord ++ tailWord_228053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228098 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_228098 : Nat := 118140960795 + 228098 * 2 ^ 59
def prefixEnd_228098 : Nat := 4983230072969 + 3 ^ 40 * 228098 * 2
def baseEnd_228098 : Nat := 52055071257490577433779

theorem tailTrace_228098 : CollatzResearch.WordTrace tailWord_228098 prefixEnd_228098 52055071257490577433779 := by
  unfold tailWord_228098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079854381911844220515237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5546278351764917921373965 2079854381911844220515237)
  ·
    refine ⟨389972696608470791346607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2079854381911844220515237 389972696608470791346607)
    ·
      refine ⟨584959044912706187019911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389972696608470791346607 584959044912706187019911)
      ·
        refine ⟨877438567369059280529867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584959044912706187019911 877438567369059280529867)
        ·
          refine ⟨1316157851053588920794801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877438567369059280529867 1316157851053588920794801)
          ·
            refine ⟨987118388290191690596101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316157851053588920794801 987118388290191690596101)
            ·
              refine ⟨185084697804410941986769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 987118388290191690596101 185084697804410941986769)
              ·
                refine ⟨138813523353308206490077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185084697804410941986769 138813523353308206490077)
                ·
                  refine ⟨52055071257490577433779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138813523353308206490077 52055071257490577433779)
                  ·
                    rfl

theorem cell21_228098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_228098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228098 prefixEnd_228098 := by exact prefixLift 228098
  have htrace : WordTrace (prefixWord ++ tailWord_228098) baseStart_228098 baseEnd_228098 := by
    simpa [prefixWord, tailWord_228098, baseEnd_228098] using wordTrace_append hprefix tailTrace_228098
  have hstable : (prefixWord ++ tailWord_228098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228098).length < 2 ^ (prefixWord ++ tailWord_228098).sum := by decide
  have hdescent : baseEnd_228098 < baseStart_228098 := by decide
  rcases family_descends (prefixWord ++ tailWord_228098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228140 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_228140 : Nat := 118140960795 + 228140 * 2 ^ 59
def prefixEnd_228140 : Nat := 4983230072969 + 3 ^ 40 * 228140 * 2
def baseEnd_228140 : Nat := 52064656229707837733693

theorem tailTrace_228140 : CollatzResearch.WordTrace tailWord_228140 prefixEnd_228140 52064656229707837733693 := by
  unfold tailWord_228140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160474696747609027544937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5547299595663478703393249 4160474696747609027544937)
  ·
    refine ⟨3120356022560706770658703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4160474696747609027544937 3120356022560706770658703)
    ·
      refine ⟨4680534033841060155988055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120356022560706770658703 4680534033841060155988055)
      ·
        refine ⟨7020801050761590233982083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680534033841060155988055 7020801050761590233982083)
        ·
          refine ⟨10531201576142385350973125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020801050761590233982083 10531201576142385350973125)
          ·
            refine ⟨1974600295526697253307461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10531201576142385350973125 1974600295526697253307461)
            ·
              refine ⟨370237555411255734995149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1974600295526697253307461 370237555411255734995149)
              ·
                refine ⟨138839083279220900623181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370237555411255734995149 138839083279220900623181)
                ·
                  refine ⟨52064656229707837733693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138839083279220900623181 52064656229707837733693)
                  ·
                    rfl

theorem cell21_228140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_228140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228140 prefixEnd_228140 := by exact prefixLift 228140
  have htrace : WordTrace (prefixWord ++ tailWord_228140) baseStart_228140 baseEnd_228140 := by
    simpa [prefixWord, tailWord_228140, baseEnd_228140] using wordTrace_append hprefix tailTrace_228140
  have hstable : (prefixWord ++ tailWord_228140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228140).length < 2 ^ (prefixWord ++ tailWord_228140).sum := by decide
  have hdescent : baseEnd_228140 < baseStart_228140 := by decide
  rcases family_descends (prefixWord ++ tailWord_228140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228151 : List Nat := [1, 1, 3, 1, 2, 1, 12]
def baseStart_228151 : Nat := 118140960795 + 228151 * 2 ^ 59
def prefixEnd_228151 : Nat := 4983230072969 + 3 ^ 40 * 228151 * 2
def baseEnd_228151 : Nat := 5785240731063807005593

theorem tailTrace_228151 : CollatzResearch.WordTrace tailWord_228151 prefixEnd_228151 5785240731063807005593 := by
  unfold tailWord_228151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321350596455366933740307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5547567064303577955826871 8321350596455366933740307)
  ·
    refine ⟨12482025894683050400610461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321350596455366933740307 12482025894683050400610461)
    ·
      refine ⟨4680759710506143900228923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12482025894683050400610461 4680759710506143900228923)
      ·
        refine ⟨7021139565759215850343385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680759710506143900228923 7021139565759215850343385)
        ·
          refine ⟨5265854674319411887757539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7021139565759215850343385 5265854674319411887757539)
          ·
            refine ⟨7898782011479117831636309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265854674319411887757539 7898782011479117831636309)
            ·
              refine ⟨5785240731063807005593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7898782011479117831636309 5785240731063807005593)
              ·
                rfl

theorem cell21_228151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_228151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228151 prefixEnd_228151 := by exact prefixLift 228151
  have htrace : WordTrace (prefixWord ++ tailWord_228151) baseStart_228151 baseEnd_228151 := by
    simpa [prefixWord, tailWord_228151, baseEnd_228151] using wordTrace_append hprefix tailTrace_228151
  have hstable : (prefixWord ++ tailWord_228151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228151).length < 2 ^ (prefixWord ++ tailWord_228151).sum := by decide
  have hdescent : baseEnd_228151 < baseStart_228151 := by decide
  rcases family_descends (prefixWord ++ tailWord_228151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228154 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_228154 : Nat := 118140960795 + 228154 * 2 ^ 59
def prefixEnd_228154 : Nat := 4983230072969 + 3 ^ 40 * 228154 * 2
def baseEnd_228154 : Nat := 52067851220446924500331

theorem tailTrace_228154 : CollatzResearch.WordTrace tailWord_228154 prefixEnd_228154 52067851220446924500331 := by
  unfold tailWord_228154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080365003861124611524879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5547640010296332297399677 2080365003861124611524879)
  ·
    refine ⟨3120547505791686917287319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080365003861124611524879 3120547505791686917287319)
    ·
      refine ⟨4680821258687530375930979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120547505791686917287319 4680821258687530375930979)
      ·
        refine ⟨7021231888031295563896469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680821258687530375930979 7021231888031295563896469)
        ·
          refine ⟨329120244751466979557647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7021231888031295563896469 329120244751466979557647)
          ·
            refine ⟨493680367127200469336471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329120244751466979557647 493680367127200469336471)
            ·
              refine ⟨740520550690800704004707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493680367127200469336471 740520550690800704004707)
              ·
                refine ⟨1110780826036201056007061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740520550690800704004707 1110780826036201056007061)
                ·
                  refine ⟨52067851220446924500331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1110780826036201056007061 52067851220446924500331)
                  ·
                    rfl

theorem cell21_228154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_228154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228154 prefixEnd_228154 := by exact prefixLift 228154
  have htrace : WordTrace (prefixWord ++ tailWord_228154) baseStart_228154 baseEnd_228154 := by
    simpa [prefixWord, tailWord_228154, baseEnd_228154] using wordTrace_append hprefix tailTrace_228154
  have hstable : (prefixWord ++ tailWord_228154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228154).length < 2 ^ (prefixWord ++ tailWord_228154).sum := by decide
  have hdescent : baseEnd_228154 < baseStart_228154 := by decide
  rcases family_descends (prefixWord ++ tailWord_228154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228185 : List Nat := [1, 2, 1, 2, 2, 6, 2, 5]
def baseStart_228185 : Nat := 118140960795 + 228185 * 2 ^ 59
def prefixEnd_228185 : Nat := 4983230072969 + 3 ^ 40 * 228185 * 2
def baseEnd_228185 : Nat := 17358308614265919827867

theorem tailTrace_228185 : CollatzResearch.WordTrace tailWord_228185 prefixEnd_228185 17358308614265919827867 := by
  unfold tailWord_228185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322590678332190740478009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5548393785554793826985339 8322590678332190740478009)
  ·
    refine ⟨6241943008749143055358507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8322590678332190740478009 6241943008749143055358507)
    ·
      refine ⟨9362914513123714583037761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241943008749143055358507 9362914513123714583037761)
      ·
        refine ⟨7022185884842785937278321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9362914513123714583037761 7022185884842785937278321)
        ·
          refine ⟨5266639413632089452958741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022185884842785937278321 5266639413632089452958741)
          ·
            refine ⟨246873722514004193107441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5266639413632089452958741 246873722514004193107441)
            ·
              refine ⟨185155291885503144830581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246873722514004193107441 185155291885503144830581)
              ·
                refine ⟨17358308614265919827867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185155291885503144830581 17358308614265919827867)
                ·
                  rfl

theorem cell21_228185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].length) (baseStart_228185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228185 prefixEnd_228185 := by exact prefixLift 228185
  have htrace : WordTrace (prefixWord ++ tailWord_228185) baseStart_228185 baseEnd_228185 := by
    simpa [prefixWord, tailWord_228185, baseEnd_228185] using wordTrace_append hprefix tailTrace_228185
  have hstable : (prefixWord ++ tailWord_228185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228185).length < 2 ^ (prefixWord ++ tailWord_228185).sum := by decide
  have hdescent : baseEnd_228185 < baseStart_228185 := by decide
  rcases family_descends (prefixWord ++ tailWord_228185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228222 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_228222 : Nat := 118140960795 + 228222 * 2 ^ 59
def prefixEnd_228222 : Nat := 4983230072969 + 3 ^ 40 * 228222 * 2
def baseEnd_228222 : Nat := 52083369746893917366859

theorem tailTrace_228222 : CollatzResearch.WordTrace tailWord_228222 prefixEnd_228222 52083369746893917366859 := by
  unfold tailWord_228222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040492522399768257446865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5549293452798764039716613 1040492522399768257446865)
  ·
    refine ⟨780369391799826193085149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1040492522399768257446865 780369391799826193085149)
    ·
      refine ⟨292638521924934822406931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 780369391799826193085149 292638521924934822406931)
      ·
        refine ⟨438957782887402233610397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292638521924934822406931 438957782887402233610397)
        ·
          refine ⟨164609168582775837603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438957782887402233610397 164609168582775837603899)
          ·
            refine ⟨246913752874163756405849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164609168582775837603899 246913752874163756405849)
            ·
              refine ⟨185185314655622817304387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246913752874163756405849 185185314655622817304387)
              ·
                refine ⟨277777971983434225956581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185185314655622817304387 277777971983434225956581)
                ·
                  refine ⟨52083369746893917366859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277777971983434225956581 52083369746893917366859)
                  ·
                    rfl

theorem cell21_228222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_228222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228222 prefixEnd_228222 := by exact prefixLift 228222
  have htrace : WordTrace (prefixWord ++ tailWord_228222) baseStart_228222 baseEnd_228222 := by
    simpa [prefixWord, tailWord_228222, baseEnd_228222] using wordTrace_append hprefix tailTrace_228222
  have hstable : (prefixWord ++ tailWord_228222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228222).length < 2 ^ (prefixWord ++ tailWord_228222).sum := by decide
  have hdescent : baseEnd_228222 < baseStart_228222 := by decide
  rcases family_descends (prefixWord ++ tailWord_228222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228244 : List Nat := [2, 4, 2, 1, 1, 1, 1, 9]
def baseStart_228244 : Nat := 118140960795 + 228244 * 2 ^ 59
def prefixEnd_228244 : Nat := 4983230072969 + 3 ^ 40 * 228244 * 2
def baseEnd_228244 : Nat := 17362796815542256000049

theorem tailTrace_228244 : CollatzResearch.WordTrace tailWord_228244 prefixEnd_228244 17362796815542256000049 := by
  unfold tailWord_228244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162371292559221908437893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5549828390078962544583857 4162371292559221908437893)
  ·
    refine ⟨780444617354854107832105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4162371292559221908437893 780444617354854107832105)
    ·
      refine ⟨585333463016140580874079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 780444617354854107832105 585333463016140580874079)
      ·
        refine ⟨878000194524210871311119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585333463016140580874079 878000194524210871311119)
        ·
          refine ⟨1317000291786316306966679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878000194524210871311119 1317000291786316306966679)
          ·
            refine ⟨1975500437679474460450019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317000291786316306966679 1975500437679474460450019)
            ·
              refine ⟨2963250656519211690675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975500437679474460450019 2963250656519211690675029)
              ·
                refine ⟨17362796815542256000049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2963250656519211690675029 17362796815542256000049)
                ·
                  rfl

theorem cell21_228244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_228244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228244 prefixEnd_228244 := by exact prefixLift 228244
  have htrace : WordTrace (prefixWord ++ tailWord_228244) baseStart_228244 baseEnd_228244 := by
    simpa [prefixWord, tailWord_228244, baseEnd_228244] using wordTrace_append hprefix tailTrace_228244
  have hstable : (prefixWord ++ tailWord_228244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228244).length < 2 ^ (prefixWord ++ tailWord_228244).sum := by decide
  have hdescent : baseEnd_228244 < baseStart_228244 := by decide
  rcases family_descends (prefixWord ++ tailWord_228244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228309 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 3]
def baseStart_228309 : Nat := 118140960795 + 228309 * 2 ^ 59
def prefixEnd_228309 : Nat := 4983230072969 + 3 ^ 40 * 228309 * 2
def baseEnd_228309 : Nat := 52103224332201099416681

theorem tailTrace_228309 : CollatzResearch.WordTrace tailWord_228309 prefixEnd_228309 52103224332201099416681 := by
  unfold tailWord_228309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327113329882959917991981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5551408886588639945327987 8327113329882959917991981)
  ·
    refine ⟨3122667498706109969246993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8327113329882959917991981 3122667498706109969246993)
    ·
      refine ⟨2342000624029582476935245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3122667498706109969246993 2342000624029582476935245)
      ·
        refine ⟨878250234011093428850717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2342000624029582476935245 878250234011093428850717)
        ·
          refine ⟨329343837754160035819019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878250234011093428850717 329343837754160035819019)
          ·
            refine ⟨494015756631240053728529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329343837754160035819019 494015756631240053728529)
            ·
              refine ⟨370511817473430040296397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494015756631240053728529 370511817473430040296397)
              ·
                refine ⟨138941931552536265111149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370511817473430040296397 138941931552536265111149)
                ·
                  refine ⟨52103224332201099416681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138941931552536265111149 52103224332201099416681)
                  ·
                    rfl

theorem cell21_228309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_228309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228309 prefixEnd_228309 := by exact prefixLift 228309
  have htrace : WordTrace (prefixWord ++ tailWord_228309) baseStart_228309 baseEnd_228309 := by
    simpa [prefixWord, tailWord_228309, baseEnd_228309] using wordTrace_append hprefix tailTrace_228309
  have hstable : (prefixWord ++ tailWord_228309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228309).length < 2 ^ (prefixWord ++ tailWord_228309).sum := by decide
  have hdescent : baseEnd_228309 < baseStart_228309 := by decide
  rcases family_descends (prefixWord ++ tailWord_228309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228354 : List Nat := [3, 4, 1, 3, 1, 1, 1, 7]
def baseStart_228354 : Nat := 118140960795 + 228354 * 2 ^ 59
def prefixEnd_228354 : Nat := 4983230072969 + 3 ^ 40 * 228354 * 2
def baseEnd_228354 : Nat := 17371164648430340388863

theorem tailTrace_228354 : CollatzResearch.WordTrace tailWord_228354 prefixEnd_228354 17371164648430340388863 := by
  unfold tailWord_228354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082188653679983150845029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5552503076479955068920077 2082188653679983150845029)
  ·
    refine ⟨390410372564996840783443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2082188653679983150845029 390410372564996840783443)
    ·
      refine ⟨585615558847495261175165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390410372564996840783443 585615558847495261175165)
      ·
        refine ⟨219605834567810722940687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585615558847495261175165 219605834567810722940687)
        ·
          refine ⟨329408751851716084411031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219605834567810722940687 329408751851716084411031)
          ·
            refine ⟨494113127777574126616547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329408751851716084411031 494113127777574126616547)
            ·
              refine ⟨741169691666361189924821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494113127777574126616547 741169691666361189924821)
              ·
                refine ⟨17371164648430340388863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 741169691666361189924821 17371164648430340388863)
                ·
                  rfl

theorem cell21_228354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_228354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228354 prefixEnd_228354 := by exact prefixLift 228354
  have htrace : WordTrace (prefixWord ++ tailWord_228354) baseStart_228354 baseEnd_228354 := by
    simpa [prefixWord, tailWord_228354, baseEnd_228354] using wordTrace_append hprefix tailTrace_228354
  have hstable : (prefixWord ++ tailWord_228354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228354).length < 2 ^ (prefixWord ++ tailWord_228354).sum := by decide
  have hdescent : baseEnd_228354 < baseStart_228354 := by decide
  rcases family_descends (prefixWord ++ tailWord_228354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228385 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 3]
def baseStart_228385 : Nat := 118140960795 + 228385 * 2 ^ 59
def prefixEnd_228385 : Nat := 4983230072969 + 3 ^ 40 * 228385 * 2
def baseEnd_228385 : Nat := 52120568567641856149859

theorem tailTrace_228385 : CollatzResearch.WordTrace tailWord_228385 prefixEnd_228385 52120568567641856149859 := by
  unfold tailWord_228385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329885277607624897758609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5553256851738416598505739 8329885277607624897758609)
  ·
    refine ⟨6247413958205718673318957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8329885277607624897758609 6247413958205718673318957)
    ·
      refine ⟨2342780234327144502494609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6247413958205718673318957 2342780234327144502494609)
      ·
        refine ⟨1757085175745358376870957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2342780234327144502494609 1757085175745358376870957)
        ·
          refine ⟨658906940904509391326609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1757085175745358376870957 658906940904509391326609)
          ·
            refine ⟨494180205678382043494957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658906940904509391326609 494180205678382043494957)
            ·
              refine ⟨185317577129393266310609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494180205678382043494957 185317577129393266310609)
              ·
                refine ⟨138988182847044949732957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185317577129393266310609 138988182847044949732957)
                ·
                  refine ⟨52120568567641856149859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138988182847044949732957 52120568567641856149859)
                  ·
                    rfl

theorem cell21_228385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_228385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228385 prefixEnd_228385 := by exact prefixLift 228385
  have htrace : WordTrace (prefixWord ++ tailWord_228385) baseStart_228385 baseEnd_228385 := by
    simpa [prefixWord, tailWord_228385, baseEnd_228385] using wordTrace_append hprefix tailTrace_228385
  have hstable : (prefixWord ++ tailWord_228385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228385).length < 2 ^ (prefixWord ++ tailWord_228385).sum := by decide
  have hdescent : baseEnd_228385 < baseStart_228385 := by decide
  rcases family_descends (prefixWord ++ tailWord_228385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228410 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_228410 : Nat := 118140960795 + 228410 * 2 ^ 59
def prefixEnd_228410 : Nat := 4983230072969 + 3 ^ 40 * 228410 * 2
def baseEnd_228410 : Nat := 52126273908247368233141

theorem tailTrace_228410 : CollatzResearch.WordTrace tailWord_228410 prefixEnd_228410 52126273908247368233141 := by
  unfold tailWord_228410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082699275629263541854671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5553864735011369444945789 2082699275629263541854671)
  ·
    refine ⟨3124048913443895312782007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082699275629263541854671 3124048913443895312782007)
    ·
      refine ⟨4686073370165842969173011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124048913443895312782007 4686073370165842969173011)
      ·
        refine ⟨7029110055248764453759517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686073370165842969173011 7029110055248764453759517)
        ·
          refine ⟨2635916270718286670159819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7029110055248764453759517 2635916270718286670159819)
          ·
            refine ⟨3953874406077430005239729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635916270718286670159819 3953874406077430005239729)
            ·
              refine ⟨2965405804558072503929797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953874406077430005239729 2965405804558072503929797)
              ·
                refine ⟨556013588354638594486837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2965405804558072503929797 556013588354638594486837)
                ·
                  refine ⟨52126273908247368233141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556013588354638594486837 52126273908247368233141)
                  ·
                    rfl

theorem cell21_228410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_228410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228410 prefixEnd_228410 := by exact prefixLift 228410
  have htrace : WordTrace (prefixWord ++ tailWord_228410) baseStart_228410 baseEnd_228410 := by
    simpa [prefixWord, tailWord_228410, baseEnd_228410] using wordTrace_append hprefix tailTrace_228410
  have hstable : (prefixWord ++ tailWord_228410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228410).length < 2 ^ (prefixWord ++ tailWord_228410).sum := by decide
  have hdescent : baseEnd_228410 < baseStart_228410 := by decide
  rcases family_descends (prefixWord ++ tailWord_228410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228444 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_228444 : Nat := 118140960795 + 228444 * 2 ^ 59
def prefixEnd_228444 : Nat := 4983230072969 + 3 ^ 40 * 228444 * 2
def baseEnd_228444 : Nat := 52134033171470864666405

theorem tailTrace_228444 : CollatzResearch.WordTrace tailWord_228444 prefixEnd_228444 52134033171470864666405 := by
  unfold tailWord_228444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166018592196938987078193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5554691456262585316104257 4166018592196938987078193)
  ·
    refine ⟨3124513944147704240308645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4166018592196938987078193 3124513944147704240308645)
    ·
      refine ⟨585846364527694545057871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3124513944147704240308645 585846364527694545057871)
      ·
        refine ⟨878769546791541817586807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585846364527694545057871 878769546791541817586807)
        ·
          refine ⟨1318154320187312726380211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878769546791541817586807 1318154320187312726380211)
          ·
            refine ⟨1977231480280969089570317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318154320187312726380211 1977231480280969089570317)
            ·
              refine ⟨741461805105363408588869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1977231480280969089570317 741461805105363408588869)
              ·
                refine ⟨139024088457255639110413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741461805105363408588869 139024088457255639110413)
                ·
                  refine ⟨52134033171470864666405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139024088457255639110413 52134033171470864666405)
                  ·
                    rfl

theorem cell21_228444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_228444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228444 prefixEnd_228444 := by exact prefixLift 228444
  have htrace : WordTrace (prefixWord ++ tailWord_228444) baseStart_228444 baseEnd_228444 := by
    simpa [prefixWord, tailWord_228444, baseEnd_228444] using wordTrace_append hprefix tailTrace_228444
  have hstable : (prefixWord ++ tailWord_228444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228444).length < 2 ^ (prefixWord ++ tailWord_228444).sum := by decide
  have hdescent : baseEnd_228444 < baseStart_228444 := by decide
  rcases family_descends (prefixWord ++ tailWord_228444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228458 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_228458 : Nat := 118140960795 + 228458 * 2 ^ 59
def prefixEnd_228458 : Nat := 4983230072969 + 3 ^ 40 * 228458 * 2
def baseEnd_228458 : Nat := 52137228162209951433043

theorem tailTrace_228458 : CollatzResearch.WordTrace tailWord_228458 prefixEnd_228458 52137228162209951433043 := by
  unfold tailWord_228458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083136951585789591291507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5555031870895438910110685 2083136951585789591291507)
  ·
    refine ⟨3124705427378684386937261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083136951585789591291507 3124705427378684386937261)
    ·
      refine ⟨1171764535267006645101473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3124705427378684386937261 1171764535267006645101473)
      ·
        refine ⟨878823401450254983826105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171764535267006645101473 878823401450254983826105)
        ·
          refine ⟨659117551087691237869579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878823401450254983826105 659117551087691237869579)
          ·
            refine ⟨988676326631536856804369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659117551087691237869579 988676326631536856804369)
            ·
              refine ⟨741507244973652642603277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988676326631536856804369 741507244973652642603277)
              ·
                refine ⟨278065216865119740976229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 741507244973652642603277 278065216865119740976229)
                ·
                  refine ⟨52137228162209951433043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278065216865119740976229 52137228162209951433043)
                  ·
                    rfl

theorem cell21_228458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_228458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228458 prefixEnd_228458 := by exact prefixLift 228458
  have htrace : WordTrace (prefixWord ++ tailWord_228458) baseStart_228458 baseEnd_228458 := by
    simpa [prefixWord, tailWord_228458, baseEnd_228458] using wordTrace_append hprefix tailTrace_228458
  have hstable : (prefixWord ++ tailWord_228458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228458).length < 2 ^ (prefixWord ++ tailWord_228458).sum := by decide
  have hdescent : baseEnd_228458 < baseStart_228458 := by decide
  rcases family_descends (prefixWord ++ tailWord_228458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228503 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_228503 : Nat := 118140960795 + 228503 * 2 ^ 59
def prefixEnd_228503 : Nat := 4983230072969 + 3 ^ 40 * 228503 * 2
def baseEnd_228503 : Nat := 52147497775299873182951

theorem tailTrace_228503 : CollatzResearch.WordTrace tailWord_228503 prefixEnd_228503 52147497775299873182951 := by
  unfold tailWord_228503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334189091180131050554163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5556126060786754033702775 8334189091180131050554163)
  ·
    refine ⟨12501283636770196575831245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8334189091180131050554163 12501283636770196575831245)
    ·
      refine ⟨4687981363788823715936717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12501283636770196575831245 4687981363788823715936717)
      ·
        refine ⟨1757993011420808893476269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4687981363788823715936717 1757993011420808893476269)
        ·
          refine ⟨659247379282803335053601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1757993011420808893476269 659247379282803335053601)
          ·
            refine ⟨494435534462102501290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659247379282803335053601 494435534462102501290201)
            ·
              refine ⟨370826650846576875967651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494435534462102501290201 370826650846576875967651)
              ·
                refine ⟨556239976269865313951477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370826650846576875967651 556239976269865313951477)
                ·
                  refine ⟨52147497775299873182951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556239976269865313951477 52147497775299873182951)
                  ·
                    rfl

theorem cell21_228503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_228503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228503 prefixEnd_228503 := by exact prefixLift 228503
  have htrace : WordTrace (prefixWord ++ tailWord_228503) baseStart_228503 baseEnd_228503 := by
    simpa [prefixWord, tailWord_228503, baseEnd_228503] using wordTrace_append hprefix tailTrace_228503
  have hstable : (prefixWord ++ tailWord_228503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228503).length < 2 ^ (prefixWord ++ tailWord_228503).sum := by decide
  have hdescent : baseEnd_228503 < baseStart_228503 := by decide
  rcases family_descends (prefixWord ++ tailWord_228503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228568 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_228568 : Nat := 118140960795 + 228568 * 2 ^ 59
def prefixEnd_228568 : Nat := 4983230072969 + 3 ^ 40 * 228568 * 2
def baseEnd_228568 : Nat := 52162331660874204599485

theorem tailTrace_228568 : CollatzResearch.WordTrace tailWord_228568 prefixEnd_228568 52162331660874204599485 := by
  unfold tailWord_228568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168279917972323575835179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5557706557296431434446905 4168279917972323575835179)
  ·
    refine ⟨6252419876958485363752769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168279917972323575835179 6252419876958485363752769)
    ·
      refine ⟨4689314907718864022814577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6252419876958485363752769 4689314907718864022814577)
      ·
        refine ⟨3516986180789148017110933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4689314907718864022814577 3516986180789148017110933)
        ·
          refine ⟨164858727224491313302075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3516986180789148017110933 164858727224491313302075)
          ·
            refine ⟨247288090836736969953113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164858727224491313302075 247288090836736969953113)
            ·
              refine ⟨185466068127552727464835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247288090836736969953113 185466068127552727464835)
              ·
                refine ⟨278199102191329091197253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185466068127552727464835 278199102191329091197253)
                ·
                  refine ⟨52162331660874204599485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278199102191329091197253 52162331660874204599485)
                  ·
                    rfl

theorem cell21_228568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_228568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228568 prefixEnd_228568 := by exact prefixLift 228568
  have htrace : WordTrace (prefixWord ++ tailWord_228568) baseStart_228568 baseEnd_228568 := by
    simpa [prefixWord, tailWord_228568, baseEnd_228568] using wordTrace_append hprefix tailTrace_228568
  have hstable : (prefixWord ++ tailWord_228568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228568).length < 2 ^ (prefixWord ++ tailWord_228568).sum := by decide
  have hdescent : baseEnd_228568 < baseStart_228568 := by decide
  rcases family_descends (prefixWord ++ tailWord_228568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228652 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_228652 : Nat := 118140960795 + 228652 * 2 ^ 59
def prefixEnd_228652 : Nat := 4983230072969 + 3 ^ 40 * 228652 * 2
def baseEnd_228652 : Nat := 52181501605308725199313

theorem tailTrace_228652 : CollatzResearch.WordTrace tailWord_228652 prefixEnd_228652 52181501605308725199313 := by
  unfold tailWord_228652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169811783820164748864105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5559749045093552998485473 4169811783820164748864105)
  ·
    refine ⟨3127358837865123561648079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4169811783820164748864105 3127358837865123561648079)
    ·
      refine ⟨4691038256797685342472119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127358837865123561648079 4691038256797685342472119)
      ·
        refine ⟨7036557385196528013708179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691038256797685342472119 7036557385196528013708179)
        ·
          refine ⟨10554836077794792020562269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036557385196528013708179 10554836077794792020562269)
          ·
            refine ⟨3958063529173047007710851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10554836077794792020562269 3958063529173047007710851)
            ·
              refine ⟨5937095293759570511566277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958063529173047007710851 5937095293759570511566277)
              ·
                refine ⟨1113205367579919470918677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5937095293759570511566277 1113205367579919470918677)
                ·
                  refine ⟨52181501605308725199313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1113205367579919470918677 52181501605308725199313)
                  ·
                    rfl

theorem cell21_228652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_228652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228652 prefixEnd_228652 := by exact prefixLift 228652
  have htrace : WordTrace (prefixWord ++ tailWord_228652) baseStart_228652 baseEnd_228652 := by
    simpa [prefixWord, tailWord_228652, baseEnd_228652] using wordTrace_append hprefix tailTrace_228652
  have hstable : (prefixWord ++ tailWord_228652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228652).length < 2 ^ (prefixWord ++ tailWord_228652).sum := by decide
  have hdescent : baseEnd_228652 < baseStart_228652 := by decide
  rcases family_descends (prefixWord ++ tailWord_228652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228686 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_228686 : Nat := 118140960795 + 228686 * 2 ^ 59
def prefixEnd_228686 : Nat := 4983230072969 + 3 ^ 40 * 228686 * 2
def baseEnd_228686 : Nat := 52189260868532221632577

theorem tailTrace_228686 : CollatzResearch.WordTrace tailWord_228686 prefixEnd_228686 52189260868532221632577 := by
  unfold tailWord_228686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042607956189644163058239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5560575766344768869643941 1042607956189644163058239)
  ·
    refine ⟨1563911934284466244587359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042607956189644163058239 1563911934284466244587359)
    ·
      refine ⟨2345867901426699366881039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563911934284466244587359 2345867901426699366881039)
      ·
        refine ⟨3518801852140049050321559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345867901426699366881039 3518801852140049050321559)
        ·
          refine ⟨5278202778210073575482339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518801852140049050321559 5278202778210073575482339)
          ·
            refine ⟨7917304167315110363223509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278202778210073575482339 7917304167315110363223509)
            ·
              refine ⟨185561816421447899138051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7917304167315110363223509 185561816421447899138051)
              ·
                refine ⟨278342724632171848707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185561816421447899138051 278342724632171848707077)
                ·
                  refine ⟨52189260868532221632577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278342724632171848707077 52189260868532221632577)
                  ·
                    rfl

theorem cell21_228686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_228686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228686 prefixEnd_228686 := by exact prefixLift 228686
  have htrace : WordTrace (prefixWord ++ tailWord_228686) baseStart_228686 baseEnd_228686 := by
    simpa [prefixWord, tailWord_228686, baseEnd_228686] using wordTrace_append hprefix tailTrace_228686
  have hstable : (prefixWord ++ tailWord_228686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228686).length < 2 ^ (prefixWord ++ tailWord_228686).sum := by decide
  have hdescent : baseEnd_228686 < baseStart_228686 := by decide
  rcases family_descends (prefixWord ++ tailWord_228686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228734 : List Nat := [4, 2, 3, 2, 1, 1, 2, 6]
def baseStart_228734 : Nat := 118140960795 + 228734 * 2 ^ 59
def prefixEnd_228734 : Nat := 4983230072969 + 3 ^ 40 * 228734 * 2
def baseEnd_228734 : Nat := 17400071707498268277493

theorem tailTrace_228734 : CollatzResearch.WordTrace tailWord_228734 prefixEnd_228734 17400071707498268277493 := by
  unfold tailWord_228734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042826794167907187776657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5561742902228838334808837 1042826794167907187776657)
  ·
    refine ⟨782120095625930390832493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042826794167907187776657 782120095625930390832493)
    ·
      refine ⟨293295035859723896562185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 782120095625930390832493 293295035859723896562185)
      ·
        refine ⟨219971276894792922421639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293295035859723896562185 219971276894792922421639)
        ·
          refine ⟨329956915342189383632459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219971276894792922421639 329956915342189383632459)
          ·
            refine ⟨494935373013284075448689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329956915342189383632459 494935373013284075448689)
            ·
              refine ⟨371201529759963056586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494935373013284075448689 371201529759963056586517)
              ·
                refine ⟨17400071707498268277493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371201529759963056586517 17400071707498268277493)
                ·
                  rfl

theorem cell21_228734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_228734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228734 prefixEnd_228734 := by exact prefixLift 228734
  have htrace : WordTrace (prefixWord ++ tailWord_228734) baseStart_228734 baseEnd_228734 := by
    simpa [prefixWord, tailWord_228734, baseEnd_228734] using wordTrace_append hprefix tailTrace_228734
  have hstable : (prefixWord ++ tailWord_228734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228734).length < 2 ^ (prefixWord ++ tailWord_228734).sum := by decide
  have hdescent : baseEnd_228734 < baseStart_228734 := by decide
  rcases family_descends (prefixWord ++ tailWord_228734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228773 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_228773 : Nat := 118140960795 + 228773 * 2 ^ 59
def prefixEnd_228773 : Nat := 4983230072969 + 3 ^ 40 * 228773 * 2
def baseEnd_228773 : Nat := 52209115453839403682399

theorem tailTrace_228773 : CollatzResearch.WordTrace tailWord_228773 prefixEnd_228773 52209115453839403682399 := by
  unfold tailWord_228773
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344036800201967162882973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5562691200134644775255315 8344036800201967162882973)
  ·
    refine ⟨3129013800075737686081115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8344036800201967162882973 3129013800075737686081115)
    ·
      refine ⟨4693520700113606529121673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129013800075737686081115 4693520700113606529121673)
      ·
        refine ⟨3520140525085204896841255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693520700113606529121673 3520140525085204896841255)
        ·
          refine ⟨5280210787627807345261883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520140525085204896841255 5280210787627807345261883)
          ·
            refine ⟨7920316181441711017892825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280210787627807345261883 7920316181441711017892825)
            ·
              refine ⟨5940237136081283263419619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920316181441711017892825 5940237136081283263419619)
              ·
                refine ⟨8910355704121924895129429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940237136081283263419619 8910355704121924895129429)
                ·
                  refine ⟨52209115453839403682399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8910355704121924895129429 52209115453839403682399)
                  ·
                    rfl

theorem cell21_228773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_228773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228773 prefixEnd_228773 := by exact prefixLift 228773
  have htrace : WordTrace (prefixWord ++ tailWord_228773) baseStart_228773 baseEnd_228773 := by
    simpa [prefixWord, tailWord_228773, baseEnd_228773] using wordTrace_append hprefix tailTrace_228773
  have hstable : (prefixWord ++ tailWord_228773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228773).length < 2 ^ (prefixWord ++ tailWord_228773).sum := by decide
  have hdescent : baseEnd_228773 < baseStart_228773 := by decide
  rcases family_descends (prefixWord ++ tailWord_228773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228776 : List Nat := [2, 1, 6, 1, 2, 9]
def baseStart_228776 : Nat := 118140960795 + 228776 * 2 ^ 59
def prefixEnd_228776 : Nat := 4983230072969 + 3 ^ 40 * 228776 * 2
def baseEnd_228776 : Nat := 1933696299804150560459

theorem tailTrace_228776 : CollatzResearch.WordTrace tailWord_228776 prefixEnd_228776 1933696299804150560459 := by
  unfold tailWord_228776
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172073109595549337621091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5562764146127399116828121 4172073109595549337621091)
  ·
    refine ⟨6258109664393324006431637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172073109595549337621091 6258109664393324006431637)
    ·
      refine ⟨293348890518437062801483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6258109664393324006431637 293348890518437062801483)
      ·
        refine ⟨440023335777655594202225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293348890518437062801483 440023335777655594202225)
        ·
          refine ⟨330017501833241695651669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440023335777655594202225 330017501833241695651669)
          ·
            refine ⟨1933696299804150560459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 330017501833241695651669 1933696299804150560459)
            ·
              rfl

theorem cell21_228776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 9].length) (baseStart_228776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228776 prefixEnd_228776 := by exact prefixLift 228776
  have htrace : WordTrace (prefixWord ++ tailWord_228776) baseStart_228776 baseEnd_228776 := by
    simpa [prefixWord, tailWord_228776, baseEnd_228776] using wordTrace_append hprefix tailTrace_228776
  have hstable : (prefixWord ++ tailWord_228776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228776).length < 2 ^ (prefixWord ++ tailWord_228776).sum := by decide
  have hdescent : baseEnd_228776 < baseStart_228776 := by decide
  rcases family_descends (prefixWord ++ tailWord_228776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228793 : List Nat := [1, 2, 1, 4, 5, 1, 1, 6]
def baseStart_228793 : Nat := 118140960795 + 228793 * 2 ^ 59
def prefixEnd_228793 : Nat := 4983230072969 + 3 ^ 40 * 228793 * 2
def baseEnd_228793 : Nat := 17404559908774604449675

theorem tailTrace_228793 : CollatzResearch.WordTrace tailWord_228793 prefixEnd_228793 17404559908774604449675 := by
  unfold tailWord_228793
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344766260129510578611033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5563177506753007052407355 8344766260129510578611033)
  ·
    refine ⟨6258574695097132933958275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8344766260129510578611033 6258574695097132933958275)
    ·
      refine ⟨9387862042645699400937413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258574695097132933958275 9387862042645699400937413)
      ·
        refine ⟨1760224132996068637675765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9387862042645699400937413 1760224132996068637675765)
        ·
          refine ⟨165021012468381434782103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1760224132996068637675765 165021012468381434782103)
          ·
            refine ⟨247531518702572152173155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165021012468381434782103 247531518702572152173155)
            ·
              refine ⟨371297278053858228259733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247531518702572152173155 371297278053858228259733)
              ·
                refine ⟨17404559908774604449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371297278053858228259733 17404559908774604449675)
                ·
                  rfl

theorem cell21_228793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].length) (baseStart_228793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228793 prefixEnd_228793 := by exact prefixLift 228793
  have htrace : WordTrace (prefixWord ++ tailWord_228793) baseStart_228793 baseEnd_228793 := by
    simpa [prefixWord, tailWord_228793, baseEnd_228793] using wordTrace_append hprefix tailTrace_228793
  have hstable : (prefixWord ++ tailWord_228793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228793).length < 2 ^ (prefixWord ++ tailWord_228793).sum := by decide
  have hdescent : baseEnd_228793 < baseStart_228793 := by decide
  rcases family_descends (prefixWord ++ tailWord_228793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228835 : List Nat := [1, 1, 1, 6, 2, 2, 8]
def baseStart_228835 : Nat := 118140960795 + 228835 * 2 ^ 59
def prefixEnd_228835 : Nat := 4983230072969 + 3 ^ 40 * 228835 * 2
def baseEnd_228835 : Nat := 5802584966504563738771

theorem tailTrace_228835 : CollatzResearch.WordTrace tailWord_228835 prefixEnd_228835 5802584966504563738771 := by
  unfold tailWord_228835
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346298125977351751639959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5564198750651567834426639 8346298125977351751639959)
  ·
    refine ⟨12519447188966027627459939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346298125977351751639959 12519447188966027627459939)
    ·
      refine ⟨18779170783449041441189909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12519447188966027627459939 18779170783449041441189909)
      ·
        refine ⟨880273630474173817555777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18779170783449041441189909 880273630474173817555777)
        ·
          refine ⟨660205222855630363166833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880273630474173817555777 660205222855630363166833)
          ·
            refine ⟨495153917141722772375125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660205222855630363166833 495153917141722772375125)
            ·
              refine ⟨5802584966504563738771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 495153917141722772375125 5802584966504563738771)
              ·
                rfl

theorem cell21_228835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_228835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228835 prefixEnd_228835 := by exact prefixLift 228835
  have htrace : WordTrace (prefixWord ++ tailWord_228835) baseStart_228835 baseEnd_228835 := by
    simpa [prefixWord, tailWord_228835, baseEnd_228835] using wordTrace_append hprefix tailTrace_228835
  have hstable : (prefixWord ++ tailWord_228835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228835).length < 2 ^ (prefixWord ++ tailWord_228835).sum := by decide
  have hdescent : baseEnd_228835 < baseStart_228835 := by decide
  rcases family_descends (prefixWord ++ tailWord_228835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228883 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 3]
def baseStart_228883 : Nat := 118140960795 + 228883 * 2 ^ 59
def prefixEnd_228883 : Nat := 4983230072969 + 3 ^ 40 * 228883 * 2
def baseEnd_228883 : Nat := 52234218952503656848841

theorem tailTrace_228883 : CollatzResearch.WordTrace tailWord_228883 prefixEnd_228883 52234218952503656848841 := by
  unfold tailWord_228883
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348048829803455949387303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5565365886535637299591535 8348048829803455949387303)
  ·
    refine ⟨12522073244705183924080955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348048829803455949387303 12522073244705183924080955)
    ·
      refine ⟨18783109867057775886121433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12522073244705183924080955 18783109867057775886121433)
      ·
        refine ⟨14087332400293331914591075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18783109867057775886121433 14087332400293331914591075)
        ·
          refine ⟨21130998600439997871886613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087332400293331914591075 21130998600439997871886613)
          ·
            refine ⟨990515559395624900244685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21130998600439997871886613 990515559395624900244685)
            ·
              refine ⟨371443334773359337591757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990515559395624900244685 371443334773359337591757)
              ·
                refine ⟨139291250540009751596909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371443334773359337591757 139291250540009751596909)
                ·
                  refine ⟨52234218952503656848841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139291250540009751596909 52234218952503656848841)
                  ·
                    rfl

theorem cell21_228883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].length) (baseStart_228883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228883 prefixEnd_228883 := by exact prefixLift 228883
  have htrace : WordTrace (prefixWord ++ tailWord_228883) baseStart_228883 baseEnd_228883 := by
    simpa [prefixWord, tailWord_228883, baseEnd_228883] using wordTrace_append hprefix tailTrace_228883
  have hstable : (prefixWord ++ tailWord_228883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228883).length < 2 ^ (prefixWord ++ tailWord_228883).sum := by decide
  have hdescent : baseEnd_228883 < baseStart_228883 := by decide
  rcases family_descends (prefixWord ++ tailWord_228883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228987 : List Nat := [1, 1, 1, 1, 1, 4, 7, 5]
def baseStart_228987 : Nat := 118140960795 + 228987 * 2 ^ 59
def prefixEnd_228987 : Nat := 4983230072969 + 3 ^ 40 * 228987 * 2
def baseEnd_228987 : Nat := 17419317723140862371765

theorem tailTrace_228987 : CollatzResearch.WordTrace tailWord_228987 prefixEnd_228987 17419317723140862371765 := by
  unfold tailWord_228987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351842021426681711173215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567894680951121140782143 8351842021426681711173215)
  ·
    refine ⟨12527763032140022566759823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8351842021426681711173215 12527763032140022566759823)
    ·
      refine ⟨18791644548210033850139735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12527763032140022566759823 18791644548210033850139735)
      ·
        refine ⟨28187466822315050775209603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18791644548210033850139735 28187466822315050775209603)
        ·
          refine ⟨42281200233472576162814405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28187466822315050775209603 42281200233472576162814405)
          ·
            refine ⟨7927725043776108030527701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42281200233472576162814405 7927725043776108030527701)
            ·
              refine ⟨185806055713502531965493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7927725043776108030527701 185806055713502531965493)
              ·
                refine ⟨17419317723140862371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185806055713502531965493 17419317723140862371765)
                ·
                  rfl

theorem cell21_228987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].length) (baseStart_228987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_228987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_228987 prefixEnd_228987 := by exact prefixLift 228987
  have htrace : WordTrace (prefixWord ++ tailWord_228987) baseStart_228987 baseEnd_228987 := by
    simpa [prefixWord, tailWord_228987, baseEnd_228987] using wordTrace_append hprefix tailTrace_228987
  have hstable : (prefixWord ++ tailWord_228987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228987).length < 2 ^ (prefixWord ++ tailWord_228987).sum := by decide
  have hdescent : baseEnd_228987 < baseStart_228987 := by decide
  rcases family_descends (prefixWord ++ tailWord_228987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229038 : List Nat := [4, 1, 4, 1, 2, 2, 2, 5]
def baseStart_229038 : Nat := 118140960795 + 229038 * 2 ^ 59
def prefixEnd_229038 : Nat := 4983230072969 + 3 ^ 40 * 229038 * 2
def baseEnd_229038 : Nat := 17423197354752610588397

theorem tailTrace_229038 : CollatzResearch.WordTrace tailWord_229038 prefixEnd_229038 17423197354752610588397 := by
  unfold tailWord_229038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044212768030239677659971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5569134762827944947519845 1044212768030239677659971)
  ·
    refine ⟨1566319152045359516489957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044212768030239677659971 1566319152045359516489957)
    ·
      refine ⟨293684841008504909341867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1566319152045359516489957 293684841008504909341867)
      ·
        refine ⟨440527261512757364012801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293684841008504909341867 440527261512757364012801)
        ·
          refine ⟨330395446134568023009601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440527261512757364012801 330395446134568023009601)
          ·
            refine ⟨247796584600926017257201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330395446134568023009601 247796584600926017257201)
            ·
              refine ⟨185847438450694512942901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247796584600926017257201 185847438450694512942901)
              ·
                refine ⟨17423197354752610588397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185847438450694512942901 17423197354752610588397)
                ·
                  rfl

theorem cell21_229038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_229038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229038 prefixEnd_229038 := by exact prefixLift 229038
  have htrace : WordTrace (prefixWord ++ tailWord_229038) baseStart_229038 baseEnd_229038 := by
    simpa [prefixWord, tailWord_229038, baseEnd_229038] using wordTrace_append hprefix tailTrace_229038
  have hstable : (prefixWord ++ tailWord_229038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229038).length < 2 ^ (prefixWord ++ tailWord_229038).sum := by decide
  have hdescent : baseEnd_229038 < baseStart_229038 := by decide
  rcases family_descends (prefixWord ++ tailWord_229038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229052 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_229052 : Nat := 118140960795 + 229052 * 2 ^ 59
def prefixEnd_229052 : Nat := 4983230072969 + 3 ^ 40 * 229052 * 2
def baseEnd_229052 : Nat := 52272787054996918531829

theorem tailTrace_229052 : CollatzResearch.WordTrace tailWord_229052 prefixEnd_229052 52272787054996918531829 := by
  unfold tailWord_229052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177106383095598906144705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5569475177460798541526273 4177106383095598906144705)
  ·
    refine ⟨3132829787321699179608529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4177106383095598906144705 3132829787321699179608529)
    ·
      refine ⟨2349622340491274384706397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3132829787321699179608529 2349622340491274384706397)
      ·
        refine ⟨881108377684227894264899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2349622340491274384706397 881108377684227894264899)
        ·
          refine ⟨1321662566526341841397349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881108377684227894264899 1321662566526341841397349)
          ·
            refine ⟨247811731223689095262003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1321662566526341841397349 247811731223689095262003)
            ·
              refine ⟨371717596835533642893005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247811731223689095262003 371717596835533642893005)
              ·
                refine ⟨139394098813325116084877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371717596835533642893005 139394098813325116084877)
                ·
                  refine ⟨52272787054996918531829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139394098813325116084877 52272787054996918531829)
                  ·
                    rfl

theorem cell21_229052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_229052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229052 prefixEnd_229052 := by exact prefixLift 229052
  have htrace : WordTrace (prefixWord ++ tailWord_229052) baseStart_229052 baseEnd_229052 := by
    simpa [prefixWord, tailWord_229052, baseEnd_229052] using wordTrace_append hprefix tailTrace_229052
  have hstable : (prefixWord ++ tailWord_229052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229052).length < 2 ^ (prefixWord ++ tailWord_229052).sum := by decide
  have hdescent : baseEnd_229052 < baseStart_229052 := by decide
  rcases family_descends (prefixWord ++ tailWord_229052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229153 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_229153 : Nat := 118140960795 + 229153 * 2 ^ 59
def prefixEnd_229153 : Nat := 4983230072969 + 3 ^ 40 * 229153 * 2
def baseEnd_229153 : Nat := 52295836631043187348289

theorem tailTrace_229153 : CollatzResearch.WordTrace tailWord_229153 prefixEnd_229153 52295836631043187348289 := by
  unfold tailWord_229153
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357896538825292061716113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5571931025883528041144075 8357896538825292061716113)
  ·
    refine ⟨6268422404118969046287085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8357896538825292061716113 6268422404118969046287085)
    ·
      refine ⟨2350658401544613392357657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6268422404118969046287085 2350658401544613392357657)
      ·
        refine ⟨1762993801158460044268243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350658401544613392357657 1762993801158460044268243)
        ·
          refine ⟨2644490701737690066402365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762993801158460044268243 2644490701737690066402365)
          ·
            refine ⟨991684013151633774900887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644490701737690066402365 991684013151633774900887)
            ·
              refine ⟨1487526019727450662351331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991684013151633774900887 1487526019727450662351331)
              ·
                refine ⟨2231289029591175993526997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487526019727450662351331 2231289029591175993526997)
                ·
                  refine ⟨52295836631043187348289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2231289029591175993526997 52295836631043187348289)
                  ·
                    rfl

theorem cell21_229153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_229153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229153 prefixEnd_229153 := by exact prefixLift 229153
  have htrace : WordTrace (prefixWord ++ tailWord_229153) baseStart_229153 baseEnd_229153 := by
    simpa [prefixWord, tailWord_229153, baseEnd_229153] using wordTrace_append hprefix tailTrace_229153
  have hstable : (prefixWord ++ tailWord_229153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229153).length < 2 ^ (prefixWord ++ tailWord_229153).sum := by decide
  have hdescent : baseEnd_229153 < baseStart_229153 := by decide
  rcases family_descends (prefixWord ++ tailWord_229153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229156 : List Nat := [2, 3, 1, 3, 2, 2, 3, 5]
def baseStart_229156 : Nat := 118140960795 + 229156 * 2 ^ 59
def prefixEnd_229156 : Nat := 4983230072969 + 3 ^ 40 * 229156 * 2
def baseEnd_229156 : Nat := 17432173757305282932761

theorem tailTrace_229156 : CollatzResearch.WordTrace tailWord_229156 prefixEnd_229156 17432173757305282932761 := by
  unfold tailWord_229156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179002978907211787037661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5572003971876282382716881 4179002978907211787037661)
  ·
    refine ⟨1567126117090204420139123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4179002978907211787037661 1567126117090204420139123)
    ·
      refine ⟨2350689175635306630208685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567126117090204420139123 2350689175635306630208685)
      ·
        refine ⟨881508440863239986328257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2350689175635306630208685 881508440863239986328257)
        ·
          refine ⟨661131330647429989746193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881508440863239986328257 661131330647429989746193)
          ·
            refine ⟨495848497985572492309645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661131330647429989746193 495848497985572492309645)
            ·
              refine ⟨185943186744589684616117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495848497985572492309645 185943186744589684616117)
              ·
                refine ⟨17432173757305282932761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185943186744589684616117 17432173757305282932761)
                ·
                  rfl

theorem cell21_229156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_229156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229156 prefixEnd_229156 := by exact prefixLift 229156
  have htrace : WordTrace (prefixWord ++ tailWord_229156) baseStart_229156 baseEnd_229156 := by
    simpa [prefixWord, tailWord_229156, baseEnd_229156] using wordTrace_append hprefix tailTrace_229156
  have hstable : (prefixWord ++ tailWord_229156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229156).length < 2 ^ (prefixWord ++ tailWord_229156).sum := by decide
  have hdescent : baseEnd_229156 < baseStart_229156 := by decide
  rcases family_descends (prefixWord ++ tailWord_229156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229167 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_229167 : Nat := 118140960795 + 229167 * 2 ^ 59
def prefixEnd_229167 : Nat := 4983230072969 + 3 ^ 40 * 229167 * 2
def baseEnd_229167 : Nat := 52299031621782274114927

theorem tailTrace_229167 : CollatzResearch.WordTrace tailWord_229167 prefixEnd_229167 52299031621782274114927 := by
  unfold tailWord_229167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358407160774572452725755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5572271440516381635150503 8358407160774572452725755)
  ·
    refine ⟨12537610741161858679088633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8358407160774572452725755 12537610741161858679088633)
    ·
      refine ⟨9403208055871394009316475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12537610741161858679088633 9403208055871394009316475)
      ·
        refine ⟨14104812083807091013974713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403208055871394009316475 14104812083807091013974713)
        ·
          refine ⟨10578609062855318260481035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14104812083807091013974713 10578609062855318260481035)
          ·
            refine ⟨15867913594282977390721553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10578609062855318260481035 15867913594282977390721553)
            ·
              refine ⟨11900935195712233043041165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15867913594282977390721553 11900935195712233043041165)
              ·
                refine ⟨4462850698392087391140437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11900935195712233043041165 4462850698392087391140437)
                ·
                  refine ⟨52299031621782274114927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4462850698392087391140437 52299031621782274114927)
                  ·
                    rfl

theorem cell21_229167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_229167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229167 prefixEnd_229167 := by exact prefixLift 229167
  have htrace : WordTrace (prefixWord ++ tailWord_229167) baseStart_229167 baseEnd_229167 := by
    simpa [prefixWord, tailWord_229167, baseEnd_229167] using wordTrace_append hprefix tailTrace_229167
  have hstable : (prefixWord ++ tailWord_229167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229167).length < 2 ^ (prefixWord ++ tailWord_229167).sum := by decide
  have hdescent : baseEnd_229167 < baseStart_229167 := by decide
  rcases family_descends (prefixWord ++ tailWord_229167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229215 : List Nat := [1, 1, 2, 3, 1, 4, 4, 5]
def baseStart_229215 : Nat := 118140960795 + 229215 * 2 ^ 59
def prefixEnd_229215 : Nat := 4983230072969 + 3 ^ 40 * 229215 * 2
def baseEnd_229215 : Nat := 17436661958581619104943

theorem tailTrace_229215 : CollatzResearch.WordTrace tailWord_229215 prefixEnd_229215 17436661958581619104943 := by
  unfold tailWord_229215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360157864600676650473099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5573438576400451100315399 8360157864600676650473099)
  ·
    refine ⟨12540236796901014975709649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360157864600676650473099 12540236796901014975709649)
    ·
      refine ⟨9405177597675761231782237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12540236796901014975709649 9405177597675761231782237)
      ·
        refine ⟨3526941599128410461918339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9405177597675761231782237 3526941599128410461918339)
        ·
          refine ⟨5290412398692615692877509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526941599128410461918339 5290412398692615692877509)
          ·
            refine ⟨991952324754865442414533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5290412398692615692877509 991952324754865442414533)
            ·
              refine ⟨185991060891537270452725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 991952324754865442414533 185991060891537270452725)
              ·
                refine ⟨17436661958581619104943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185991060891537270452725 17436661958581619104943)
                ·
                  rfl

theorem cell21_229215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].length) (baseStart_229215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229215 prefixEnd_229215 := by exact prefixLift 229215
  have htrace : WordTrace (prefixWord ++ tailWord_229215) baseStart_229215 baseEnd_229215 := by
    simpa [prefixWord, tailWord_229215, baseEnd_229215] using wordTrace_append hprefix tailTrace_229215
  have hstable : (prefixWord ++ tailWord_229215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229215).length < 2 ^ (prefixWord ++ tailWord_229215).sum := by decide
  have hdescent : baseEnd_229215 < baseStart_229215 := by decide
  rcases family_descends (prefixWord ++ tailWord_229215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229229 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_229229 : Nat := 118140960795 + 229229 * 2 ^ 59
def prefixEnd_229229 : Nat := 4983230072969 + 3 ^ 40 * 229229 * 2
def baseEnd_229229 : Nat := 52313180866483944081467

theorem tailTrace_229229 : CollatzResearch.WordTrace tailWord_229229 prefixEnd_229229 52313180866483944081467 := by
  unfold tailWord_229229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360668486549957041482741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5573778991033304694321827 8360668486549957041482741)
  ·
    refine ⟨783812670614058472639007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8360668486549957041482741 783812670614058472639007)
    ·
      refine ⟨1175719005921087708958511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783812670614058472639007 1175719005921087708958511)
      ·
        refine ⟨1763578508881631563437767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175719005921087708958511 1763578508881631563437767)
        ·
          refine ⟨2645367763322447345156651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763578508881631563437767 2645367763322447345156651)
          ·
            refine ⟨3968051644983671017734977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645367763322447345156651 3968051644983671017734977)
            ·
              refine ⟨2976038733737753263301233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968051644983671017734977 2976038733737753263301233)
              ·
                refine ⟨2232029050303314947475925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976038733737753263301233 2232029050303314947475925)
                ·
                  refine ⟨52313180866483944081467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2232029050303314947475925 52313180866483944081467)
                  ·
                    rfl

theorem cell21_229229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_229229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229229 prefixEnd_229229 := by exact prefixLift 229229
  have htrace : WordTrace (prefixWord ++ tailWord_229229) baseStart_229229 baseEnd_229229 := by
    simpa [prefixWord, tailWord_229229, baseEnd_229229] using wordTrace_append hprefix tailTrace_229229
  have hstable : (prefixWord ++ tailWord_229229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229229).length < 2 ^ (prefixWord ++ tailWord_229229).sum := by decide
  have hdescent : baseEnd_229229 < baseStart_229229 := by decide
  rcases family_descends (prefixWord ++ tailWord_229229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229305 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_229305 : Nat := 118140960795 + 229305 * 2 ^ 59
def prefixEnd_229305 : Nat := 4983230072969 + 3 ^ 40 * 229305 * 2
def baseEnd_229305 : Nat := 52330525101924700814645

theorem tailTrace_229305 : CollatzResearch.WordTrace tailWord_229305 prefixEnd_229305 52330525101924700814645 := by
  unfold tailWord_229305
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363440434274622021249369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5575626956183081347499579 8363440434274622021249369)
  ·
    refine ⟨6272580325705966515937027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8363440434274622021249369 6272580325705966515937027)
    ·
      refine ⟨9408870488558949773905541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272580325705966515937027 9408870488558949773905541)
      ·
        refine ⟨1764163216604803082607289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9408870488558949773905541 1764163216604803082607289)
        ·
          refine ⟨1323122412453602311955467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764163216604803082607289 1323122412453602311955467)
          ·
            refine ⟨1984683618680403467933201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323122412453602311955467 1984683618680403467933201)
            ·
              refine ⟨1488512714010302600949901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984683618680403467933201 1488512714010302600949901)
              ·
                refine ⟨558192267753863475356213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488512714010302600949901 558192267753863475356213)
                ·
                  refine ⟨52330525101924700814645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558192267753863475356213 52330525101924700814645)
                  ·
                    rfl

theorem cell21_229305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_229305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229305 prefixEnd_229305 := by exact prefixLift 229305
  have htrace : WordTrace (prefixWord ++ tailWord_229305) baseStart_229305 baseEnd_229305 := by
    simpa [prefixWord, tailWord_229305, baseEnd_229305] using wordTrace_append hprefix tailTrace_229305
  have hstable : (prefixWord ++ tailWord_229305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229305).length < 2 ^ (prefixWord ++ tailWord_229305).sum := by decide
  have hdescent : baseEnd_229305 < baseStart_229305 := by decide
  rcases family_descends (prefixWord ++ tailWord_229305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229319 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_229319 : Nat := 118140960795 + 229319 * 2 ^ 59
def prefixEnd_229319 : Nat := 4983230072969 + 3 ^ 40 * 229319 * 2
def baseEnd_229319 : Nat := 52333720092663787581283

theorem tailTrace_229319 : CollatzResearch.WordTrace tailWord_229319 prefixEnd_229319 52333720092663787581283 := by
  unfold tailWord_229319
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363951056223902412259011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5575967370815934941506007 8363951056223902412259011)
  ·
    refine ⟨12545926584335853618388517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363951056223902412259011 12545926584335853618388517)
    ·
      refine ⟨2352361234562972553447847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12545926584335853618388517 2352361234562972553447847)
      ·
        refine ⟨3528541851844458830171771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352361234562972553447847 3528541851844458830171771)
        ·
          refine ⟨5292812777766688245257657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528541851844458830171771 5292812777766688245257657)
          ·
            refine ⟨3969609583325016183943243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292812777766688245257657 3969609583325016183943243)
            ·
              refine ⟨5954414374987524275914865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969609583325016183943243 5954414374987524275914865)
              ·
                refine ⟨4465810781240643206936149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954414374987524275914865 4465810781240643206936149)
                ·
                  refine ⟨52333720092663787581283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4465810781240643206936149 52333720092663787581283)
                  ·
                    rfl

theorem cell21_229319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_229319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229319 prefixEnd_229319 := by exact prefixLift 229319
  have htrace : WordTrace (prefixWord ++ tailWord_229319) baseStart_229319 baseEnd_229319 := by
    simpa [prefixWord, tailWord_229319, baseEnd_229319] using wordTrace_append hprefix tailTrace_229319
  have hstable : (prefixWord ++ tailWord_229319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229319).length < 2 ^ (prefixWord ++ tailWord_229319).sum := by decide
  have hdescent : baseEnd_229319 < baseStart_229319 := by decide
  rcases family_descends (prefixWord ++ tailWord_229319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229381 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_229381 : Nat := 118140960795 + 229381 * 2 ^ 59
def prefixEnd_229381 : Nat := 4983230072969 + 3 ^ 40 * 229381 * 2
def baseEnd_229381 : Nat := 52347869337365457547823

theorem tailTrace_229381 : CollatzResearch.WordTrace tailWord_229381 prefixEnd_229381 52347869337365457547823 := by
  unfold tailWord_229381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366212381999287001015997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5577474921332858000677331 8366212381999287001015997)
  ·
    refine ⟨3137329643249732625380999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8366212381999287001015997 3137329643249732625380999)
    ·
      refine ⟨4705994464874598938071499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137329643249732625380999 4705994464874598938071499)
      ·
        refine ⟨7058991697311898407107249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705994464874598938071499 7058991697311898407107249)
        ·
          refine ⟨5294243772983923805330437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058991697311898407107249 5294243772983923805330437)
          ·
            refine ⟨992670707434485713499457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5294243772983923805330437 992670707434485713499457)
            ·
              refine ⟨744503030575864285124593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992670707434485713499457 744503030575864285124593)
              ·
                refine ⟨558377272931898213843445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744503030575864285124593 558377272931898213843445)
                ·
                  refine ⟨52347869337365457547823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558377272931898213843445 52347869337365457547823)
                  ·
                    rfl

theorem cell21_229381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_229381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229381 prefixEnd_229381 := by exact prefixLift 229381
  have htrace : WordTrace (prefixWord ++ tailWord_229381) baseStart_229381 baseEnd_229381 := by
    simpa [prefixWord, tailWord_229381, baseEnd_229381] using wordTrace_append hprefix tailTrace_229381
  have hstable : (prefixWord ++ tailWord_229381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229381).length < 2 ^ (prefixWord ++ tailWord_229381).sum := by decide
  have hdescent : baseEnd_229381 < baseStart_229381 := by decide
  rcases family_descends (prefixWord ++ tailWord_229381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229395 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_229395 : Nat := 118140960795 + 229395 * 2 ^ 59
def prefixEnd_229395 : Nat := 4983230072969 + 3 ^ 40 * 229395 * 2
def baseEnd_229395 : Nat := 52351064328104544314461

theorem tailTrace_229395 : CollatzResearch.WordTrace tailWord_229395 prefixEnd_229395 52351064328104544314461 := by
  unfold tailWord_229395
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366723003948567392025639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5577815335965711594683759 8366723003948567392025639)
  ·
    refine ⟨12550084505922851088038459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366723003948567392025639 12550084505922851088038459)
    ·
      refine ⟨18825126758884276632057689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12550084505922851088038459 18825126758884276632057689)
      ·
        refine ⟨14118845069163207474043267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18825126758884276632057689 14118845069163207474043267)
        ·
          refine ⟨21178267603744811211064901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14118845069163207474043267 21178267603744811211064901)
          ·
            refine ⟨3970925175702152102074669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21178267603744811211064901 3970925175702152102074669)
            ·
              refine ⟨1489096940888307038278001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3970925175702152102074669 1489096940888307038278001)
              ·
                refine ⟨1116822705666230278708501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489096940888307038278001 1116822705666230278708501)
                ·
                  refine ⟨52351064328104544314461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1116822705666230278708501 52351064328104544314461)
                  ·
                    rfl

theorem cell21_229395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_229395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229395 prefixEnd_229395 := by exact prefixLift 229395
  have htrace : WordTrace (prefixWord ++ tailWord_229395) baseStart_229395 baseEnd_229395 := by
    simpa [prefixWord, tailWord_229395, baseEnd_229395] using wordTrace_append hprefix tailTrace_229395
  have hstable : (prefixWord ++ tailWord_229395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229395).length < 2 ^ (prefixWord ++ tailWord_229395).sum := by decide
  have hdescent : baseEnd_229395 < baseStart_229395 := by decide
  rcases family_descends (prefixWord ++ tailWord_229395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229426 : List Nat := [3, 2, 1, 1, 2, 3, 1, 8]
def baseStart_229426 : Nat := 118140960795 + 229426 * 2 ^ 59
def prefixEnd_229426 : Nat := 4983230072969 + 3 ^ 40 * 229426 * 2
def baseEnd_229426 : Nat := 17452712983485126432577

theorem tailTrace_229426 : CollatzResearch.WordTrace tailWord_229426 prefixEnd_229426 17452712983485126432577 := by
  unfold tailWord_229426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091963416709064921601033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5578569111224173124269421 2091963416709064921601033)
  ·
    refine ⟨1568972562531798691200775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2091963416709064921601033 1568972562531798691200775)
    ·
      refine ⟨2353458843797698036801163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568972562531798691200775 2353458843797698036801163)
      ·
        refine ⟨3530188265696547055201745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353458843797698036801163 3530188265696547055201745)
        ·
          refine ⟨2647641199272410291401309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530188265696547055201745 2647641199272410291401309)
          ·
            refine ⟨992865449727153859275491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2647641199272410291401309 992865449727153859275491)
            ·
              refine ⟨1489298174590730788913237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992865449727153859275491 1489298174590730788913237)
              ·
                refine ⟨17452712983485126432577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1489298174590730788913237 17452712983485126432577)
                ·
                  rfl

theorem cell21_229426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_229426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229426 prefixEnd_229426 := by exact prefixLift 229426
  have htrace : WordTrace (prefixWord ++ tailWord_229426) baseStart_229426 baseEnd_229426 := by
    simpa [prefixWord, tailWord_229426, baseEnd_229426] using wordTrace_append hprefix tailTrace_229426
  have hstable : (prefixWord ++ tailWord_229426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229426).length < 2 ^ (prefixWord ++ tailWord_229426).sum := by decide
  have hdescent : baseEnd_229426 < baseStart_229426 := by decide
  rcases family_descends (prefixWord ++ tailWord_229426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229429 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 4]
def baseStart_229429 : Nat := 118140960795 + 229429 * 2 ^ 59
def prefixEnd_229429 : Nat := 4983230072969 + 3 ^ 40 * 229429 * 2
def baseEnd_229429 : Nat := 52358823591328040747725

theorem tailTrace_229429 : CollatzResearch.WordTrace tailWord_229429 prefixEnd_229429 52358823591328040747725 := by
  unfold tailWord_229429
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367963085825391198763341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5578642057216927465842227 8367963085825391198763341)
  ·
    refine ⟨3137986157184521699536253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8367963085825391198763341 3137986157184521699536253)
    ·
      refine ⟨1176744808944195637326095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3137986157184521699536253 1176744808944195637326095)
      ·
        refine ⟨1765117213416293455989143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176744808944195637326095 1765117213416293455989143)
        ·
          refine ⟨2647675820124440183983715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765117213416293455989143 2647675820124440183983715)
          ·
            refine ⟨3971513730186660275975573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647675820124440183983715 3971513730186660275975573)
            ·
              refine ⟨186164706102499700436355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3971513730186660275975573 186164706102499700436355)
              ·
                refine ⟨279247059153749550654533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186164706102499700436355 279247059153749550654533)
                ·
                  refine ⟨52358823591328040747725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279247059153749550654533 52358823591328040747725)
                  ·
                    rfl

theorem cell21_229429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_229429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229429 prefixEnd_229429 := by exact prefixLift 229429
  have htrace : WordTrace (prefixWord ++ tailWord_229429) baseStart_229429 baseEnd_229429 := by
    simpa [prefixWord, tailWord_229429, baseEnd_229429] using wordTrace_append hprefix tailTrace_229429
  have hstable : (prefixWord ++ tailWord_229429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229429).length < 2 ^ (prefixWord ++ tailWord_229429).sum := by decide
  have hdescent : baseEnd_229429 < baseStart_229429 := by decide
  rcases family_descends (prefixWord ++ tailWord_229429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
