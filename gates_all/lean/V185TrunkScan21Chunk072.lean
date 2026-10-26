import V185TrunkScan21Chunk071

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_872259 : List Nat := [1, 1, 1, 3, 1, 6, 3, 5]
def baseStart_872259 : Nat := 118140960795 + 872259 * 2 ^ 59
def prefixEnd_872259 : Nat := 4983230072969 + 3 ^ 40 * 872259 * 2
def baseEnd_872259 : Nat := 66353795882993780200157

theorem tailTrace_872259 : CollatzResearch.WordTrace tailWord_872259 prefixEnd_872259 66353795882993780200157 := by
  unfold tailWord_872259
  simp only [CollatzResearch.WordTrace]
  refine ⟨31813899346962087822203831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21209266231308058548135887 31813899346962087822203831)
  ·
    refine ⟨47720849020443131733305747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31813899346962087822203831 47720849020443131733305747)
    ·
      refine ⟨71581273530664697599958621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47720849020443131733305747 71581273530664697599958621)
      ·
        refine ⟨26842977573999261599984483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71581273530664697599958621 26842977573999261599984483)
        ·
          refine ⟨40264466360998892399976725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26842977573999261599984483 40264466360998892399976725)
          ·
            refine ⟨1887396860671823081248909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40264466360998892399976725 1887396860671823081248909)
            ·
              refine ⟨707773822751933655468341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1887396860671823081248909 707773822751933655468341)
              ·
                refine ⟨66353795882993780200157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707773822751933655468341 66353795882993780200157)
                ·
                  rfl

theorem cell21_872259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].length) (baseStart_872259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872259 prefixEnd_872259 := by exact prefixLift 872259
  have htrace : WordTrace (prefixWord ++ tailWord_872259) baseStart_872259 baseEnd_872259 := by
    simpa [prefixWord, tailWord_872259, baseEnd_872259] using wordTrace_append hprefix tailTrace_872259
  have hstable : (prefixWord ++ tailWord_872259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872259).length < 2 ^ (prefixWord ++ tailWord_872259).sum := by decide
  have hdescent : baseEnd_872259 < baseStart_872259 := by decide
  rcases family_descends (prefixWord ++ tailWord_872259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872290 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_872290 : Nat := 118140960795 + 872290 * 2 ^ 59
def prefixEnd_872290 : Nat := 4983230072969 + 3 ^ 40 * 872290 * 2
def baseEnd_872290 : Nat := 199068462271332175583741

theorem tailTrace_872290 : CollatzResearch.WordTrace tailWord_872290 prefixEnd_872290 199068462271332175583741 := by
  unfold tailWord_872290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953757502462445029145581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21210020006566520077721549 7953757502462445029145581)
  ·
    refine ⟨2982659063423416885929593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7953757502462445029145581 2982659063423416885929593)
    ·
      refine ⟨2236994297567562664447195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2982659063423416885929593 2236994297567562664447195)
      ·
        refine ⟨3355491446351343996670793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236994297567562664447195 3355491446351343996670793)
        ·
          refine ⟨2516618584763507997503095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355491446351343996670793 2516618584763507997503095)
          ·
            refine ⟨3774927877145261996254643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516618584763507997503095 3774927877145261996254643)
            ·
              refine ⟨5662391815717892994381965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774927877145261996254643 5662391815717892994381965)
              ·
                refine ⟨2123396930894209872893237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5662391815717892994381965 2123396930894209872893237)
                ·
                  refine ⟨199068462271332175583741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123396930894209872893237 199068462271332175583741)
                  ·
                    rfl

theorem cell21_872290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_872290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872290 prefixEnd_872290 := by exact prefixLift 872290
  have htrace : WordTrace (prefixWord ++ tailWord_872290) baseStart_872290 baseEnd_872290 := by
    simpa [prefixWord, tailWord_872290, baseEnd_872290] using wordTrace_append hprefix tailTrace_872290
  have hstable : (prefixWord ++ tailWord_872290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872290).length < 2 ^ (prefixWord ++ tailWord_872290).sum := by decide
  have hdescent : baseEnd_872290 < baseStart_872290 := by decide
  rcases family_descends (prefixWord ++ tailWord_872290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872310 : List Nat := [5, 1, 1, 3, 3, 1, 2, 5]
def baseStart_872310 : Nat := 118140960795 + 872310 * 2 ^ 59
def prefixEnd_872310 : Nat := 4983230072969 + 3 ^ 40 * 872310 * 2
def baseEnd_872310 : Nat := 66357675514605528416789

theorem tailTrace_872310 : CollatzResearch.WordTrace tailWord_872310 prefixEnd_872310 66357675514605528416789 := by
  unfold tailWord_872310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988484966861082720769399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21210506313184882354873589 1988484966861082720769399)
  ·
    refine ⟨2982727450291624081154099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1988484966861082720769399 2982727450291624081154099)
    ·
      refine ⟨4474091175437436121731149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982727450291624081154099 4474091175437436121731149)
      ·
        refine ⟨1677784190789038545649181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4474091175437436121731149 1677784190789038545649181)
        ·
          refine ⟨629169071545889454618443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1677784190789038545649181 629169071545889454618443)
          ·
            refine ⟨943753607318834181927665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629169071545889454618443 943753607318834181927665)
            ·
              refine ⟨707815205489125636445749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943753607318834181927665 707815205489125636445749)
              ·
                refine ⟨66357675514605528416789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707815205489125636445749 66357675514605528416789)
                ·
                  rfl

theorem cell21_872310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_872310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872310 prefixEnd_872310 := by exact prefixLift 872310
  have htrace : WordTrace (prefixWord ++ tailWord_872310) baseStart_872310 baseEnd_872310 := by
    simpa [prefixWord, tailWord_872310, baseEnd_872310] using wordTrace_append hprefix tailTrace_872310
  have hstable : (prefixWord ++ tailWord_872310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872310).length < 2 ^ (prefixWord ++ tailWord_872310).sum := by decide
  have hdescent : baseEnd_872310 < baseStart_872310 := by decide
  rcases family_descends (prefixWord ++ tailWord_872310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872687 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 3]
def baseStart_872687 : Nat := 118140960795 + 872687 * 2 ^ 59
def prefixEnd_872687 : Nat := 4983230072969 + 3 ^ 40 * 872687 * 2
def baseEnd_872687 : Nat := 199159063080147707466263

theorem tailTrace_872687 : CollatzResearch.WordTrace tailWord_872687 prefixEnd_872687 199159063080147707466263 := by
  unfold tailWord_872687
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829509789411516918784315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21219673192941011279189543 31829509789411516918784315)
  ·
    refine ⟨47744264684117275378176473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31829509789411516918784315 47744264684117275378176473)
    ·
      refine ⟨35808198513087956533632355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47744264684117275378176473 35808198513087956533632355)
      ·
        refine ⟨53712297769631934800448533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35808198513087956533632355 53712297769631934800448533)
        ·
          refine ⟨2517763957951496943771025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53712297769631934800448533 2517763957951496943771025)
          ·
            refine ⟨1888322968463622707828269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517763957951496943771025 1888322968463622707828269)
            ·
              refine ⟨708121113173858515435601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888322968463622707828269 708121113173858515435601)
              ·
                refine ⟨531090834880393886576701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708121113173858515435601 531090834880393886576701)
                ·
                  refine ⟨199159063080147707466263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531090834880393886576701 199159063080147707466263)
                  ·
                    rfl

theorem cell21_872687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].length) (baseStart_872687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872687 prefixEnd_872687 := by exact prefixLift 872687
  have htrace : WordTrace (prefixWord ++ tailWord_872687) baseStart_872687 baseEnd_872687 := by
    simpa [prefixWord, tailWord_872687, baseEnd_872687] using wordTrace_append hprefix tailTrace_872687
  have hstable : (prefixWord ++ tailWord_872687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872687).length < 2 ^ (prefixWord ++ tailWord_872687).sum := by decide
  have hdescent : baseEnd_872687 < baseStart_872687 := by decide
  rcases family_descends (prefixWord ++ tailWord_872687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872698 : List Nat := [3, 1, 1, 1, 1, 6, 2, 6]
def baseStart_872698 : Nat := 118140960795 + 872698 * 2 ^ 59
def prefixEnd_872698 : Nat := 4983230072969 + 3 ^ 40 * 872698 * 2
def baseEnd_872698 : Nat := 66387191143338044260969

theorem tailTrace_872698 : CollatzResearch.WordTrace tailWord_872698 prefixEnd_872698 66387191143338044260969 := by
  unfold tailWord_872698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957477748092916449358687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21219940661581110531623165 7957477748092916449358687)
  ·
    refine ⟨11936216622139374674038031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7957477748092916449358687 11936216622139374674038031)
    ·
      refine ⟨17904324933209062011057047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936216622139374674038031 17904324933209062011057047)
      ·
        refine ⟨26856487399813593016585571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904324933209062011057047 26856487399813593016585571)
        ·
          refine ⟨40284731099720389524878357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26856487399813593016585571 40284731099720389524878357)
          ·
            refine ⟨1888346770299393258978673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40284731099720389524878357 1888346770299393258978673)
            ·
              refine ⟨1416260077724544944234005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888346770299393258978673 1416260077724544944234005)
              ·
                refine ⟨66387191143338044260969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416260077724544944234005 66387191143338044260969)
                ·
                  rfl

theorem cell21_872698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_872698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872698 prefixEnd_872698 := by exact prefixLift 872698
  have htrace : WordTrace (prefixWord ++ tailWord_872698) baseStart_872698 baseEnd_872698 := by
    simpa [prefixWord, tailWord_872698, baseEnd_872698] using wordTrace_append hprefix tailTrace_872698
  have hstable : (prefixWord ++ tailWord_872698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872698).length < 2 ^ (prefixWord ++ tailWord_872698).sum := by decide
  have hdescent : baseEnd_872698 < baseStart_872698 := by decide
  rcases family_descends (prefixWord ++ tailWord_872698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872749 : List Nat := [1, 5, 3, 1, 3, 1, 1, 6]
def baseStart_872749 : Nat := 118140960795 + 872749 * 2 ^ 59
def prefixEnd_872749 : Nat := 4983230072969 + 3 ^ 40 * 872749 * 2
def baseEnd_872749 : Nat := 66391070774949792477601

theorem tailTrace_872749 : CollatzResearch.WordTrace tailWord_872749 prefixEnd_872749 66391070774949792477601 := by
  unfold tailWord_872749
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831771115186901507541301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21221180743457934338360867 31831771115186901507541301)
  ·
    refine ⟨2984228542048772016331997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31831771115186901507541301 2984228542048772016331997)
    ·
      refine ⟨1119085703268289506124499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2984228542048772016331997 1119085703268289506124499)
      ·
        refine ⟨1678628554902434259186749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119085703268289506124499 1678628554902434259186749)
        ·
          refine ⟨629485708088412847195031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1678628554902434259186749 629485708088412847195031)
          ·
            refine ⟨944228562132619270792547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629485708088412847195031 944228562132619270792547)
            ·
              refine ⟨1416342843198928906188821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944228562132619270792547 1416342843198928906188821)
              ·
                refine ⟨66391070774949792477601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416342843198928906188821 66391070774949792477601)
                ·
                  rfl

theorem cell21_872749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].length) (baseStart_872749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872749 prefixEnd_872749 := by exact prefixLift 872749
  have htrace : WordTrace (prefixWord ++ tailWord_872749) baseStart_872749 baseEnd_872749 := by
    simpa [prefixWord, tailWord_872749, baseEnd_872749] using wordTrace_append hprefix tailTrace_872749
  have hstable : (prefixWord ++ tailWord_872749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872749).length < 2 ^ (prefixWord ++ tailWord_872749).sum := by decide
  have hdescent : baseEnd_872749 < baseStart_872749 := by decide
  rcases family_descends (prefixWord ++ tailWord_872749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872805 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_872805 : Nat := 118140960795 + 872805 * 2 ^ 59
def prefixEnd_872805 : Nat := 4983230072969 + 3 ^ 40 * 872805 * 2
def baseEnd_872805 : Nat := 199185992287805724499355

theorem tailTrace_872805 : CollatzResearch.WordTrace tailWord_872805 prefixEnd_872805 199185992287805724499355 := by
  unfold tailWord_872805
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833813602984023071579869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21222542401989348714386579 31833813602984023071579869)
  ·
    refine ⟨11937680101119008651842451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31833813602984023071579869 11937680101119008651842451)
    ·
      refine ⟨17906520151678512977763677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937680101119008651842451 17906520151678512977763677)
      ·
        refine ⟨6714945056879442366661379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17906520151678512977763677 6714945056879442366661379)
        ·
          refine ⟨10072417585319163549992069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714945056879442366661379 10072417585319163549992069)
          ·
            refine ⟨1888578297247343165623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10072417585319163549992069 1888578297247343165623513)
            ·
              refine ⟨1416433722935507374217635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888578297247343165623513 1416433722935507374217635)
              ·
                refine ⟨2124650584403261061326453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416433722935507374217635 2124650584403261061326453)
                ·
                  refine ⟨199185992287805724499355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2124650584403261061326453 199185992287805724499355)
                  ·
                    rfl

theorem cell21_872805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_872805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872805 prefixEnd_872805 := by exact prefixLift 872805
  have htrace : WordTrace (prefixWord ++ tailWord_872805) baseStart_872805 baseEnd_872805 := by
    simpa [prefixWord, tailWord_872805, baseEnd_872805] using wordTrace_append hprefix tailTrace_872805
  have hstable : (prefixWord ++ tailWord_872805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872805).length < 2 ^ (prefixWord ++ tailWord_872805).sum := by decide
  have hdescent : baseEnd_872805 < baseStart_872805 := by decide
  rcases family_descends (prefixWord ++ tailWord_872805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872909 : List Nat := [1, 6, 14]
def baseStart_872909 : Nat := 118140960795 + 872909 * 2 ^ 59
def prefixEnd_872909 : Nat := 4983230072969 + 3 ^ 40 * 872909 * 2
def baseEnd_872909 : Nat := 273264371062722434521

theorem tailTrace_872909 : CollatzResearch.WordTrace tailWord_872909 prefixEnd_872909 273264371062722434521 := by
  unfold tailWord_872909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837606794607248833365781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21225071196404832555577187 31837606794607248833365781)
  ·
    refine ⟨1492387818497214789064021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31837606794607248833365781 1492387818497214789064021)
    ·
      refine ⟨273264371062722434521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1492387818497214789064021 273264371062722434521)
      ·
        rfl

theorem cell21_872909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 14].length) (baseStart_872909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872909 prefixEnd_872909 := by exact prefixLift 872909
  have htrace : WordTrace (prefixWord ++ tailWord_872909) baseStart_872909 baseEnd_872909 := by
    simpa [prefixWord, tailWord_872909, baseEnd_872909] using wordTrace_append hprefix tailTrace_872909
  have hstable : (prefixWord ++ tailWord_872909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872909).length < 2 ^ (prefixWord ++ tailWord_872909).sum := by decide
  have hdescent : baseEnd_872909 < baseStart_872909 := by decide
  rcases family_descends (prefixWord ++ tailWord_872909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872940 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_872940 : Nat := 118140960795 + 872940 * 2 ^ 59
def prefixEnd_872940 : Nat := 4983230072969 + 3 ^ 40 * 872940 * 2
def baseEnd_872940 : Nat := 199216801127075489749079

theorem tailTrace_872940 : CollatzResearch.WordTrace tailWord_872940 prefixEnd_872940 199216801127075489749079 := by
  unfold tailWord_872940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919368728747470563872137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21225824971663294085162849 15919368728747470563872137)
  ·
    refine ⟨11939526546560602922904103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15919368728747470563872137 11939526546560602922904103)
    ·
      refine ⟨17909289819840904384356155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11939526546560602922904103 17909289819840904384356155)
      ·
        refine ⟨26863934729761356576534233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17909289819840904384356155 26863934729761356576534233)
        ·
          refine ⟨20147951047321017432400675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26863934729761356576534233 20147951047321017432400675)
          ·
            refine ⟨30221926570981526148601013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20147951047321017432400675 30221926570981526148601013)
            ·
              refine ⟨2833305616029518076431345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30221926570981526148601013 2833305616029518076431345)
              ·
                refine ⟨2124979212022138557323509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833305616029518076431345 2124979212022138557323509)
                ·
                  refine ⟨199216801127075489749079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2124979212022138557323509 199216801127075489749079)
                  ·
                    rfl

theorem cell21_872940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_872940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872940 prefixEnd_872940 := by exact prefixLift 872940
  have htrace : WordTrace (prefixWord ++ tailWord_872940) baseStart_872940 baseEnd_872940 := by
    simpa [prefixWord, tailWord_872940, baseEnd_872940] using wordTrace_append hprefix tailTrace_872940
  have hstable : (prefixWord ++ tailWord_872940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872940).length < 2 ^ (prefixWord ++ tailWord_872940).sum := by decide
  have hdescent : baseEnd_872940 < baseStart_872940 := by decide
  rcases family_descends (prefixWord ++ tailWord_872940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872971 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_872971 : Nat := 118140960795 + 872971 * 2 ^ 59
def prefixEnd_872971 : Nat := 4983230072969 + 3 ^ 40 * 872971 * 2
def baseEnd_872971 : Nat := 199223875749426324732349

theorem tailTrace_872971 : CollatzResearch.WordTrace tailWord_872971 prefixEnd_872971 199223875749426324732349 := by
  unfold tailWord_872971
  simp only [CollatzResearch.WordTrace]
  refine ⟨31839868120382633422122767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21226578746921755614748511 31839868120382633422122767)
  ·
    refine ⟨47759802180573950133184151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31839868120382633422122767 47759802180573950133184151)
    ·
      refine ⟨71639703270860925199776227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47759802180573950133184151 71639703270860925199776227)
      ·
        refine ⟨107459554906291387799664341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71639703270860925199776227 107459554906291387799664341)
        ·
          refine ⟨2518583318116204401554633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107459554906291387799664341 2518583318116204401554633)
          ·
            refine ⟨1888937488587153301165975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518583318116204401554633 1888937488587153301165975)
            ·
              refine ⟨2833406232880729951748963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888937488587153301165975 2833406232880729951748963)
              ·
                refine ⟨4250109349321094927623445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833406232880729951748963 4250109349321094927623445)
                ·
                  refine ⟨199223875749426324732349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4250109349321094927623445 199223875749426324732349)
                  ·
                    rfl

theorem cell21_872971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_872971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872971 prefixEnd_872971 := by exact prefixLift 872971
  have htrace : WordTrace (prefixWord ++ tailWord_872971) baseStart_872971 baseEnd_872971 := by
    simpa [prefixWord, tailWord_872971, baseEnd_872971] using wordTrace_append hprefix tailTrace_872971
  have hstable : (prefixWord ++ tailWord_872971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872971).length < 2 ^ (prefixWord ++ tailWord_872971).sum := by decide
  have hdescent : baseEnd_872971 < baseStart_872971 := by decide
  rcases family_descends (prefixWord ++ tailWord_872971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872974 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_872974 : Nat := 118140960795 + 872974 * 2 ^ 59
def prefixEnd_872974 : Nat := 4983230072969 + 3 ^ 40 * 872974 * 2
def baseEnd_872974 : Nat := 199224560390298986182343

theorem tailTrace_872974 : CollatzResearch.WordTrace tailWord_872974 prefixEnd_872974 199224560390298986182343 := by
  unfold tailWord_872974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979997192421470616810247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21226651692914509956321317 3979997192421470616810247)
  ·
    refine ⟨5969995788632205925215371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3979997192421470616810247 5969995788632205925215371)
    ·
      refine ⟨8954993682948308887823057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969995788632205925215371 8954993682948308887823057)
      ·
        refine ⟨6716245262211231665867293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8954993682948308887823057 6716245262211231665867293)
        ·
          refine ⟨2518591973329211874700235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6716245262211231665867293 2518591973329211874700235)
          ·
            refine ⟨3777887959993817812050353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518591973329211874700235 3777887959993817812050353)
            ·
              refine ⟨2833415969995363359037765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777887959993817812050353 2833415969995363359037765)
              ·
                refine ⟨531265494374130629819581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2833415969995363359037765 531265494374130629819581)
                ·
                  refine ⟨199224560390298986182343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531265494374130629819581 199224560390298986182343)
                  ·
                    rfl

theorem cell21_872974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_872974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872974 prefixEnd_872974 := by exact prefixLift 872974
  have htrace : WordTrace (prefixWord ++ tailWord_872974) baseStart_872974 baseEnd_872974 := by
    simpa [prefixWord, tailWord_872974, baseEnd_872974] using wordTrace_append hprefix tailTrace_872974
  have hstable : (prefixWord ++ tailWord_872974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872974).length < 2 ^ (prefixWord ++ tailWord_872974).sum := by decide
  have hdescent : baseEnd_872974 < baseStart_872974 := by decide
  rcases family_descends (prefixWord ++ tailWord_872974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873002 : List Nat := [3, 1, 4, 1, 1, 3, 1, 7]
def baseStart_873002 : Nat := 118140960795 + 873002 * 2 ^ 59
def prefixEnd_873002 : Nat := 4983230072969 + 3 ^ 40 * 873002 * 2
def baseEnd_873002 : Nat := 66410316790592386571873

theorem tailTrace_873002 : CollatzResearch.WordTrace tailWord_873002 prefixEnd_873002 66410316790592386571873 := by
  unfold tailWord_873002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960249695817581429125315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21227332522180217144334173 7960249695817581429125315)
  ·
    refine ⟨11940374543726372143687973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7960249695817581429125315 11940374543726372143687973)
    ·
      refine ⟨2238820226948694776941495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11940374543726372143687973 2238820226948694776941495)
      ·
        refine ⟨3358230340423042165412243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238820226948694776941495 3358230340423042165412243)
        ·
          refine ⟨5037345510634563248118365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358230340423042165412243 5037345510634563248118365)
          ·
            refine ⟨1889004566487961218044387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5037345510634563248118365 1889004566487961218044387)
            ·
              refine ⟨2833506849731941827066581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889004566487961218044387 2833506849731941827066581)
              ·
                refine ⟨66410316790592386571873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2833506849731941827066581 66410316790592386571873)
                ·
                  rfl

theorem cell21_873002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_873002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873002 prefixEnd_873002 := by exact prefixLift 873002
  have htrace : WordTrace (prefixWord ++ tailWord_873002) baseStart_873002 baseEnd_873002 := by
    simpa [prefixWord, tailWord_873002, baseEnd_873002] using wordTrace_append hprefix tailTrace_873002
  have hstable : (prefixWord ++ tailWord_873002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873002).length < 2 ^ (prefixWord ++ tailWord_873002).sum := by decide
  have hdescent : baseEnd_873002 < baseStart_873002 := by decide
  rcases family_descends (prefixWord ++ tailWord_873002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873047 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_873047 : Nat := 118140960795 + 873047 * 2 ^ 59
def prefixEnd_873047 : Nat := 4983230072969 + 3 ^ 40 * 873047 * 2
def baseEnd_873047 : Nat := 199241219984867081465527

theorem tailTrace_873047 : CollatzResearch.WordTrace tailWord_873047 prefixEnd_873047 199241219984867081465527 := by
  unfold tailWord_873047
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842640068107298401889395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21228426712071532267926263 31842640068107298401889395)
  ·
    refine ⟨47763960102160947602834093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31842640068107298401889395 47763960102160947602834093)
    ·
      refine ⟨17911485038310355351062785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47763960102160947602834093 17911485038310355351062785)
      ·
        refine ⟨13433613778732766513297089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17911485038310355351062785 13433613778732766513297089)
        ·
          refine ⟨10075210334049574884972817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13433613778732766513297089 10075210334049574884972817)
          ·
            refine ⟨7556407750537181163729613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10075210334049574884972817 7556407750537181163729613)
            ·
              refine ⟨2833652906451442936398605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556407750537181163729613 2833652906451442936398605)
              ·
                refine ⟨1062619839919291101149477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833652906451442936398605 1062619839919291101149477)
                ·
                  refine ⟨199241219984867081465527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062619839919291101149477 199241219984867081465527)
                  ·
                    rfl

theorem cell21_873047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_873047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873047 prefixEnd_873047 := by exact prefixLift 873047
  have htrace : WordTrace (prefixWord ++ tailWord_873047) baseStart_873047 baseEnd_873047 := by
    simpa [prefixWord, tailWord_873047, baseEnd_873047] using wordTrace_append hprefix tailTrace_873047
  have hstable : (prefixWord ++ tailWord_873047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873047).length < 2 ^ (prefixWord ++ tailWord_873047).sum := by decide
  have hdescent : baseEnd_873047 < baseStart_873047 := by decide
  rcases family_descends (prefixWord ++ tailWord_873047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873075 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_873075 : Nat := 118140960795 + 873075 * 2 ^ 59
def prefixEnd_873075 : Nat := 4983230072969 + 3 ^ 40 * 873075 * 2
def baseEnd_873075 : Nat := 199247609966345254998803

theorem tailTrace_873075 : CollatzResearch.WordTrace tailWord_873075 prefixEnd_873075 199247609966345254998803 := by
  unfold tailWord_873075
  simp only [CollatzResearch.WordTrace]
  refine ⟨31843661312005859183908679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21229107541337239455939119 31843661312005859183908679)
  ·
    refine ⟨47765491968008788775863019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31843661312005859183908679 47765491968008788775863019)
    ·
      refine ⟨71648237952013183163794529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47765491968008788775863019 71648237952013183163794529)
      ·
        refine ⟨53736178464009887372845897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71648237952013183163794529 53736178464009887372845897)
        ·
          refine ⟨40302133848007415529634423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53736178464009887372845897 40302133848007415529634423)
          ·
            refine ⟨60453200772011123294451635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40302133848007415529634423 60453200772011123294451635)
            ·
              refine ⟨90679801158016684941677453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60453200772011123294451635 90679801158016684941677453)
              ·
                refine ⟨34004925434256256853129045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90679801158016684941677453 34004925434256256853129045)
                ·
                  refine ⟨199247609966345254998803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34004925434256256853129045 199247609966345254998803)
                  ·
                    rfl

theorem cell21_873075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_873075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873075 prefixEnd_873075 := by exact prefixLift 873075
  have htrace : WordTrace (prefixWord ++ tailWord_873075) baseStart_873075 baseEnd_873075 := by
    simpa [prefixWord, tailWord_873075, baseEnd_873075] using wordTrace_append hprefix tailTrace_873075
  have hstable : (prefixWord ++ tailWord_873075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873075).length < 2 ^ (prefixWord ++ tailWord_873075).sum := by decide
  have hdescent : baseEnd_873075 < baseStart_873075 := by decide
  rcases family_descends (prefixWord ++ tailWord_873075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873078 : List Nat := [5, 1, 1, 2, 3, 9]
def baseStart_873078 : Nat := 118140960795 + 873078 * 2 ^ 59
def prefixEnd_873078 : Nat := 4983230072969 + 3 ^ 40 * 873078 * 2
def baseEnd_873078 : Nat := 7379566466933996905511

theorem tailTrace_873078 : CollatzResearch.WordTrace tailWord_873078 prefixEnd_873078 7379566466933996905511 := by
  unfold tailWord_873078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990235670687186918516743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21229180487329993797511925 1990235670687186918516743)
  ·
    refine ⟨2985353506030780377775115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1990235670687186918516743 2985353506030780377775115)
    ·
      refine ⟨4478030259046170566662673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2985353506030780377775115 4478030259046170566662673)
      ·
        refine ⟨3358522694284627924997005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4478030259046170566662673 3358522694284627924997005)
        ·
          refine ⟨1259446010356735471873877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3358522694284627924997005 1259446010356735471873877)
          ·
            refine ⟨7379566466933996905511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1259446010356735471873877 7379566466933996905511)
            ·
              rfl

theorem cell21_873078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 9].length) (baseStart_873078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873078 prefixEnd_873078 := by exact prefixLift 873078
  have htrace : WordTrace (prefixWord ++ tailWord_873078) baseStart_873078 baseEnd_873078 := by
    simpa [prefixWord, tailWord_873078, baseEnd_873078] using wordTrace_append hprefix tailTrace_873078
  have hstable : (prefixWord ++ tailWord_873078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873078).length < 2 ^ (prefixWord ++ tailWord_873078).sum := by decide
  have hdescent : baseEnd_873078 < baseStart_873078 := by decide
  rcases family_descends (prefixWord ++ tailWord_873078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873213 : List Nat := [1, 4, 1, 1, 1, 1, 6, 6]
def baseStart_873213 : Nat := 118140960795 + 873213 * 2 ^ 59
def prefixEnd_873213 : Nat := 4983230072969 + 3 ^ 40 * 873213 * 2
def baseEnd_873213 : Nat := 66426367815495893899507

theorem tailTrace_873213 : CollatzResearch.WordTrace tailWord_873213 prefixEnd_873213 66426367815495893899507 := by
  unfold tailWord_873213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848694585505908752432293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21232463057003939168288195 31848694585505908752432293)
  ·
    refine ⟨5971630234782357891081055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31848694585505908752432293 5971630234782357891081055)
    ·
      refine ⟨8957445352173536836621583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971630234782357891081055 8957445352173536836621583)
      ·
        refine ⟨13436168028260305254932375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8957445352173536836621583 13436168028260305254932375)
        ·
          refine ⟨20154252042390457882398563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13436168028260305254932375 20154252042390457882398563)
          ·
            refine ⟨30231378063585686823597845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20154252042390457882398563 30231378063585686823597845)
            ·
              refine ⟨1417095846730579069856149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30231378063585686823597845 1417095846730579069856149)
              ·
                refine ⟨66426367815495893899507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1417095846730579069856149 66426367815495893899507)
                ·
                  rfl

theorem cell21_873213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_873213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873213 prefixEnd_873213 := by exact prefixLift 873213
  have htrace : WordTrace (prefixWord ++ tailWord_873213) baseStart_873213 baseEnd_873213 := by
    simpa [prefixWord, tailWord_873213, baseEnd_873213] using wordTrace_append hprefix tailTrace_873213
  have hstable : (prefixWord ++ tailWord_873213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873213).length < 2 ^ (prefixWord ++ tailWord_873213).sum := by decide
  have hdescent : baseEnd_873213 < baseStart_873213 := by decide
  rcases family_descends (prefixWord ++ tailWord_873213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873227 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_873227 : Nat := 118140960795 + 873227 * 2 ^ 59
def prefixEnd_873227 : Nat := 4983230072969 + 3 ^ 40 * 873227 * 2
def baseEnd_873227 : Nat := 199282298437226768465159

theorem tailTrace_873227 : CollatzResearch.WordTrace tailWord_873227 prefixEnd_873227 199282298437226768465159 := by
  unfold tailWord_873227
  simp only [CollatzResearch.WordTrace]
  refine ⟨31849205207455189143441935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21232803471636792762294623 31849205207455189143441935)
  ·
    refine ⟨47773807811182783715162903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31849205207455189143441935 47773807811182783715162903)
    ·
      refine ⟨71660711716774175572744355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47773807811182783715162903 71660711716774175572744355)
      ·
        refine ⟨107491067575161263359116533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71660711716774175572744355 107491067575161263359116533)
        ·
          refine ⟨10077287585171368439917175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107491067575161263359116533 10077287585171368439917175)
          ·
            refine ⟨15115931377757052659875763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077287585171368439917175 15115931377757052659875763)
            ·
              refine ⟨22673897066635578989813645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115931377757052659875763 22673897066635578989813645)
              ·
                refine ⟨8502711399988342121180117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22673897066635578989813645 8502711399988342121180117)
                ·
                  refine ⟨199282298437226768465159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8502711399988342121180117 199282298437226768465159)
                  ·
                    rfl

theorem cell21_873227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_873227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873227 prefixEnd_873227 := by exact prefixLift 873227
  have htrace : WordTrace (prefixWord ++ tailWord_873227) baseStart_873227 baseEnd_873227 := by
    simpa [prefixWord, tailWord_873227, baseEnd_873227] using wordTrace_append hprefix tailTrace_873227
  have hstable : (prefixWord ++ tailWord_873227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873227).length < 2 ^ (prefixWord ++ tailWord_873227).sum := by decide
  have hdescent : baseEnd_873227 < baseStart_873227 := by decide
  rcases family_descends (prefixWord ++ tailWord_873227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873320 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_873320 : Nat := 118140960795 + 873320 * 2 ^ 59
def prefixEnd_873320 : Nat := 4983230072969 + 3 ^ 40 * 873320 * 2
def baseEnd_873320 : Nat := 199303522304279273414969

theorem tailTrace_873320 : CollatzResearch.WordTrace tailWord_873320 prefixEnd_873320 199303522304279273414969 := by
  unfold tailWord_873320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926298598059133013288707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21235064797412177351051609 15926298598059133013288707)
  ·
    refine ⟨23889447897088699519933061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15926298598059133013288707 23889447897088699519933061)
    ·
      refine ⟨4479271480704131159987449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23889447897088699519933061 4479271480704131159987449)
      ·
        refine ⟨3359453610528098369990587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4479271480704131159987449 3359453610528098369990587)
        ·
          refine ⟨5039180415792147554985881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359453610528098369990587 5039180415792147554985881)
          ·
            refine ⟨3779385311844110666239411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5039180415792147554985881 3779385311844110666239411)
            ·
              refine ⟨5669077967766165999359117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779385311844110666239411 5669077967766165999359117)
              ·
                refine ⟨2125904237912312249759669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5669077967766165999359117 2125904237912312249759669)
                ·
                  refine ⟨199303522304279273414969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2125904237912312249759669 199303522304279273414969)
                  ·
                    rfl

theorem cell21_873320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_873320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873320 prefixEnd_873320 := by exact prefixLift 873320
  have htrace : WordTrace (prefixWord ++ tailWord_873320) baseStart_873320 baseEnd_873320 := by
    simpa [prefixWord, tailWord_873320, baseEnd_873320] using wordTrace_append hprefix tailTrace_873320
  have hstable : (prefixWord ++ tailWord_873320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873320).length < 2 ^ (prefixWord ++ tailWord_873320).sum := by decide
  have hdescent : baseEnd_873320 < baseStart_873320 := by decide
  rcases family_descends (prefixWord ++ tailWord_873320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873354 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_873354 : Nat := 118140960795 + 873354 * 2 ^ 59
def prefixEnd_873354 : Nat := 4983230072969 + 3 ^ 40 * 873354 * 2
def baseEnd_873354 : Nat := 199311281567502769848233

theorem tailTrace_873354 : CollatzResearch.WordTrace tailWord_873354 prefixEnd_873354 199311281567502769848233 := by
  unfold tailWord_873354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963459319498772458328779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21235891518663393222210077 7963459319498772458328779)
  ·
    refine ⟨11945188979248158687493169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7963459319498772458328779 11945188979248158687493169)
    ·
      refine ⟨8958891734436119015619877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11945188979248158687493169 8958891734436119015619877)
      ·
        refine ⟨1679792200206772315428727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8958891734436119015619877 1679792200206772315428727)
        ·
          refine ⟨2519688300310158473143091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679792200206772315428727 2519688300310158473143091)
          ·
            refine ⟨3779532450465237709714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519688300310158473143091 3779532450465237709714637)
            ·
              refine ⟨1417324668924464141142989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3779532450465237709714637 1417324668924464141142989)
              ·
                refine ⟨531496750846674052928621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417324668924464141142989 531496750846674052928621)
                ·
                  refine ⟨199311281567502769848233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531496750846674052928621 199311281567502769848233)
                  ·
                    rfl

theorem cell21_873354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_873354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873354 prefixEnd_873354 := by exact prefixLift 873354
  have htrace : WordTrace (prefixWord ++ tailWord_873354) baseStart_873354 baseEnd_873354 := by
    simpa [prefixWord, tailWord_873354, baseEnd_873354] using wordTrace_append hprefix tailTrace_873354
  have hstable : (prefixWord ++ tailWord_873354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873354).length < 2 ^ (prefixWord ++ tailWord_873354).sum := by decide
  have hdescent : baseEnd_873354 < baseStart_873354 := by decide
  rcases family_descends (prefixWord ++ tailWord_873354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873365 : List Nat := [1, 3, 2, 1, 1, 6, 7]
def baseStart_873365 : Nat := 118140960795 + 873365 * 2 ^ 59
def prefixEnd_873365 : Nat := 4983230072969 + 3 ^ 40 * 873365 * 2
def baseEnd_873365 : Nat := 22145976879707688351653

theorem tailTrace_873365 : CollatzResearch.WordTrace tailWord_873365 prefixEnd_873365 22145976879707688351653 := by
  unfold tailWord_873365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854238480955238711965549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21236158987303492474643699 31854238480955238711965549)
  ·
    refine ⟨11945339430358214516987081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31854238480955238711965549 11945339430358214516987081)
    ·
      refine ⟨8959004572768660887740311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11945339430358214516987081 8959004572768660887740311)
      ·
        refine ⟨13438506859152991331610467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8959004572768660887740311 13438506859152991331610467)
        ·
          refine ⟨20157760288729486997415701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438506859152991331610467 20157760288729486997415701)
          ·
            refine ⟨944895013534194703003861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20157760288729486997415701 944895013534194703003861)
            ·
              refine ⟨22145976879707688351653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 944895013534194703003861 22145976879707688351653)
              ·
                rfl

theorem cell21_873365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 7].length) (baseStart_873365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873365 prefixEnd_873365 := by exact prefixLift 873365
  have htrace : WordTrace (prefixWord ++ tailWord_873365) baseStart_873365 baseEnd_873365 := by
    simpa [prefixWord, tailWord_873365, baseEnd_873365] using wordTrace_append hprefix tailTrace_873365
  have hstable : (prefixWord ++ tailWord_873365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873365).length < 2 ^ (prefixWord ++ tailWord_873365).sum := by decide
  have hdescent : baseEnd_873365 < baseStart_873365 := by decide
  rcases family_descends (prefixWord ++ tailWord_873365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873455 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_873455 : Nat := 118140960795 + 873455 * 2 ^ 59
def prefixEnd_873455 : Nat := 4983230072969 + 3 ^ 40 * 873455 * 2
def baseEnd_873455 : Nat := 199334331143549038664693

theorem tailTrace_873455 : CollatzResearch.WordTrace tailWord_873455 prefixEnd_873455 199334331143549038664693 := by
  unfold tailWord_873455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857521050629184082741819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21238347367086122721827879 31857521050629184082741819)
  ·
    refine ⟨47786281575943776124112729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31857521050629184082741819 47786281575943776124112729)
    ·
      refine ⟨35839711181957832093084547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47786281575943776124112729 35839711181957832093084547)
      ·
        refine ⟨53759566772936748139626821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35839711181957832093084547 53759566772936748139626821)
        ·
          refine ⟨10079918769925640276180029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53759566772936748139626821 10079918769925640276180029)
          ·
            refine ⟨3779969538722115103567511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10079918769925640276180029 3779969538722115103567511)
            ·
              refine ⟨5669954308083172655351267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779969538722115103567511 5669954308083172655351267)
              ·
                refine ⟨8504931462124758983026901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669954308083172655351267 8504931462124758983026901)
                ·
                  refine ⟨199334331143549038664693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8504931462124758983026901 199334331143549038664693)
                  ·
                    rfl

theorem cell21_873455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_873455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873455 prefixEnd_873455 := by exact prefixLift 873455
  have htrace : WordTrace (prefixWord ++ tailWord_873455) baseStart_873455 baseEnd_873455 := by
    simpa [prefixWord, tailWord_873455, baseEnd_873455] using wordTrace_append hprefix tailTrace_873455
  have hstable : (prefixWord ++ tailWord_873455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873455).length < 2 ^ (prefixWord ++ tailWord_873455).sum := by decide
  have hdescent : baseEnd_873455 < baseStart_873455 := by decide
  rcases family_descends (prefixWord ++ tailWord_873455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873534 : List Nat := [4, 2, 1, 3, 1, 3, 7]
def baseStart_873534 : Nat := 118140960795 + 873534 * 2 ^ 59
def prefixEnd_873534 : Nat := 4983230072969 + 3 ^ 40 * 873534 * 2
def baseEnd_873534 : Nat := 22150262224429161871985

theorem tailTrace_873534 : CollatzResearch.WordTrace tailWord_873534 prefixEnd_873534 22150262224429161871985 := by
  unfold tailWord_873534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982550302167872571858457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21240268278228653716578437 3982550302167872571858457)
  ·
    refine ⟨2986912726625904428893843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3982550302167872571858457 2986912726625904428893843)
    ·
      refine ⟨4480369089938856643340765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986912726625904428893843 4480369089938856643340765)
      ·
        refine ⟨1680138408727071241252787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4480369089938856643340765 1680138408727071241252787)
        ·
          refine ⟨2520207613090606861879181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680138408727071241252787 2520207613090606861879181)
          ·
            refine ⟨945077854908977573204693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520207613090606861879181 945077854908977573204693)
            ·
              refine ⟨22150262224429161871985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 945077854908977573204693 22150262224429161871985)
              ·
                rfl

theorem cell21_873534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 7].length) (baseStart_873534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873534 prefixEnd_873534 := by exact prefixLift 873534
  have htrace : WordTrace (prefixWord ++ tailWord_873534) baseStart_873534 baseEnd_873534 := by
    simpa [prefixWord, tailWord_873534, baseEnd_873534] using wordTrace_append hprefix tailTrace_873534
  have hstable : (prefixWord ++ tailWord_873534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873534).length < 2 ^ (prefixWord ++ tailWord_873534).sum := by decide
  have hdescent : baseEnd_873534 < baseStart_873534 := by decide
  rcases family_descends (prefixWord ++ tailWord_873534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873593 : List Nat := [1, 2, 1, 3, 6, 8]
def baseStart_873593 : Nat := 118140960795 + 873593 * 2 ^ 59
def prefixEnd_873593 : Nat := 4983230072969 + 3 ^ 40 * 873593 * 2
def baseEnd_873593 : Nat := 7383919430507091309793

theorem tailTrace_873593 : CollatzResearch.WordTrace tailWord_873593 prefixEnd_873593 7383919430507091309793 := by
  unfold tailWord_873593
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862554324129233651265433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21241702882752822434176955 31862554324129233651265433)
  ·
    refine ⟨23896915743096925238449075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31862554324129233651265433 23896915743096925238449075)
    ·
      refine ⟨35845373614645387857673613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896915743096925238449075 35845373614645387857673613)
      ·
        refine ⟨13442015105492020446627605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35845373614645387857673613 13442015105492020446627605)
        ·
          refine ⟨630094458069938458435669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13442015105492020446627605 630094458069938458435669)
          ·
            refine ⟨7383919430507091309793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 630094458069938458435669 7383919430507091309793)
            ·
              rfl

theorem cell21_873593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 8].length) (baseStart_873593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873593 prefixEnd_873593 := by exact prefixLift 873593
  have htrace : WordTrace (prefixWord ++ tailWord_873593) baseStart_873593 baseEnd_873593 := by
    simpa [prefixWord, tailWord_873593, baseEnd_873593] using wordTrace_append hprefix tailTrace_873593
  have hstable : (prefixWord ++ tailWord_873593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873593).length < 2 ^ (prefixWord ++ tailWord_873593).sum := by decide
  have hdescent : baseEnd_873593 < baseStart_873593 := by decide
  rcases family_descends (prefixWord ++ tailWord_873593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873607 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_873607 : Nat := 118140960795 + 873607 * 2 ^ 59
def prefixEnd_873607 : Nat := 4983230072969 + 3 ^ 40 * 873607 * 2
def baseEnd_873607 : Nat := 199369019614430552131049

theorem tailTrace_873607 : CollatzResearch.WordTrace tailWord_873607 prefixEnd_873607 199369019614430552131049 := by
  unfold tailWord_873607
  simp only [CollatzResearch.WordTrace]
  refine ⟨31863064946078514042275075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21242043297385676028183383 31863064946078514042275075)
  ·
    refine ⟨47794597419117771063412613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31863064946078514042275075 47794597419117771063412613)
    ·
      refine ⟨8961487016084582074389865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47794597419117771063412613 8961487016084582074389865)
      ·
        refine ⟨6721115262063436555792399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8961487016084582074389865 6721115262063436555792399)
        ·
          refine ⟨10081672893095154833688599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721115262063436555792399 10081672893095154833688599)
          ·
            refine ⟨15122509339642732250532899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081672893095154833688599 15122509339642732250532899)
            ·
              refine ⟨22683764009464098375799349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122509339642732250532899 22683764009464098375799349)
              ·
                refine ⟨2126602875887259222731189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22683764009464098375799349 2126602875887259222731189)
                ·
                  refine ⟨199369019614430552131049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126602875887259222731189 199369019614430552131049)
                  ·
                    rfl

theorem cell21_873607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_873607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873607 prefixEnd_873607 := by exact prefixLift 873607
  have htrace : WordTrace (prefixWord ++ tailWord_873607) baseStart_873607 baseEnd_873607 := by
    simpa [prefixWord, tailWord_873607, baseEnd_873607] using wordTrace_append hprefix tailTrace_873607
  have hstable : (prefixWord ++ tailWord_873607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873607).length < 2 ^ (prefixWord ++ tailWord_873607).sum := by decide
  have hdescent : baseEnd_873607 < baseStart_873607 := by decide
  rcases family_descends (prefixWord ++ tailWord_873607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873624 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_873624 : Nat := 118140960795 + 873624 * 2 ^ 59
def prefixEnd_873624 : Nat := 4983230072969 + 3 ^ 40 * 873624 * 2
def baseEnd_873624 : Nat := 199372899246042300347681

theorem tailTrace_873624 : CollatzResearch.WordTrace tailWord_873624 prefixEnd_873624 199372899246042300347681 := by
  unfold tailWord_873624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931842493508462972821963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21242456658011283963762617 15931842493508462972821963)
  ·
    refine ⟨23897763740262694459232945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931842493508462972821963 23897763740262694459232945)
    ·
      refine ⟨17923322805197020844424709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23897763740262694459232945 17923322805197020844424709)
      ·
        refine ⟨3360623025974441408329633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17923322805197020844424709 3360623025974441408329633)
        ·
          refine ⟨2520467269480831056247225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360623025974441408329633 2520467269480831056247225)
          ·
            refine ⟨1890350452110623292185419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520467269480831056247225 1890350452110623292185419)
            ·
              refine ⟨2835525678165934938278129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890350452110623292185419 2835525678165934938278129)
              ·
                refine ⟨2126644258624451203708597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835525678165934938278129 2126644258624451203708597)
                ·
                  refine ⟨199372899246042300347681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126644258624451203708597 199372899246042300347681)
                  ·
                    rfl

theorem cell21_873624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_873624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873624 prefixEnd_873624 := by exact prefixLift 873624
  have htrace : WordTrace (prefixWord ++ tailWord_873624) baseStart_873624 baseEnd_873624 := by
    simpa [prefixWord, tailWord_873624, baseEnd_873624] using wordTrace_append hprefix tailTrace_873624
  have hstable : (prefixWord ++ tailWord_873624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873624).length < 2 ^ (prefixWord ++ tailWord_873624).sum := by decide
  have hdescent : baseEnd_873624 < baseStart_873624 := by decide
  rcases family_descends (prefixWord ++ tailWord_873624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873731 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 4]
def baseStart_873731 : Nat := 118140960795 + 873731 * 2 ^ 59
def prefixEnd_873731 : Nat := 4983230072969 + 3 ^ 40 * 873731 * 2
def baseEnd_873731 : Nat := 199397318103833892064129

theorem tailTrace_873731 : CollatzResearch.WordTrace tailWord_873731 prefixEnd_873731 199397318103833892064129 := by
  unfold tailWord_873731
  simp only [CollatzResearch.WordTrace]
  refine ⟨31867587597629283219789047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21245058398419522146526031 31867587597629283219789047)
  ·
    refine ⟨47801381396443924829683571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31867587597629283219789047 47801381396443924829683571)
    ·
      refine ⟨71702072094665887244525357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47801381396443924829683571 71702072094665887244525357)
      ·
        refine ⟨26888277035499707716697009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71702072094665887244525357 26888277035499707716697009)
        ·
          refine ⟨20166207776624780787522757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26888277035499707716697009 20166207776624780787522757)
          ·
            refine ⟨3781163958117146397660517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20166207776624780787522757 3781163958117146397660517)
            ·
              refine ⟨708968242146964949561347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3781163958117146397660517 708968242146964949561347)
              ·
                refine ⟨1063452363220447424342021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708968242146964949561347 1063452363220447424342021)
                ·
                  refine ⟨199397318103833892064129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063452363220447424342021 199397318103833892064129)
                  ·
                    rfl

theorem cell21_873731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_873731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873731 prefixEnd_873731 := by exact prefixLift 873731
  have htrace : WordTrace (prefixWord ++ tailWord_873731) baseStart_873731 baseEnd_873731 := by
    simpa [prefixWord, tailWord_873731, baseEnd_873731] using wordTrace_append hprefix tailTrace_873731
  have hstable : (prefixWord ++ tailWord_873731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873731).length < 2 ^ (prefixWord ++ tailWord_873731).sum := by decide
  have hdescent : baseEnd_873731 < baseStart_873731 := by decide
  rcases family_descends (prefixWord ++ tailWord_873731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873776 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_873776 : Nat := 118140960795 + 873776 * 2 ^ 59
def prefixEnd_873776 : Nat := 4983230072969 + 3 ^ 40 * 873776 * 2
def baseEnd_873776 : Nat := 199407587716923813814037

theorem tailTrace_873776 : CollatzResearch.WordTrace tailWord_873776 prefixEnd_873776 199407587716923813814037 := by
  unfold tailWord_873776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934614441233127952588591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21246152588310837270118121 15934614441233127952588591)
  ·
    refine ⟨23901921661849691928882887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15934614441233127952588591 23901921661849691928882887)
    ·
      refine ⟨35852882492774537893324331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23901921661849691928882887 35852882492774537893324331)
      ·
        refine ⟨53779323739161806839986497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35852882492774537893324331 53779323739161806839986497)
        ·
          refine ⟨40334492804371355129989873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53779323739161806839986497 40334492804371355129989873)
          ·
            refine ⟨30250869603278516347492405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40334492804371355129989873 30250869603278516347492405)
            ·
              refine ⟨2836019025307360907577413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30250869603278516347492405 2836019025307360907577413)
              ·
                refine ⟨531753567245130170170765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2836019025307360907577413 531753567245130170170765)
                ·
                  refine ⟨199407587716923813814037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531753567245130170170765 199407587716923813814037)
                  ·
                    rfl

theorem cell21_873776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_873776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873776 prefixEnd_873776 := by exact prefixLift 873776
  have htrace : WordTrace (prefixWord ++ tailWord_873776) baseStart_873776 baseEnd_873776 := by
    simpa [prefixWord, tailWord_873776, baseEnd_873776] using wordTrace_append hprefix tailTrace_873776
  have hstable : (prefixWord ++ tailWord_873776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873776).length < 2 ^ (prefixWord ++ tailWord_873776).sum := by decide
  have hdescent : baseEnd_873776 < baseStart_873776 := by decide
  rcases family_descends (prefixWord ++ tailWord_873776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873886 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_873886 : Nat := 118140960795 + 873886 * 2 ^ 59
def prefixEnd_873886 : Nat := 4983230072969 + 3 ^ 40 * 873886 * 2
def baseEnd_873886 : Nat := 199432691215588066980479

theorem tailTrace_873886 : CollatzResearch.WordTrace tailWord_873886 prefixEnd_873886 199432691215588066980479 := by
  unfold tailWord_873886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984155114008468086460189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21248827274711829794454341 3984155114008468086460189)
  ·
    refine ⟨1494058167753175532422571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3984155114008468086460189 1494058167753175532422571)
    ·
      refine ⟨2241087251629763298633857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494058167753175532422571 2241087251629763298633857)
      ·
        refine ⟨1680815438722322473975393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2241087251629763298633857 1680815438722322473975393)
        ·
          refine ⟨1260611579041741855481545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680815438722322473975393 1260611579041741855481545)
          ·
            refine ⟨945458684281306391611159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260611579041741855481545 945458684281306391611159)
            ·
              refine ⟨1418188026421959587416739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945458684281306391611159 1418188026421959587416739)
              ·
                refine ⟨2127282039632939381125109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418188026421959587416739 2127282039632939381125109)
                ·
                  refine ⟨199432691215588066980479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2127282039632939381125109 199432691215588066980479)
                  ·
                    rfl

theorem cell21_873886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_873886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873886 prefixEnd_873886 := by exact prefixLift 873886
  have htrace : WordTrace (prefixWord ++ tailWord_873886) baseStart_873886 baseEnd_873886 := by
    simpa [prefixWord, tailWord_873886, baseEnd_873886] using wordTrace_append hprefix tailTrace_873886
  have hstable : (prefixWord ++ tailWord_873886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873886).length < 2 ^ (prefixWord ++ tailWord_873886).sum := by decide
  have hdescent : baseEnd_873886 < baseStart_873886 := by decide
  rcases family_descends (prefixWord ++ tailWord_873886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873928 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_873928 : Nat := 118140960795 + 873928 * 2 ^ 59
def prefixEnd_873928 : Nat := 4983230072969 + 3 ^ 40 * 873928 * 2
def baseEnd_873928 : Nat := 199442276187805327280393

theorem tailTrace_873928 : CollatzResearch.WordTrace tailWord_873928 prefixEnd_873928 199442276187805327280393 := by
  unfold tailWord_873928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937386388957792932355219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21249848518610390576473625 15937386388957792932355219)
  ·
    refine ⟨23906079583436689398532829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15937386388957792932355219 23906079583436689398532829)
    ·
      refine ⟨8964779843788758524449811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23906079583436689398532829 8964779843788758524449811)
      ·
        refine ⟨13447169765683137786674717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964779843788758524449811 13447169765683137786674717)
        ·
          refine ⟨5042688662131176670003019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13447169765683137786674717 5042688662131176670003019)
          ·
            refine ⟨7564032993196765005004529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042688662131176670003019 7564032993196765005004529)
            ·
              refine ⟨5673024744897573753753397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564032993196765005004529 5673024744897573753753397)
              ·
                refine ⟨531846069834147539414381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5673024744897573753753397 531846069834147539414381)
                ·
                  refine ⟨199442276187805327280393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531846069834147539414381 199442276187805327280393)
                  ·
                    rfl

theorem cell21_873928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_873928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873928 prefixEnd_873928 := by exact prefixLift 873928
  have htrace : WordTrace (prefixWord ++ tailWord_873928) baseStart_873928 baseEnd_873928 := by
    simpa [prefixWord, tailWord_873928, baseEnd_873928] using wordTrace_append hprefix tailTrace_873928
  have hstable : (prefixWord ++ tailWord_873928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873928).length < 2 ^ (prefixWord ++ tailWord_873928).sum := by decide
  have hdescent : baseEnd_873928 < baseStart_873928 := by decide
  rcases family_descends (prefixWord ++ tailWord_873928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873945 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 3]
def baseStart_873945 : Nat := 118140960795 + 873945 * 2 ^ 59
def prefixEnd_873945 : Nat := 4983230072969 + 3 ^ 40 * 873945 * 2
def baseEnd_873945 : Nat := 199446155819417075497025

theorem tailTrace_873945 : CollatzResearch.WordTrace tailWord_873945 prefixEnd_873945 199446155819417075497025 := by
  unfold tailWord_873945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875392818853997768079289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21250261879235998512052859 31875392818853997768079289)
  ·
    refine ⟨23906544614140498326059467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31875392818853997768079289 23906544614140498326059467)
    ·
      refine ⟨35859816921210747489089201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23906544614140498326059467 35859816921210747489089201)
      ·
        refine ⟨26894862690908060616816901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35859816921210747489089201 26894862690908060616816901)
        ·
          refine ⟨5042786754545261365653169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26894862690908060616816901 5042786754545261365653169)
          ·
            refine ⟨3782090065908946024239877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042786754545261365653169 3782090065908946024239877)
            ·
              refine ⟨709141887357927379544977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3782090065908946024239877 709141887357927379544977)
              ·
                refine ⟨531856415518445534658733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709141887357927379544977 531856415518445534658733)
                ·
                  refine ⟨199446155819417075497025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531856415518445534658733 199446155819417075497025)
                  ·
                    rfl

theorem cell21_873945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_873945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_873945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_873945 prefixEnd_873945 := by exact prefixLift 873945
  have htrace : WordTrace (prefixWord ++ tailWord_873945) baseStart_873945 baseEnd_873945 := by
    simpa [prefixWord, tailWord_873945, baseEnd_873945] using wordTrace_append hprefix tailTrace_873945
  have hstable : (prefixWord ++ tailWord_873945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873945).length < 2 ^ (prefixWord ++ tailWord_873945).sum := by decide
  have hdescent : baseEnd_873945 < baseStart_873945 := by decide
  rcases family_descends (prefixWord ++ tailWord_873945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874001 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_874001 : Nat := 118140960795 + 874001 * 2 ^ 59
def prefixEnd_874001 : Nat := 4983230072969 + 3 ^ 40 * 874001 * 2
def baseEnd_874001 : Nat := 199458935782373422563577

theorem tailTrace_874001 : CollatzResearch.WordTrace tailWord_874001 prefixEnd_874001 199458935782373422563577 := by
  unfold tailWord_874001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31877435306651119332117857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21251623537767412888078571 31877435306651119332117857)
  ·
    refine ⟨23908076479988339499088393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31877435306651119332117857 23908076479988339499088393)
    ·
      refine ⟨17931057359991254624316295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23908076479988339499088393 17931057359991254624316295)
      ·
        refine ⟨26896586039986881936474443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931057359991254624316295 26896586039986881936474443)
        ·
          refine ⟨40344879059980322904711665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896586039986881936474443 40344879059980322904711665)
          ·
            refine ⟨30258659294985242178533749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40344879059980322904711665 30258659294985242178533749)
            ·
              refine ⟨2836749308904866454237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30258659294985242178533749 2836749308904866454237539)
              ·
                refine ⟨4255123963357299681356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836749308904866454237539 4255123963357299681356309)
                ·
                  refine ⟨199458935782373422563577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4255123963357299681356309 199458935782373422563577)
                  ·
                    rfl

theorem cell21_874001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_874001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874001 prefixEnd_874001 := by exact prefixLift 874001
  have htrace : WordTrace (prefixWord ++ tailWord_874001) baseStart_874001 baseEnd_874001 := by
    simpa [prefixWord, tailWord_874001, baseEnd_874001] using wordTrace_append hprefix tailTrace_874001
  have hstable : (prefixWord ++ tailWord_874001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874001).length < 2 ^ (prefixWord ++ tailWord_874001).sum := by decide
  have hdescent : baseEnd_874001 < baseStart_874001 := by decide
  rcases family_descends (prefixWord ++ tailWord_874001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874018 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_874018 : Nat := 118140960795 + 874018 * 2 ^ 59
def prefixEnd_874018 : Nat := 4983230072969 + 3 ^ 40 * 874018 * 2
def baseEnd_874018 : Nat := 199462815413985170780209

theorem tailTrace_874018 : CollatzResearch.WordTrace tailWord_874018 prefixEnd_874018 199462815413985170780209 := by
  unfold tailWord_874018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969513836897382808871677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21252036898393020823657805 7969513836897382808871677)
  ·
    refine ⟨2988567688836518553326879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7969513836897382808871677 2988567688836518553326879)
    ·
      refine ⟨4482851533254777829990319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988567688836518553326879 4482851533254777829990319)
      ·
        refine ⟨6724277299882166744985479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482851533254777829990319 6724277299882166744985479)
        ·
          refine ⟨10086415949823250117478219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724277299882166744985479 10086415949823250117478219)
          ·
            refine ⟨15129623924734875176217329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086415949823250117478219 15129623924734875176217329)
            ·
              refine ⟨11347217943551156382162997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15129623924734875176217329 11347217943551156382162997)
              ·
                refine ⟨1063801682207920910827781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11347217943551156382162997 1063801682207920910827781)
                ·
                  refine ⟨199462815413985170780209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063801682207920910827781 199462815413985170780209)
                  ·
                    rfl

theorem cell21_874018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_874018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874018 prefixEnd_874018 := by exact prefixLift 874018
  have htrace : WordTrace (prefixWord ++ tailWord_874018) baseStart_874018 baseEnd_874018 := by
    simpa [prefixWord, tailWord_874018, baseEnd_874018] using wordTrace_append hprefix tailTrace_874018
  have hstable : (prefixWord ++ tailWord_874018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874018).length < 2 ^ (prefixWord ++ tailWord_874018).sum := by decide
  have hdescent : baseEnd_874018 < baseStart_874018 := by decide
  rcases family_descends (prefixWord ++ tailWord_874018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874142 : List Nat := [4, 3, 1, 1, 1, 3, 3, 5]
def baseStart_874142 : Nat := 118140960795 + 874142 * 2 ^ 59
def prefixEnd_874142 : Nat := 4983230072969 + 3 ^ 40 * 874142 * 2
def baseEnd_874142 : Nat := 66497037967796170237763

theorem tailTrace_874142 : CollatzResearch.WordTrace tailWord_874142 prefixEnd_874142 66497037967796170237763 := by
  unfold tailWord_874142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985322249892537551625085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21255051999426866942000453 3985322249892537551625085)
  ·
    refine ⟨1494495843709701581859407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3985322249892537551625085 1494495843709701581859407)
    ·
      refine ⟨2241743765564552372789111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494495843709701581859407 2241743765564552372789111)
      ·
        refine ⟨3362615648346828559183667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241743765564552372789111 3362615648346828559183667)
        ·
          refine ⟨5043923472520242838775501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362615648346828559183667 5043923472520242838775501)
          ·
            refine ⟨1891471302195091064540813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5043923472520242838775501 1891471302195091064540813)
            ·
              refine ⟨709301738323159149202805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1891471302195091064540813 709301738323159149202805)
              ·
                refine ⟨66497037967796170237763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709301738323159149202805 66497037967796170237763)
                ·
                  rfl

theorem cell21_874142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_874142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874142 prefixEnd_874142 := by exact prefixLift 874142
  have htrace : WordTrace (prefixWord ++ tailWord_874142) baseStart_874142 baseEnd_874142 := by
    simpa [prefixWord, tailWord_874142, baseEnd_874142] using wordTrace_append hprefix tailTrace_874142
  have hstable : (prefixWord ++ tailWord_874142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874142).length < 2 ^ (prefixWord ++ tailWord_874142).sum := by decide
  have hdescent : baseEnd_874142 < baseStart_874142 := by decide
  rcases family_descends (prefixWord ++ tailWord_874142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874170 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_874170 : Nat := 118140960795 + 874170 * 2 ^ 59
def prefixEnd_874170 : Nat := 4983230072969 + 3 ^ 40 * 874170 * 2
def baseEnd_874170 : Nat := 199497503884866684246565

theorem tailTrace_874170 : CollatzResearch.WordTrace tailWord_874170 prefixEnd_874170 199497503884866684246565 := by
  unfold tailWord_874170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970899810759715298754991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21255732828692574130013309 7970899810759715298754991)
  ·
    refine ⟨11956349716139572948132487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7970899810759715298754991 11956349716139572948132487)
    ·
      refine ⟨17934524574209359422198731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11956349716139572948132487 17934524574209359422198731)
      ·
        refine ⟨26901786861314039133298097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934524574209359422198731 26901786861314039133298097)
        ·
          refine ⟨20176340145985529349973573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26901786861314039133298097 20176340145985529349973573)
          ·
            refine ⟨3783063777372286753120045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20176340145985529349973573 3783063777372286753120045)
            ·
              refine ⟨1418648916514607532420017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3783063777372286753120045 1418648916514607532420017)
              ·
                refine ⟨1063986687385955649315013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418648916514607532420017 1063986687385955649315013)
                ·
                  refine ⟨199497503884866684246565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063986687385955649315013 199497503884866684246565)
                  ·
                    rfl

theorem cell21_874170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_874170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874170 prefixEnd_874170 := by exact prefixLift 874170
  have htrace : WordTrace (prefixWord ++ tailWord_874170) baseStart_874170 baseEnd_874170 := by
    simpa [prefixWord, tailWord_874170, baseEnd_874170] using wordTrace_append hprefix tailTrace_874170
  have hstable : (prefixWord ++ tailWord_874170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874170).length < 2 ^ (prefixWord ++ tailWord_874170).sum := by decide
  have hdescent : baseEnd_874170 < baseStart_874170 := by decide
  rcases family_descends (prefixWord ++ tailWord_874170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874201 : List Nat := [1, 2, 1, 2, 3, 5, 2, 5]
def baseStart_874201 : Nat := 118140960795 + 874201 * 2 ^ 59
def prefixEnd_874201 : Nat := 4983230072969 + 3 ^ 40 * 874201 * 2
def baseEnd_874201 : Nat := 66501526169072506409945

theorem tailTrace_874201 : CollatzResearch.WordTrace tailWord_874201 prefixEnd_874201 66501526169072506409945 := by
  unfold tailWord_874201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884729905926553489398457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21256486603951035659598971 31884729905926553489398457)
  ·
    refine ⟨23913547429444915117048843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31884729905926553489398457 23913547429444915117048843)
    ·
      refine ⟨35870321144167372675573265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23913547429444915117048843 35870321144167372675573265)
      ·
        refine ⟨26902740858125529506679949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35870321144167372675573265 26902740858125529506679949)
        ·
          refine ⟨10088527821797073565004981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26902740858125529506679949 10088527821797073565004981)
          ·
            refine ⟨945799483293475646719217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10088527821797073565004981 945799483293475646719217)
            ·
              refine ⟨709349612470106735039413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945799483293475646719217 709349612470106735039413)
              ·
                refine ⟨66501526169072506409945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709349612470106735039413 66501526169072506409945)
                ·
                  rfl

theorem cell21_874201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].length) (baseStart_874201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874201 prefixEnd_874201 := by exact prefixLift 874201
  have htrace : WordTrace (prefixWord ++ tailWord_874201) baseStart_874201 baseEnd_874201 := by
    simpa [prefixWord, tailWord_874201, baseEnd_874201] using wordTrace_append hprefix tailTrace_874201
  have hstable : (prefixWord ++ tailWord_874201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874201).length < 2 ^ (prefixWord ++ tailWord_874201).sum := by decide
  have hdescent : baseEnd_874201 < baseStart_874201 := by decide
  rcases family_descends (prefixWord ++ tailWord_874201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874243 : List Nat := [1, 1, 1, 3, 2, 2, 3, 8]
def baseStart_874243 : Nat := 118140960795 + 874243 * 2 ^ 59
def prefixEnd_874243 : Nat := 4983230072969 + 3 ^ 40 * 874243 * 2
def baseEnd_874243 : Nat := 66504721159811593176583

theorem tailTrace_874243 : CollatzResearch.WordTrace tailWord_874243 prefixEnd_874243 66504721159811593176583 := by
  unfold tailWord_874243
  simp only [CollatzResearch.WordTrace]
  refine ⟨31886261771774394662427383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21257507847849596441618255 31886261771774394662427383)
  ·
    refine ⟨47829392657661591993641075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31886261771774394662427383 47829392657661591993641075)
    ·
      refine ⟨71744088986492387990461613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47829392657661591993641075 71744088986492387990461613)
      ·
        refine ⟨26904033369934645496423105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71744088986492387990461613 26904033369934645496423105)
        ·
          refine ⟨20178025027450984122317329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26904033369934645496423105 20178025027450984122317329)
          ·
            refine ⟨15133518770588238091737997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20178025027450984122317329 15133518770588238091737997)
            ·
              refine ⟨5675069538970589284401749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15133518770588238091737997 5675069538970589284401749)
              ·
                refine ⟨66504721159811593176583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5675069538970589284401749 66504721159811593176583)
                ·
                  rfl

theorem cell21_874243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_874243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874243 prefixEnd_874243 := by exact prefixLift 874243
  have htrace : WordTrace (prefixWord ++ tailWord_874243) baseStart_874243 baseEnd_874243 := by
    simpa [prefixWord, tailWord_874243, baseEnd_874243] using wordTrace_append hprefix tailTrace_874243
  have hstable : (prefixWord ++ tailWord_874243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874243).length < 2 ^ (prefixWord ++ tailWord_874243).sum := by decide
  have hdescent : baseEnd_874243 < baseStart_874243 := by decide
  rcases family_descends (prefixWord ++ tailWord_874243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874294 : List Nat := [5, 1, 2, 2, 1, 3, 1, 6]
def baseStart_874294 : Nat := 118140960795 + 874294 * 2 ^ 59
def prefixEnd_874294 : Nat := 4983230072969 + 3 ^ 40 * 874294 * 2
def baseEnd_874294 : Nat := 66508600791423341393215

theorem tailTrace_874294 : CollatzResearch.WordTrace tailWord_874294 prefixEnd_874294 66508600791423341393215 := by
  unfold tailWord_874294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993007618411851898283371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21258747929726420248355957 1993007618411851898283371)
  ·
    refine ⟨2989511427617777847425057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993007618411851898283371 2989511427617777847425057)
    ·
      refine ⟨2242133570713333385568793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989511427617777847425057 2242133570713333385568793)
      ·
        refine ⟨1681600178035000039176595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242133570713333385568793 1681600178035000039176595)
        ·
          refine ⟨2522400267052500058764893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681600178035000039176595 2522400267052500058764893)
          ·
            refine ⟨945900100144687522036835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2522400267052500058764893 945900100144687522036835)
            ·
              refine ⟨1418850150217031283055253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945900100144687522036835 1418850150217031283055253)
              ·
                refine ⟨66508600791423341393215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1418850150217031283055253 66508600791423341393215)
                ·
                  rfl

theorem cell21_874294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_874294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874294 prefixEnd_874294 := by exact prefixLift 874294
  have htrace : WordTrace (prefixWord ++ tailWord_874294) baseStart_874294 baseEnd_874294 := by
    simpa [prefixWord, tailWord_874294, baseEnd_874294] using wordTrace_append hprefix tailTrace_874294
  have hstable : (prefixWord ++ tailWord_874294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874294).length < 2 ^ (prefixWord ++ tailWord_874294).sum := by decide
  have hdescent : baseEnd_874294 < baseStart_874294 := by decide
  rcases family_descends (prefixWord ++ tailWord_874294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874339 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_874339 : Nat := 118140960795 + 874339 * 2 ^ 59
def prefixEnd_874339 : Nat := 4983230072969 + 3 ^ 40 * 874339 * 2
def baseEnd_874339 : Nat := 199536071987359945929553

theorem tailTrace_874339 : CollatzResearch.WordTrace tailWord_874339 prefixEnd_874339 199536071987359945929553 := by
  unfold tailWord_874339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889763179426603057922071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21259842119617735371948047 31889763179426603057922071)
  ·
    refine ⟨47834644769139904586883107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31889763179426603057922071 47834644769139904586883107)
    ·
      refine ⟨71751967153709856880324661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47834644769139904586883107 71751967153709856880324661)
      ·
        refine ⟨6726746920660299082530437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71751967153709856880324661 6726746920660299082530437)
        ·
          refine ⟨1261265047623806077974457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6726746920660299082530437 1261265047623806077974457)
          ·
            refine ⟨945948785717854558480843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261265047623806077974457 945948785717854558480843)
            ·
              refine ⟨1418923178576781837721265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945948785717854558480843 1418923178576781837721265)
              ·
                refine ⟨1064192383932586378290949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418923178576781837721265 1064192383932586378290949)
                ·
                  refine ⟨199536071987359945929553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064192383932586378290949 199536071987359945929553)
                  ·
                    rfl

theorem cell21_874339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_874339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874339 prefixEnd_874339 := by exact prefixLift 874339
  have htrace : WordTrace (prefixWord ++ tailWord_874339) baseStart_874339 baseEnd_874339 := by
    simpa [prefixWord, tailWord_874339, baseEnd_874339] using wordTrace_append hprefix tailTrace_874339
  have hstable : (prefixWord ++ tailWord_874339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874339).length < 2 ^ (prefixWord ++ tailWord_874339).sum := by decide
  have hdescent : baseEnd_874339 < baseStart_874339 := by decide
  rcases family_descends (prefixWord ++ tailWord_874339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874401 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 5]
def baseStart_874401 : Nat := 118140960795 + 874401 * 2 ^ 59
def prefixEnd_874401 : Nat := 4983230072969 + 3 ^ 40 * 874401 * 2
def baseEnd_874401 : Nat := 199550221232061615896093

theorem tailTrace_874401 : CollatzResearch.WordTrace tailWord_874401 prefixEnd_874401 199550221232061615896093 := by
  unfold tailWord_874401
  simp only [CollatzResearch.WordTrace]
  refine ⟨31892024505201987646679057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21261349670134658431119371 31892024505201987646679057)
  ·
    refine ⟨23919018378901490735009293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31892024505201987646679057 23919018378901490735009293)
    ·
      refine ⟨8969631892088059025628485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23919018378901490735009293 8969631892088059025628485)
      ·
        refine ⟨1681805979766511067305341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8969631892088059025628485 1681805979766511067305341)
        ·
          refine ⟨630677242412441650239503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1681805979766511067305341 630677242412441650239503)
          ·
            refine ⟨946015863618662475359255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630677242412441650239503 946015863618662475359255)
            ·
              refine ⟨1419023795427993713038883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946015863618662475359255 1419023795427993713038883)
              ·
                refine ⟨2128535693141990569558325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419023795427993713038883 2128535693141990569558325)
                ·
                  refine ⟨199550221232061615896093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2128535693141990569558325 199550221232061615896093)
                  ·
                    rfl

theorem cell21_874401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_874401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874401 prefixEnd_874401 := by exact prefixLift 874401
  have htrace : WordTrace (prefixWord ++ tailWord_874401) baseStart_874401 baseEnd_874401 := by
    simpa [prefixWord, tailWord_874401, baseEnd_874401] using wordTrace_append hprefix tailTrace_874401
  have hstable : (prefixWord ++ tailWord_874401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874401).length < 2 ^ (prefixWord ++ tailWord_874401).sum := by decide
  have hdescent : baseEnd_874401 < baseStart_874401 := by decide
  rcases family_descends (prefixWord ++ tailWord_874401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874443 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 3]
def baseStart_874443 : Nat := 118140960795 + 874443 * 2 ^ 59
def prefixEnd_874443 : Nat := 4983230072969 + 3 ^ 40 * 874443 * 2
def baseEnd_874443 : Nat := 199559806204278876196007

theorem tailTrace_874443 : CollatzResearch.WordTrace tailWord_874443 prefixEnd_874443 199559806204278876196007 := by
  unfold tailWord_874443
  simp only [CollatzResearch.WordTrace]
  refine ⟨31893556371049828819707983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21262370914033219213138655 31893556371049828819707983)
  ·
    refine ⟨47840334556574743229561975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31893556371049828819707983 47840334556574743229561975)
    ·
      refine ⟨71760501834862114844342963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47840334556574743229561975 71760501834862114844342963)
      ·
        refine ⟨107640752752293172266514445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71760501834862114844342963 107640752752293172266514445)
        ·
          refine ⟨40365282282109939599942917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107640752752293172266514445 40365282282109939599942917)
          ·
            refine ⟨7568490427895613674989297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40365282282109939599942917 7568490427895613674989297)
            ·
              refine ⟨5676367820921710256241973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7568490427895613674989297 5676367820921710256241973)
              ·
                refine ⟨532159483211410336522685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5676367820921710256241973 532159483211410336522685)
                ·
                  refine ⟨199559806204278876196007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532159483211410336522685 199559806204278876196007)
                  ·
                    rfl

theorem cell21_874443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].length) (baseStart_874443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874443 prefixEnd_874443 := by exact prefixLift 874443
  have htrace : WordTrace (prefixWord ++ tailWord_874443) baseStart_874443 baseEnd_874443 := by
    simpa [prefixWord, tailWord_874443, baseEnd_874443] using wordTrace_append hprefix tailTrace_874443
  have hstable : (prefixWord ++ tailWord_874443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874443).length < 2 ^ (prefixWord ++ tailWord_874443).sum := by decide
  have hdescent : baseEnd_874443 < baseStart_874443 := by decide
  rcases family_descends (prefixWord ++ tailWord_874443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874553 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 3]
def baseStart_874553 : Nat := 118140960795 + 874553 * 2 ^ 59
def prefixEnd_874553 : Nat := 4983230072969 + 3 ^ 40 * 874553 * 2
def baseEnd_874553 : Nat := 199584909702943129362449

theorem tailTrace_874553 : CollatzResearch.WordTrace tailWord_874553 prefixEnd_874553 199584909702943129362449 := by
  unfold tailWord_874553
  simp only [CollatzResearch.WordTrace]
  refine ⟨31897568400651317606212313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21265045600434211737474875 31897568400651317606212313)
  ·
    refine ⟨23923176300488488204659235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31897568400651317606212313 23923176300488488204659235)
    ·
      refine ⟨35884764450732732306988853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23923176300488488204659235 35884764450732732306988853)
      ·
        refine ⟨3364196667256193653780205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35884764450732732306988853 3364196667256193653780205)
        ·
          refine ⟨1261573750221072620167577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3364196667256193653780205 1261573750221072620167577)
          ·
            refine ⟨946180312665804465125683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261573750221072620167577 946180312665804465125683)
            ·
              refine ⟨1419270468998706697688525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946180312665804465125683 1419270468998706697688525)
              ·
                refine ⟨532226425874515011633197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419270468998706697688525 532226425874515011633197)
                ·
                  refine ⟨199584909702943129362449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532226425874515011633197 199584909702943129362449)
                  ·
                    rfl

theorem cell21_874553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_874553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874553 prefixEnd_874553 := by exact prefixLift 874553
  have htrace : WordTrace (prefixWord ++ tailWord_874553) baseStart_874553 baseEnd_874553 := by
    simpa [prefixWord, tailWord_874553, baseEnd_874553] using wordTrace_append hprefix tailTrace_874553
  have hstable : (prefixWord ++ tailWord_874553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874553).length < 2 ^ (prefixWord ++ tailWord_874553).sum := by decide
  have hdescent : baseEnd_874553 < baseStart_874553 := by decide
  rcases family_descends (prefixWord ++ tailWord_874553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874629 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 3]
def baseStart_874629 : Nat := 118140960795 + 874629 * 2 ^ 59
def prefixEnd_874629 : Nat := 4983230072969 + 3 ^ 40 * 874629 * 2
def baseEnd_874629 : Nat := 199602253938383886095627

theorem tailTrace_874629 : CollatzResearch.WordTrace tailWord_874629 prefixEnd_874629 199602253938383886095627 := by
  unfold tailWord_874629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900340348375982585978941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21266893565583988390652627 31900340348375982585978941)
  ·
    refine ⟨11962627630640993469742103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31900340348375982585978941 11962627630640993469742103)
    ·
      refine ⟨17943941445961490204613155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962627630640993469742103 17943941445961490204613155)
      ·
        refine ⟨26915912168942235306919733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943941445961490204613155 26915912168942235306919733)
        ·
          refine ⟨2523366765838334560023725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26915912168942235306919733 2523366765838334560023725)
          ·
            refine ⟨946262537189375460008897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523366765838334560023725 946262537189375460008897)
            ·
              refine ⟨709696902892031595006673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946262537189375460008897 709696902892031595006673)
              ·
                refine ⟨532272677169023696255005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709696902892031595006673 532272677169023696255005)
                ·
                  refine ⟨199602253938383886095627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532272677169023696255005 199602253938383886095627)
                  ·
                    rfl

theorem cell21_874629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_874629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874629 prefixEnd_874629 := by exact prefixLift 874629
  have htrace : WordTrace (prefixWord ++ tailWord_874629) baseStart_874629 baseEnd_874629 := by
    simpa [prefixWord, tailWord_874629, baseEnd_874629] using wordTrace_append hprefix tailTrace_874629
  have hstable : (prefixWord ++ tailWord_874629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874629).length < 2 ^ (prefixWord ++ tailWord_874629).sum := by decide
  have hdescent : baseEnd_874629 < baseStart_874629 := by decide
  rcases family_descends (prefixWord ++ tailWord_874629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874733 : List Nat := [1, 5, 1, 2, 4, 1, 7]
def baseStart_874733 : Nat := 118140960795 + 874733 * 2 ^ 59
def prefixEnd_874733 : Nat := 4983230072969 + 3 ^ 40 * 874733 * 2
def baseEnd_874733 : Nat := 22180665350589201818009

theorem tailTrace_874733 : CollatzResearch.WordTrace tailWord_874733 prefixEnd_874733 22180665350589201818009 := by
  unfold tailWord_874733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904133539999208347764853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21269422359999472231843235 31904133539999208347764853)
  ·
    refine ⟨2991012519374925782602955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31904133539999208347764853 2991012519374925782602955)
    ·
      refine ⟨4486518779062388673904433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991012519374925782602955 4486518779062388673904433)
      ·
        refine ⟨3364889084296791505428325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486518779062388673904433 3364889084296791505428325)
        ·
          refine ⟨630916703305648407267811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3364889084296791505428325 630916703305648407267811)
          ·
            refine ⟨946375054958472610901717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630916703305648407267811 946375054958472610901717)
            ·
              refine ⟨22180665350589201818009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 946375054958472610901717 22180665350589201818009)
              ·
                rfl

theorem cell21_874733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 7].length) (baseStart_874733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874733 prefixEnd_874733 := by exact prefixLift 874733
  have htrace : WordTrace (prefixWord ++ tailWord_874733) baseStart_874733 baseEnd_874733 := by
    simpa [prefixWord, tailWord_874733, baseEnd_874733] using wordTrace_append hprefix tailTrace_874733
  have hstable : (prefixWord ++ tailWord_874733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874733).length < 2 ^ (prefixWord ++ tailWord_874733).sum := by decide
  have hdescent : baseEnd_874733 < baseStart_874733 := by decide
  rcases family_descends (prefixWord ++ tailWord_874733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874761 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_874761 : Nat := 118140960795 + 874761 * 2 ^ 59
def prefixEnd_874761 : Nat := 4983230072969 + 3 ^ 40 * 874761 * 2
def baseEnd_874761 : Nat := 199632378136780989895357

theorem tailTrace_874761 : CollatzResearch.WordTrace tailWord_874761 prefixEnd_874761 199632378136780989895357 := by
  unfold tailWord_874761
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905154783897769129784137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21270103189265179419856091 31905154783897769129784137)
  ·
    refine ⟨23928866087923326847338103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31905154783897769129784137 23928866087923326847338103)
    ·
      refine ⟨35893299131884990271007155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23928866087923326847338103 35893299131884990271007155)
      ·
        refine ⟨53839948697827485406510733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35893299131884990271007155 53839948697827485406510733)
        ·
          refine ⟨20189980761685307027441525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53839948697827485406510733 20189980761685307027441525)
          ·
            refine ⟨1892810696407997533822643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20189980761685307027441525 1892810696407997533822643)
            ·
              refine ⟨2839216044611996300733965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892810696407997533822643 2839216044611996300733965)
              ·
                refine ⟨1064706016729498612775237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2839216044611996300733965 1064706016729498612775237)
                ·
                  refine ⟨199632378136780989895357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064706016729498612775237 199632378136780989895357)
                  ·
                    rfl

theorem cell21_874761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_874761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874761 prefixEnd_874761 := by exact prefixLift 874761
  have htrace : WordTrace (prefixWord ++ tailWord_874761) baseStart_874761 baseEnd_874761 := by
    simpa [prefixWord, tailWord_874761, baseEnd_874761] using wordTrace_append hprefix tailTrace_874761
  have hstable : (prefixWord ++ tailWord_874761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874761).length < 2 ^ (prefixWord ++ tailWord_874761).sum := by decide
  have hdescent : baseEnd_874761 < baseStart_874761 := by decide
  rcases family_descends (prefixWord ++ tailWord_874761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874775 : List Nat := [1, 1, 3, 4, 1, 2, 2, 7]
def baseStart_874775 : Nat := 118140960795 + 874775 * 2 ^ 59
def prefixEnd_874775 : Nat := 4983230072969 + 3 ^ 40 * 874775 * 2
def baseEnd_874775 : Nat := 66545191042506692220665

theorem tailTrace_874775 : CollatzResearch.WordTrace tailWord_874775 prefixEnd_874775 66545191042506692220665 := by
  unfold tailWord_874775
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905665405847049520793779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21270443603898033013862519 31905665405847049520793779)
  ·
    refine ⟨47858498108770574281190669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905665405847049520793779 47858498108770574281190669)
    ·
      refine ⟨17946936790788965355446501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47858498108770574281190669 17946936790788965355446501)
      ·
        refine ⟨3365050648272931004146219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17946936790788965355446501 3365050648272931004146219)
        ·
          refine ⟨5047575972409396506219329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365050648272931004146219 5047575972409396506219329)
          ·
            refine ⟨3785681979307047379664497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047575972409396506219329 3785681979307047379664497)
            ·
              refine ⟨2839261484480285534748373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785681979307047379664497 2839261484480285534748373)
              ·
                refine ⟨66545191042506692220665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2839261484480285534748373 66545191042506692220665)
                ·
                  rfl

theorem cell21_874775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_874775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874775 prefixEnd_874775 := by exact prefixLift 874775
  have htrace : WordTrace (prefixWord ++ tailWord_874775) baseStart_874775 baseEnd_874775 := by
    simpa [prefixWord, tailWord_874775, baseEnd_874775] using wordTrace_append hprefix tailTrace_874775
  have hstable : (prefixWord ++ tailWord_874775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874775).length < 2 ^ (prefixWord ++ tailWord_874775).sum := by decide
  have hdescent : baseEnd_874775 < baseStart_874775 := by decide
  rcases family_descends (prefixWord ++ tailWord_874775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874792 : List Nat := [2, 1, 5, 1, 4, 8]
def baseStart_874792 : Nat := 118140960795 + 874792 * 2 ^ 59
def prefixEnd_874792 : Nat := 4983230072969 + 3 ^ 40 * 874792 * 2
def baseEnd_874792 : Nat := 7394053805893771291801

theorem tailTrace_874792 : CollatzResearch.WordTrace tailWord_874792 prefixEnd_874792 7394053805893771291801 := by
  unfold tailWord_874792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15953142723392730712081315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21270856964523640949441753 15953142723392730712081315)
  ·
    refine ⟨23929714085089096068121973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15953142723392730712081315 23929714085089096068121973)
    ·
      refine ⟨2243410695477102756386435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23929714085089096068121973 2243410695477102756386435)
      ·
        refine ⟨3365116043215654134579653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243410695477102756386435 3365116043215654134579653)
        ·
          refine ⟨630959258102935150233685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3365116043215654134579653 630959258102935150233685)
          ·
            refine ⟨7394053805893771291801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 630959258102935150233685 7394053805893771291801)
            ·
              rfl

theorem cell21_874792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 8].length) (baseStart_874792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874792 prefixEnd_874792 := by exact prefixLift 874792
  have htrace : WordTrace (prefixWord ++ tailWord_874792) baseStart_874792 baseEnd_874792 := by
    simpa [prefixWord, tailWord_874792, baseEnd_874792] using wordTrace_append hprefix tailTrace_874792
  have hstable : (prefixWord ++ tailWord_874792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874792).length < 2 ^ (prefixWord ++ tailWord_874792).sum := by decide
  have hdescent : baseEnd_874792 < baseStart_874792 := by decide
  rcases family_descends (prefixWord ++ tailWord_874792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874846 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_874846 : Nat := 118140960795 + 874846 * 2 ^ 59
def prefixEnd_874846 : Nat := 4983230072969 + 3 ^ 40 * 874846 * 2
def baseEnd_874846 : Nat := 199651776294839730978517

theorem tailTrace_874846 : CollatzResearch.WordTrace tailWord_874846 prefixEnd_874846 199651776294839730978517 := by
  unfold tailWord_874846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988531873573728580828549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21272169992393219097752261 3988531873573728580828549)
  ·
    refine ⟨747849726295074108905353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3988531873573728580828549 747849726295074108905353)
    ·
      refine ⟨560887294721305581679015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747849726295074108905353 560887294721305581679015)
      ·
        refine ⟨841330942081958372518523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560887294721305581679015 841330942081958372518523)
        ·
          refine ⟨1261996413122937558777785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841330942081958372518523 1261996413122937558777785)
          ·
            refine ⟨946497309842203169083339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261996413122937558777785 946497309842203169083339)
            ·
              refine ⟨1419745964763304753625009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946497309842203169083339 1419745964763304753625009)
              ·
                refine ⟨1064809473572478565218757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419745964763304753625009 1064809473572478565218757)
                ·
                  refine ⟨199651776294839730978517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064809473572478565218757 199651776294839730978517)
                  ·
                    rfl

theorem cell21_874846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_874846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874846 prefixEnd_874846 := by exact prefixLift 874846
  have htrace : WordTrace (prefixWord ++ tailWord_874846) baseStart_874846 baseEnd_874846 := by
    simpa [prefixWord, tailWord_874846, baseEnd_874846] using wordTrace_append hprefix tailTrace_874846
  have hstable : (prefixWord ++ tailWord_874846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874846).length < 2 ^ (prefixWord ++ tailWord_874846).sum := by decide
  have hdescent : baseEnd_874846 < baseStart_874846 := by decide
  rcases family_descends (prefixWord ++ tailWord_874846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874922 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_874922 : Nat := 118140960795 + 874922 * 2 ^ 59
def prefixEnd_874922 : Nat := 4983230072969 + 3 ^ 40 * 874922 * 2
def baseEnd_874922 : Nat := 199669120530280487711695

theorem tailTrace_874922 : CollatzResearch.WordTrace tailWord_874922 prefixEnd_874922 199669120530280487711695 := by
  unfold tailWord_874922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977756734078623406598755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21274017957542995750930013 7977756734078623406598755)
  ·
    refine ⟨11966635101117935109898133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7977756734078623406598755 11966635101117935109898133)
    ·
      refine ⟨560936020364903208276475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11966635101117935109898133 560936020364903208276475)
      ·
        refine ⟨841404030547354812414713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560936020364903208276475 841404030547354812414713)
        ·
          refine ⟨631053022910516109311035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841404030547354812414713 631053022910516109311035)
          ·
            refine ⟨946579534365774163966553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631053022910516109311035 946579534365774163966553)
            ·
              refine ⟨709934650774330622974915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946579534365774163966553 709934650774330622974915)
              ·
                refine ⟨1064901976161495934462373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709934650774330622974915 1064901976161495934462373)
                ·
                  refine ⟨199669120530280487711695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064901976161495934462373 199669120530280487711695)
                  ·
                    rfl

theorem cell21_874922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_874922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874922 prefixEnd_874922 := by exact prefixLift 874922
  have htrace : WordTrace (prefixWord ++ tailWord_874922) baseStart_874922 baseEnd_874922 := by
    simpa [prefixWord, tailWord_874922, baseEnd_874922] using wordTrace_append hprefix tailTrace_874922
  have hstable : (prefixWord ++ tailWord_874922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874922).length < 2 ^ (prefixWord ++ tailWord_874922).sum := by decide
  have hdescent : baseEnd_874922 < baseStart_874922 := by decide
  rcases family_descends (prefixWord ++ tailWord_874922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874975 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 3]
def baseStart_874975 : Nat := 118140960795 + 874975 * 2 ^ 59
def prefixEnd_874975 : Nat := 4983230072969 + 3 ^ 40 * 874975 * 2
def baseEnd_874975 : Nat := 199681215852364173328253

theorem tailTrace_874975 : CollatzResearch.WordTrace tailWord_874975 prefixEnd_874975 199681215852364173328253 := by
  unfold tailWord_874975
  simp only [CollatzResearch.WordTrace]
  refine ⟨31912960005122483678074379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21275306670081655785382919 31912960005122483678074379)
  ·
    refine ⟨47869440007683725517111569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31912960005122483678074379 47869440007683725517111569)
    ·
      refine ⟨35902080005762794137833677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47869440007683725517111569 35902080005762794137833677)
      ·
        refine ⟨13463280002161047801687629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35902080005762794137833677 13463280002161047801687629)
        ·
          refine ⟨5048730000810392925632861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13463280002161047801687629 5048730000810392925632861)
          ·
            refine ⟨1893273750303897347112323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5048730000810392925632861 1893273750303897347112323)
            ·
              refine ⟨2839910625455846020668485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893273750303897347112323 2839910625455846020668485)
              ·
                refine ⟨532483242272971128875341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2839910625455846020668485 532483242272971128875341)
                ·
                  refine ⟨199681215852364173328253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532483242272971128875341 199681215852364173328253)
                  ·
                    rfl

theorem cell21_874975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].length) (baseStart_874975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874975 prefixEnd_874975 := by exact prefixLift 874975
  have htrace : WordTrace (prefixWord ++ tailWord_874975) baseStart_874975 baseEnd_874975 := by
    simpa [prefixWord, tailWord_874975, baseEnd_874975] using wordTrace_append hprefix tailTrace_874975
  have hstable : (prefixWord ++ tailWord_874975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874975).length < 2 ^ (prefixWord ++ tailWord_874975).sum := by decide
  have hdescent : baseEnd_874975 < baseStart_874975 := by decide
  rcases family_descends (prefixWord ++ tailWord_874975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874978 : List Nat := [3, 3, 3, 2, 1, 2, 1, 6]
def baseStart_874978 : Nat := 118140960795 + 874978 * 2 ^ 59
def prefixEnd_874978 : Nat := 4983230072969 + 3 ^ 40 * 874978 * 2
def baseEnd_874978 : Nat := 66560633497745611592749

theorem tailTrace_874978 : CollatzResearch.WordTrace tailWord_874978 prefixEnd_874978 66560633497745611592749 := by
  unfold tailWord_874978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978267356027903797608397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21275379616074410126955725 7978267356027903797608397)
  ·
    refine ⟨2991850258510463924103149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7978267356027903797608397 2991850258510463924103149)
    ·
      refine ⟨1121943846941423971538681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991850258510463924103149 1121943846941423971538681)
      ·
        refine ⟨841457885206067978654011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121943846941423971538681 841457885206067978654011)
        ·
          refine ⟨1262186827809101967981017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841457885206067978654011 1262186827809101967981017)
          ·
            refine ⟨946640120856826475985763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262186827809101967981017 946640120856826475985763)
            ·
              refine ⟨1419960181285239713978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946640120856826475985763 1419960181285239713978645)
              ·
                refine ⟨66560633497745611592749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1419960181285239713978645 66560633497745611592749)
                ·
                  rfl

theorem cell21_874978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_874978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_874978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_874978 prefixEnd_874978 := by exact prefixLift 874978
  have htrace : WordTrace (prefixWord ++ tailWord_874978) baseStart_874978 baseEnd_874978 := by
    simpa [prefixWord, tailWord_874978, baseEnd_874978] using wordTrace_append hprefix tailTrace_874978
  have hstable : (prefixWord ++ tailWord_874978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874978).length < 2 ^ (prefixWord ++ tailWord_874978).sum := by decide
  have hdescent : baseEnd_874978 < baseStart_874978 := by decide
  rcases family_descends (prefixWord ++ tailWord_874978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875054 : List Nat := [4, 1, 3, 1, 4, 1, 2, 5]
def baseStart_875054 : Nat := 118140960795 + 875054 * 2 ^ 59
def prefixEnd_875054 : Nat := 4983230072969 + 3 ^ 40 * 875054 * 2
def baseEnd_875054 : Nat := 66566414909559197170475

theorem tailTrace_875054 : CollatzResearch.WordTrace tailWord_875054 prefixEnd_875054 66566414909559197170475 := by
  unfold tailWord_875054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989480171479535021275027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21277227581224186780133477 3989480171479535021275027)
  ·
    refine ⟨5984220257219302531912541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989480171479535021275027 5984220257219302531912541)
    ·
      refine ⟨2244082596457238449467203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5984220257219302531912541 2244082596457238449467203)
      ·
        refine ⟨3366123894685857674200805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244082596457238449467203 3366123894685857674200805)
        ·
          refine ⟨631148230253598313912651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3366123894685857674200805 631148230253598313912651)
          ·
            refine ⟨946722345380397470868977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631148230253598313912651 946722345380397470868977)
            ·
              refine ⟨710041759035298103151733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946722345380397470868977 710041759035298103151733)
              ·
                refine ⟨66566414909559197170475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710041759035298103151733 66566414909559197170475)
                ·
                  rfl

theorem cell21_875054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_875054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875054 prefixEnd_875054 := by exact prefixLift 875054
  have htrace : WordTrace (prefixWord ++ tailWord_875054) baseStart_875054 baseEnd_875054 := by
    simpa [prefixWord, tailWord_875054, baseEnd_875054] using wordTrace_append hprefix tailTrace_875054
  have hstable : (prefixWord ++ tailWord_875054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875054).length < 2 ^ (prefixWord ++ tailWord_875054).sum := by decide
  have hdescent : baseEnd_875054 < baseStart_875054 := by decide
  rcases family_descends (prefixWord ++ tailWord_875054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875068 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_875068 : Nat := 118140960795 + 875068 * 2 ^ 59
def prefixEnd_875068 : Nat := 4983230072969 + 3 ^ 40 * 875068 * 2
def baseEnd_875068 : Nat := 199702439719416678278063

theorem tailTrace_875068 : CollatzResearch.WordTrace tailWord_875068 prefixEnd_875068 199702439719416678278063 := by
  unfold tailWord_875068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958175996892780280604929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21277567995857040374139905 15958175996892780280604929)
  ·
    refine ⟨11968631997669585210453697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15958175996892780280604929 11968631997669585210453697)
    ·
      refine ⟨8976473998252188907840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11968631997669585210453697 8976473998252188907840273)
      ·
        refine ⟨6732355498689141680880205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8976473998252188907840273 6732355498689141680880205)
        ·
          refine ⟨2524633312008428130330077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6732355498689141680880205 2524633312008428130330077)
          ·
            refine ⟨946737492003160548873779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2524633312008428130330077 946737492003160548873779)
            ·
              refine ⟨1420106238004740823310669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946737492003160548873779 1420106238004740823310669)
              ·
                refine ⟨532539839251777808741501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420106238004740823310669 532539839251777808741501)
                ·
                  refine ⟨199702439719416678278063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532539839251777808741501 199702439719416678278063)
                  ·
                    rfl

theorem cell21_875068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_875068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875068 prefixEnd_875068 := by exact prefixLift 875068
  have htrace : WordTrace (prefixWord ++ tailWord_875068) baseStart_875068 baseEnd_875068 := by
    simpa [prefixWord, tailWord_875068, baseEnd_875068] using wordTrace_append hprefix tailTrace_875068
  have hstable : (prefixWord ++ tailWord_875068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875068).length < 2 ^ (prefixWord ++ tailWord_875068).sum := by decide
  have hdescent : baseEnd_875068 < baseStart_875068 := by decide
  rcases family_descends (prefixWord ++ tailWord_875068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875079 : List Nat := [1, 1, 4, 1, 4, 3, 7]
def baseStart_875079 : Nat := 118140960795 + 875079 * 2 ^ 59
def prefixEnd_875079 : Nat := 4983230072969 + 3 ^ 40 * 875079 * 2
def baseEnd_875079 : Nat := 22189438896587011510523

theorem tailTrace_875079 : CollatzResearch.WordTrace tailWord_875079 prefixEnd_875079 22189438896587011510523 := by
  unfold tailWord_875079
  simp only [CollatzResearch.WordTrace]
  refine ⟨31916753196745709439860291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21277835464497139626573527 31916753196745709439860291)
  ·
    refine ⟨47875129795118564159790437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31916753196745709439860291 47875129795118564159790437)
    ·
      refine ⟨8976586836584730779960707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47875129795118564159790437 8976586836584730779960707)
      ·
        refine ⟨13464880254877096169941061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976586836584730779960707 13464880254877096169941061)
        ·
          refine ⟨2524665047789455531863949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13464880254877096169941061 2524665047789455531863949)
          ·
            refine ⟨946749392921045824448981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2524665047789455531863949 946749392921045824448981)
            ·
              refine ⟨22189438896587011510523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 946749392921045824448981 22189438896587011510523)
              ·
                rfl

theorem cell21_875079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 7].length) (baseStart_875079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875079 prefixEnd_875079 := by exact prefixLift 875079
  have htrace : WordTrace (prefixWord ++ tailWord_875079) baseStart_875079 baseEnd_875079 := by
    simpa [prefixWord, tailWord_875079, baseEnd_875079] using wordTrace_append hprefix tailTrace_875079
  have hstable : (prefixWord ++ tailWord_875079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875079).length < 2 ^ (prefixWord ++ tailWord_875079).sum := by decide
  have hdescent : baseEnd_875079 < baseStart_875079 := by decide
  rcases family_descends (prefixWord ++ tailWord_875079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875085 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 3]
def baseStart_875085 : Nat := 118140960795 + 875085 * 2 ^ 59
def prefixEnd_875085 : Nat := 4983230072969 + 3 ^ 40 * 875085 * 2
def baseEnd_875085 : Nat := 199706319351028426494695

theorem tailTrace_875085 : CollatzResearch.WordTrace tailWord_875085 prefixEnd_875085 199706319351028426494695 := by
  unfold tailWord_875085
  simp only [CollatzResearch.WordTrace]
  refine ⟨31916972034723972464578709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21277981356482648309719139 31916972034723972464578709)
  ·
    refine ⟨1496108064127686209277127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31916972034723972464578709 1496108064127686209277127)
    ·
      refine ⟨2244162096191529313915691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496108064127686209277127 2244162096191529313915691)
      ·
        refine ⟨3366243144287293970873537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244162096191529313915691 3366243144287293970873537)
        ·
          refine ⟨2524682358215470478155153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366243144287293970873537 2524682358215470478155153)
          ·
            refine ⟨1893511768661602858616365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524682358215470478155153 1893511768661602858616365)
            ·
              refine ⟨710066913248101071981137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1893511768661602858616365 710066913248101071981137)
              ·
                refine ⟨532550184936075803985853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710066913248101071981137 532550184936075803985853)
                ·
                  refine ⟨199706319351028426494695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532550184936075803985853 199706319351028426494695)
                  ·
                    rfl

theorem cell21_875085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_875085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875085 prefixEnd_875085 := by exact prefixLift 875085
  have htrace : WordTrace (prefixWord ++ tailWord_875085) baseStart_875085 baseEnd_875085 := by
    simpa [prefixWord, tailWord_875085, baseEnd_875085] using wordTrace_append hprefix tailTrace_875085
  have hstable : (prefixWord ++ tailWord_875085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875085).length < 2 ^ (prefixWord ++ tailWord_875085).sum := by decide
  have hdescent : baseEnd_875085 < baseStart_875085 := by decide
  rcases family_descends (prefixWord ++ tailWord_875085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875141 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_875141 : Nat := 118140960795 + 875141 * 2 ^ 59
def prefixEnd_875141 : Nat := 4983230072969 + 3 ^ 40 * 875141 * 2
def baseEnd_875141 : Nat := 199719099313984773561247

theorem tailTrace_875141 : CollatzResearch.WordTrace tailWord_875141 prefixEnd_875141 199719099313984773561247 := by
  unfold tailWord_875141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31919014522521094028617277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21279343015014062685744851 31919014522521094028617277)
  ·
    refine ⟨11969630445945410260731479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31919014522521094028617277 11969630445945410260731479)
    ·
      refine ⟨17954445668918115391097219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969630445945410260731479 17954445668918115391097219)
      ·
        refine ⟨26931668503377173086645829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17954445668918115391097219 26931668503377173086645829)
        ·
          refine ⟨5049687844383219953746093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26931668503377173086645829 5049687844383219953746093)
          ·
            refine ⟨1893632941643707482654785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5049687844383219953746093 1893632941643707482654785)
            ·
              refine ⟨1420224706232780611991089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893632941643707482654785 1420224706232780611991089)
              ·
                refine ⟨1065168529674585458993317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420224706232780611991089 1065168529674585458993317)
                ·
                  refine ⟨199719099313984773561247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065168529674585458993317 199719099313984773561247)
                  ·
                    rfl

theorem cell21_875141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_875141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875141 prefixEnd_875141 := by exact prefixLift 875141
  have htrace : WordTrace (prefixWord ++ tailWord_875141) baseStart_875141 baseEnd_875141 := by
    simpa [prefixWord, tailWord_875141, baseEnd_875141] using wordTrace_append hprefix tailTrace_875141
  have hstable : (prefixWord ++ tailWord_875141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875141).length < 2 ^ (prefixWord ++ tailWord_875141).sum := by decide
  have hdescent : baseEnd_875141 < baseStart_875141 := by decide
  rcases family_descends (prefixWord ++ tailWord_875141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875200 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_875200 : Nat := 118140960795 + 875200 * 2 ^ 59
def prefixEnd_875200 : Nat := 4983230072969 + 3 ^ 40 * 875200 * 2
def baseEnd_875200 : Nat := 199732563917813782077793

theorem tailTrace_875200 : CollatzResearch.WordTrace tailWord_875200 prefixEnd_875200 199732563917813782077793 := by
  unfold tailWord_875200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960583214653673552507527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21280777619538231403343369 15960583214653673552507527)
  ·
    refine ⟨23940874821980510328761291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15960583214653673552507527 23940874821980510328761291)
    ·
      refine ⟨35911312232970765493141937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23940874821980510328761291 35911312232970765493141937)
      ·
        refine ⟨26933484174728074119856453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35911312232970765493141937 26933484174728074119856453)
        ·
          refine ⟨5050028282761513897473085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26933484174728074119856453 5050028282761513897473085)
          ·
            refine ⟨1893760606035567711552407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5050028282761513897473085 1893760606035567711552407)
            ·
              refine ⟨2840640909053351567328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893760606035567711552407 2840640909053351567328611)
              ·
                refine ⟨4260961363580027350992917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840640909053351567328611 4260961363580027350992917)
                ·
                  refine ⟨199732563917813782077793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4260961363580027350992917 199732563917813782077793)
                  ·
                    rfl

theorem cell21_875200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_875200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875200 prefixEnd_875200 := by exact prefixLift 875200
  have htrace : WordTrace (prefixWord ++ tailWord_875200) baseStart_875200 baseEnd_875200 := by
    simpa [prefixWord, tailWord_875200, baseEnd_875200] using wordTrace_append hprefix tailTrace_875200
  have hstable : (prefixWord ++ tailWord_875200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875200).length < 2 ^ (prefixWord ++ tailWord_875200).sum := by decide
  have hdescent : baseEnd_875200 < baseStart_875200 := by decide
  rcases family_descends (prefixWord ++ tailWord_875200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875217 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 4]
def baseStart_875217 : Nat := 118140960795 + 875217 * 2 ^ 59
def prefixEnd_875217 : Nat := 4983230072969 + 3 ^ 40 * 875217 * 2
def baseEnd_875217 : Nat := 199736443549425530294425

theorem tailTrace_875217 : CollatzResearch.WordTrace tailWord_875217 prefixEnd_875217 199736443549425530294425 := by
  unfold tailWord_875217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921786470245759008383905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21281190980163839338922603 31921786470245759008383905)
  ·
    refine ⟨23941339852684319256287929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31921786470245759008383905 23941339852684319256287929)
    ·
      refine ⟨17956004889513239442215947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23941339852684319256287929 17956004889513239442215947)
      ·
        refine ⟨26934007334269859163323921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17956004889513239442215947 26934007334269859163323921)
        ·
          refine ⟨20200505500702394372492941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26934007334269859163323921 20200505500702394372492941)
          ·
            refine ⟨7575189562763397889684853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20200505500702394372492941 7575189562763397889684853)
            ·
              refine ⟨710174021509068552157955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7575189562763397889684853 710174021509068552157955)
              ·
                refine ⟨1065261032263602828236933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710174021509068552157955 1065261032263602828236933)
                ·
                  refine ⟨199736443549425530294425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065261032263602828236933 199736443549425530294425)
                  ·
                    rfl

theorem cell21_875217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_875217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875217 prefixEnd_875217 := by exact prefixLift 875217
  have htrace : WordTrace (prefixWord ++ tailWord_875217) baseStart_875217 baseEnd_875217 := by
    simpa [prefixWord, tailWord_875217, baseEnd_875217] using wordTrace_append hprefix tailTrace_875217
  have hstable : (prefixWord ++ tailWord_875217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875217).length < 2 ^ (prefixWord ++ tailWord_875217).sum := by decide
  have hdescent : baseEnd_875217 < baseStart_875217 := by decide
  rcases family_descends (prefixWord ++ tailWord_875217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875231 : List Nat := [1, 1, 2, 3, 2, 3, 4, 5]
def baseStart_875231 : Nat := 118140960795 + 875231 * 2 ^ 59
def prefixEnd_875231 : Nat := 4983230072969 + 3 ^ 40 * 875231 * 2
def baseEnd_875231 : Nat := 66579879513388205687021

theorem tailTrace_875231 : CollatzResearch.WordTrace tailWord_875231 prefixEnd_875231 66579879513388205687021 := by
  unfold tailWord_875231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31922297092195039399393547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21281531394796692932929031 31922297092195039399393547)
  ·
    refine ⟨47883445638292559099090321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31922297092195039399393547 47883445638292559099090321)
    ·
      refine ⟨35912584228719419324317741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47883445638292559099090321 35912584228719419324317741)
      ·
        refine ⟨13467219085769782246619153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35912584228719419324317741 13467219085769782246619153)
        ·
          refine ⟨10100414314327336684964365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467219085769782246619153 10100414314327336684964365)
          ·
            refine ⟨3787655367872751256861637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10100414314327336684964365 3787655367872751256861637)
            ·
              refine ⟨710185381476140860661557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3787655367872751256861637 710185381476140860661557)
              ·
                refine ⟨66579879513388205687021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710185381476140860661557 66579879513388205687021)
                ·
                  rfl

theorem cell21_875231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].length) (baseStart_875231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875231 prefixEnd_875231 := by exact prefixLift 875231
  have htrace : WordTrace (prefixWord ++ tailWord_875231) baseStart_875231 baseEnd_875231 := by
    simpa [prefixWord, tailWord_875231, baseEnd_875231] using wordTrace_append hprefix tailTrace_875231
  have hstable : (prefixWord ++ tailWord_875231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875231).length < 2 ^ (prefixWord ++ tailWord_875231).sum := by decide
  have hdescent : baseEnd_875231 < baseStart_875231 := by decide
  rcases family_descends (prefixWord ++ tailWord_875231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875290 : List Nat := [3, 1, 1, 3, 2, 1, 1, 9]
def baseStart_875290 : Nat := 118140960795 + 875290 * 2 ^ 59
def prefixEnd_875290 : Nat := 4983230072969 + 3 ^ 40 * 875290 * 2
def baseEnd_875290 : Nat := 66584367714664541859203

theorem tailTrace_875290 : CollatzResearch.WordTrace tailWord_875290 prefixEnd_875290 66584367714664541859203 := by
  unfold tailWord_875290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981112249745323118947831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21282965999320861650527549 7981112249745323118947831)
  ·
    refine ⟨11971668374617984678421747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7981112249745323118947831 11971668374617984678421747)
    ·
      refine ⟨17957502561926977017632621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11971668374617984678421747 17957502561926977017632621)
      ·
        refine ⟨6734063460722616381612233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17957502561926977017632621 6734063460722616381612233)
        ·
          refine ⟨5050547595541962286209175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6734063460722616381612233 5050547595541962286209175)
          ·
            refine ⟨7575821393312943429313763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050547595541962286209175 7575821393312943429313763)
            ·
              refine ⟨11363732089969415143970645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575821393312943429313763 11363732089969415143970645)
              ·
                refine ⟨66584367714664541859203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11363732089969415143970645 66584367714664541859203)
                ·
                  rfl

theorem cell21_875290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_875290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875290 prefixEnd_875290 := by exact prefixLift 875290
  have htrace : WordTrace (prefixWord ++ tailWord_875290) baseStart_875290 baseEnd_875290 := by
    simpa [prefixWord, tailWord_875290, baseEnd_875290] using wordTrace_append hprefix tailTrace_875290
  have hstable : (prefixWord ++ tailWord_875290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875290).length < 2 ^ (prefixWord ++ tailWord_875290).sum := by decide
  have hdescent : baseEnd_875290 < baseStart_875290 := by decide
  rcases family_descends (prefixWord ++ tailWord_875290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875310 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_875310 : Nat := 118140960795 + 875310 * 2 ^ 59
def prefixEnd_875310 : Nat := 4983230072969 + 3 ^ 40 * 875310 * 2
def baseEnd_875310 : Nat := 199757667416478035244235

theorem tailTrace_875310 : CollatzResearch.WordTrace tailWord_875310 prefixEnd_875310 199757667416478035244235 := by
  unfold tailWord_875310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990647307363604486439923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21283452305939223927679589 3990647307363604486439923)
  ·
    refine ⟨5985970961045406729659885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990647307363604486439923 5985970961045406729659885)
    ·
      refine ⟨2244739110392027523622457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5985970961045406729659885 2244739110392027523622457)
      ·
        refine ⟨1683554332794020642716843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244739110392027523622457 1683554332794020642716843)
        ·
          refine ⟨2525331499191030964075265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683554332794020642716843 2525331499191030964075265)
          ·
            refine ⟨1893998624393273223056449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525331499191030964075265 1893998624393273223056449)
            ·
              refine ⟨1420498968294954917292337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893998624393273223056449 1420498968294954917292337)
              ·
                refine ⟨1065374226221216187969253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420498968294954917292337 1065374226221216187969253)
                ·
                  refine ⟨199757667416478035244235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065374226221216187969253 199757667416478035244235)
                  ·
                    rfl

theorem cell21_875310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_875310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875310 prefixEnd_875310 := by exact prefixLift 875310
  have htrace : WordTrace (prefixWord ++ tailWord_875310) baseStart_875310 baseEnd_875310 := by
    simpa [prefixWord, tailWord_875310, baseEnd_875310] using wordTrace_append hprefix tailTrace_875310
  have hstable : (prefixWord ++ tailWord_875310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875310).length < 2 ^ (prefixWord ++ tailWord_875310).sum := by decide
  have hdescent : baseEnd_875310 < baseStart_875310 := by decide
  rcases family_descends (prefixWord ++ tailWord_875310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875335 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_875335 : Nat := 118140960795 + 875335 * 2 ^ 59
def prefixEnd_875335 : Nat := 4983230072969 + 3 ^ 40 * 875335 * 2
def baseEnd_875335 : Nat := 199763372757083547327517

theorem tailTrace_875335 : CollatzResearch.WordTrace tailWord_875335 prefixEnd_875335 199763372757083547327517 := by
  unfold tailWord_875335
  simp only [CollatzResearch.WordTrace]
  refine ⟨31926090283818265161179459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21284060189212176774119639 31926090283818265161179459)
  ·
    refine ⟨47889135425727397741769189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31926090283818265161179459 47889135425727397741769189)
    ·
      refine ⟨8979212892323887076581723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47889135425727397741769189 8979212892323887076581723)
      ·
        refine ⟨13468819338485830614872585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979212892323887076581723 13468819338485830614872585)
        ·
          refine ⟨10101614503864372961154439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13468819338485830614872585 10101614503864372961154439)
          ·
            refine ⟨15152421755796559441731659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101614503864372961154439 15152421755796559441731659)
            ·
              refine ⟨22728632633694839162597489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15152421755796559441731659 22728632633694839162597489)
              ·
                refine ⟨17046474475271129371948117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22728632633694839162597489 17046474475271129371948117)
                ·
                  refine ⟨199763372757083547327517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17046474475271129371948117 199763372757083547327517)
                  ·
                    rfl

theorem cell21_875335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_875335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875335 prefixEnd_875335 := by exact prefixLift 875335
  have htrace : WordTrace (prefixWord ++ tailWord_875335) baseStart_875335 baseEnd_875335 := by
    simpa [prefixWord, tailWord_875335, baseEnd_875335] using wordTrace_append hprefix tailTrace_875335
  have hstable : (prefixWord ++ tailWord_875335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875335).length < 2 ^ (prefixWord ++ tailWord_875335).sum := by decide
  have hdescent : baseEnd_875335 < baseStart_875335 := by decide
  rcases family_descends (prefixWord ++ tailWord_875335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875341 : List Nat := [1, 6, 1, 2, 2, 1, 3, 5]
def baseStart_875341 : Nat := 118140960795 + 875341 * 2 ^ 59
def prefixEnd_875341 : Nat := 4983230072969 + 3 ^ 40 * 875341 * 2
def baseEnd_875341 : Nat := 66588247346276290075835

theorem tailTrace_875341 : CollatzResearch.WordTrace tailWord_875341 prefixEnd_875341 66588247346276290075835 := by
  unfold tailWord_875341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31926309121796528185897877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21284206081197685457265251 31926309121796528185897877)
  ·
    refine ⟨1496545740084212258713963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31926309121796528185897877 1496545740084212258713963)
    ·
      refine ⟨2244818610126318388070945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496545740084212258713963 2244818610126318388070945)
      ·
        refine ⟨1683613957594738791053209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244818610126318388070945 1683613957594738791053209)
        ·
          refine ⟨1262710468196054093289907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683613957594738791053209 1262710468196054093289907)
          ·
            refine ⟨1894065702294081139934861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262710468196054093289907 1894065702294081139934861)
            ·
              refine ⟨710274638360280427475573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1894065702294081139934861 710274638360280427475573)
              ·
                refine ⟨66588247346276290075835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710274638360280427475573 66588247346276290075835)
                ·
                  rfl

theorem cell21_875341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].length) (baseStart_875341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875341 prefixEnd_875341 := by exact prefixLift 875341
  have htrace : WordTrace (prefixWord ++ tailWord_875341) baseStart_875341 baseEnd_875341 := by
    simpa [prefixWord, tailWord_875341, baseEnd_875341] using wordTrace_append hprefix tailTrace_875341
  have hstable : (prefixWord ++ tailWord_875341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875341).length < 2 ^ (prefixWord ++ tailWord_875341).sum := by decide
  have hdescent : baseEnd_875341 < baseStart_875341 := by decide
  rcases family_descends (prefixWord ++ tailWord_875341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875397 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_875397 : Nat := 118140960795 + 875397 * 2 ^ 59
def prefixEnd_875397 : Nat := 4983230072969 + 3 ^ 40 * 875397 * 2
def baseEnd_875397 : Nat := 199777522001785217294057

theorem tailTrace_875397 : CollatzResearch.WordTrace tailWord_875397 prefixEnd_875397 199777522001785217294057 := by
  unfold tailWord_875397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928351609593649749936445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21285567739729099833290963 31928351609593649749936445)
  ·
    refine ⟨11973131853597618656226167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31928351609593649749936445 11973131853597618656226167)
    ·
      refine ⟨17959697780396427984339251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973131853597618656226167 17959697780396427984339251)
      ·
        refine ⟨26939546670594641976508877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959697780396427984339251 26939546670594641976508877)
        ·
          refine ⟨10102330001472990741190829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26939546670594641976508877 10102330001472990741190829)
          ·
            refine ⟨3788373750552371527946561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10102330001472990741190829 3788373750552371527946561)
            ·
              refine ⟨2841280312914278645959921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788373750552371527946561 2841280312914278645959921)
              ·
                refine ⟨2130960234685708984469941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841280312914278645959921 2130960234685708984469941)
                ·
                  refine ⟨199777522001785217294057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130960234685708984469941 199777522001785217294057)
                  ·
                    rfl

theorem cell21_875397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_875397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875397 prefixEnd_875397 := by exact prefixLift 875397
  have htrace : WordTrace (prefixWord ++ tailWord_875397) baseStart_875397 baseEnd_875397 := by
    simpa [prefixWord, tailWord_875397, baseEnd_875397] using wordTrace_append hprefix tailTrace_875397
  have hstable : (prefixWord ++ tailWord_875397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875397).length < 2 ^ (prefixWord ++ tailWord_875397).sum := by decide
  have hdescent : baseEnd_875397 < baseStart_875397 := by decide
  rcases family_descends (prefixWord ++ tailWord_875397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875400 : List Nat := [2, 1, 3, 3, 2, 3, 2, 5]
def baseStart_875400 : Nat := 118140960795 + 875400 * 2 ^ 59
def prefixEnd_875400 : Nat := 4983230072969 + 3 ^ 40 * 875400 * 2
def baseEnd_875400 : Nat := 66592735547552626248017

theorem tailTrace_875400 : CollatzResearch.WordTrace tailWord_875400 prefixEnd_875400 66592735547552626248017 := by
  unfold tailWord_875400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964230514291390631147827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21285640685721854174863769 15964230514291390631147827)
  ·
    refine ⟨23946345771437085946721741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15964230514291390631147827 23946345771437085946721741)
    ·
      refine ⟨8979879664288907230020653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23946345771437085946721741 8979879664288907230020653)
      ·
        refine ⟨3367454874108340211257745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8979879664288907230020653 3367454874108340211257745)
        ·
          refine ⟨2525591155581255158443309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367454874108340211257745 2525591155581255158443309)
          ·
            refine ⟨947096683342970684416241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2525591155581255158443309 947096683342970684416241)
            ·
              refine ⟨710322512507228013312181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947096683342970684416241 710322512507228013312181)
              ·
                refine ⟨66592735547552626248017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710322512507228013312181 66592735547552626248017)
                ·
                  rfl

theorem cell21_875400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_875400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875400 prefixEnd_875400 := by exact prefixLift 875400
  have htrace : WordTrace (prefixWord ++ tailWord_875400) baseStart_875400 baseEnd_875400 := by
    simpa [prefixWord, tailWord_875400, baseEnd_875400] using wordTrace_append hprefix tailTrace_875400
  have hstable : (prefixWord ++ tailWord_875400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875400).length < 2 ^ (prefixWord ++ tailWord_875400).sum := by decide
  have hdescent : baseEnd_875400 < baseStart_875400 := by decide
  rcases family_descends (prefixWord ++ tailWord_875400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875428 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_875428 : Nat := 118140960795 + 875428 * 2 ^ 59
def prefixEnd_875428 : Nat := 4983230072969 + 3 ^ 40 * 875428 * 2
def baseEnd_875428 : Nat := 199784596624136052277327

theorem tailTrace_875428 : CollatzResearch.WordTrace tailWord_875428 prefixEnd_875428 199784596624136052277327 := by
  unfold tailWord_875428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964741136240671022157469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21286321514987561362876625 15964741136240671022157469)
  ·
    refine ⟨5986777926090251633309051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15964741136240671022157469 5986777926090251633309051)
    ·
      refine ⟨8980166889135377449963577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986777926090251633309051 8980166889135377449963577)
      ·
        refine ⟨6735125166851533087472683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8980166889135377449963577 6735125166851533087472683)
        ·
          refine ⟨10102687750277299631209025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735125166851533087472683 10102687750277299631209025)
          ·
            refine ⟨7577015812707974723406769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10102687750277299631209025 7577015812707974723406769)
            ·
              refine ⟨5682761859530981042555077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7577015812707974723406769 5682761859530981042555077)
              ·
                refine ⟨1065517848662058945479077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5682761859530981042555077 1065517848662058945479077)
                ·
                  refine ⟨199784596624136052277327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065517848662058945479077 199784596624136052277327)
                  ·
                    rfl

theorem cell21_875428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_875428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875428 prefixEnd_875428 := by exact prefixLift 875428
  have htrace : WordTrace (prefixWord ++ tailWord_875428) baseStart_875428 baseEnd_875428 := by
    simpa [prefixWord, tailWord_875428, baseEnd_875428] using wordTrace_append hprefix tailTrace_875428
  have hstable : (prefixWord ++ tailWord_875428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875428).length < 2 ^ (prefixWord ++ tailWord_875428).sum := by decide
  have hdescent : baseEnd_875428 < baseStart_875428 := by decide
  rcases family_descends (prefixWord ++ tailWord_875428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875431 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_875431 : Nat := 118140960795 + 875431 * 2 ^ 59
def prefixEnd_875431 : Nat := 4983230072969 + 3 ^ 40 * 875431 * 2
def baseEnd_875431 : Nat := 199785281265008713727321

theorem tailTrace_875431 : CollatzResearch.WordTrace tailWord_875431 prefixEnd_875431 199785281265008713727321 := by
  unfold tailWord_875431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929591691470473556674147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21286394460980315704449431 31929591691470473556674147)
  ·
    refine ⟨47894387537205710335011221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929591691470473556674147 47894387537205710335011221)
    ·
      refine ⟨2245049415806517671953651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47894387537205710335011221 2245049415806517671953651)
      ·
        refine ⟨3367574123709776507930477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245049415806517671953651 3367574123709776507930477)
        ·
          refine ⟨1262840296391166190473929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3367574123709776507930477 1262840296391166190473929)
          ·
            refine ⟨947130222293374642855447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262840296391166190473929 947130222293374642855447)
            ·
              refine ⟨1420695333440061964283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947130222293374642855447 1420695333440061964283171)
              ·
                refine ⟨2131043000160092946424757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420695333440061964283171 2131043000160092946424757)
                ·
                  refine ⟨199785281265008713727321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2131043000160092946424757 199785281265008713727321)
                  ·
                    rfl

theorem cell21_875431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_875431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875431 prefixEnd_875431 := by exact prefixLift 875431
  have htrace : WordTrace (prefixWord ++ tailWord_875431) baseStart_875431 baseEnd_875431 := by
    simpa [prefixWord, tailWord_875431, baseEnd_875431] using wordTrace_append hprefix tailTrace_875431
  have hstable : (prefixWord ++ tailWord_875431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875431).length < 2 ^ (prefixWord ++ tailWord_875431).sum := by decide
  have hdescent : baseEnd_875431 < baseStart_875431 := by decide
  rcases family_descends (prefixWord ++ tailWord_875431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875493 : List Nat := [1, 3, 1, 6, 2, 1, 1, 6]
def baseStart_875493 : Nat := 118140960795 + 875493 * 2 ^ 59
def prefixEnd_875493 : Nat := 4983230072969 + 3 ^ 40 * 875493 * 2
def baseEnd_875493 : Nat := 66599810169903461231287

theorem tailTrace_875493 : CollatzResearch.WordTrace tailWord_875493 prefixEnd_875493 66599810169903461231287 := by
  unfold tailWord_875493
  simp only [CollatzResearch.WordTrace]
  refine ⟨31931853017245858145431133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21287902011497238763620755 31931853017245858145431133)
  ·
    refine ⟨11974444881467196804536675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31931853017245858145431133 11974444881467196804536675)
    ·
      refine ⟨17961667322200795206805013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974444881467196804536675 17961667322200795206805013)
      ·
        refine ⟨841953155728162275318985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17961667322200795206805013 841953155728162275318985)
        ·
          refine ⟨631464866796121706489239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841953155728162275318985 631464866796121706489239)
          ·
            refine ⟨947197300194182559733859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631464866796121706489239 947197300194182559733859)
            ·
              refine ⟨1420795950291273839600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947197300194182559733859 1420795950291273839600789)
              ·
                refine ⟨66599810169903461231287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1420795950291273839600789 66599810169903461231287)
                ·
                  rfl

theorem cell21_875493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].length) (baseStart_875493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875493 prefixEnd_875493 := by exact prefixLift 875493
  have htrace : WordTrace (prefixWord ++ tailWord_875493) baseStart_875493 baseEnd_875493 := by
    simpa [prefixWord, tailWord_875493, baseEnd_875493] using wordTrace_append hprefix tailTrace_875493
  have hstable : (prefixWord ++ tailWord_875493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875493).length < 2 ^ (prefixWord ++ tailWord_875493).sum := by decide
  have hdescent : baseEnd_875493 < baseStart_875493 := by decide
  rcases family_descends (prefixWord ++ tailWord_875493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875653 : List Nat := [1, 3, 1, 1, 15]
def baseStart_875653 : Nat := 118140960795 + 875653 * 2 ^ 59
def prefixEnd_875653 : Nat := 4983230072969 + 3 ^ 40 * 875653 * 2
def baseEnd_875653 : Nat := 2467110428266489642307

theorem tailTrace_875653 : CollatzResearch.WordTrace tailWord_875653 prefixEnd_875653 2467110428266489642307 := by
  unfold tailWord_875653
  simp only [CollatzResearch.WordTrace]
  refine ⟨31937688696666205471255613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21291792464444136980837075 31937688696666205471255613)
  ·
    refine ⟨11976633261249827051720855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31937688696666205471255613 11976633261249827051720855)
    ·
      refine ⟨17964949891874740577581283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11976633261249827051720855 17964949891874740577581283)
      ·
        refine ⟨26947424837812110866371925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17964949891874740577581283 26947424837812110866371925)
        ·
          refine ⟨2467110428266489642307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 26947424837812110866371925 2467110428266489642307)
          ·
            rfl

theorem cell21_875653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 15].length) (baseStart_875653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875653 prefixEnd_875653 := by exact prefixLift 875653
  have htrace : WordTrace (prefixWord ++ tailWord_875653) baseStart_875653 baseEnd_875653 := by
    simpa [prefixWord, tailWord_875653, baseEnd_875653] using wordTrace_append hprefix tailTrace_875653
  have hstable : (prefixWord ++ tailWord_875653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875653).length < 2 ^ (prefixWord ++ tailWord_875653).sum := by decide
  have hdescent : baseEnd_875653 < baseStart_875653 := by decide
  rcases family_descends (prefixWord ++ tailWord_875653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875715 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_875715 : Nat := 118140960795 + 875715 * 2 ^ 59
def prefixEnd_875715 : Nat := 4983230072969 + 3 ^ 40 * 875715 * 2
def baseEnd_875715 : Nat := 199850093934287330993407

theorem tailTrace_875715 : CollatzResearch.WordTrace tailWord_875715 prefixEnd_875715 199850093934287330993407 := by
  unfold tailWord_875715
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939950022441590060012599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21293300014961060040008399 31939950022441590060012599)
  ·
    refine ⟨47909925033662385090018899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31939950022441590060012599 47909925033662385090018899)
    ·
      refine ⟨71864887550493577635028349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47909925033662385090018899 71864887550493577635028349)
      ·
        refine ⟨26949332831435091613135631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71864887550493577635028349 26949332831435091613135631)
        ·
          refine ⟨40423999247152637419703447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26949332831435091613135631 40423999247152637419703447)
          ·
            refine ⟨60635998870728956129555171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40423999247152637419703447 60635998870728956129555171)
            ·
              refine ⟨90953998306093434194332757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60635998870728956129555171 90953998306093434194332757)
              ·
                refine ⟨1065867167649532431964837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 90953998306093434194332757 1065867167649532431964837)
                ·
                  refine ⟨199850093934287330993407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065867167649532431964837 199850093934287330993407)
                  ·
                    rfl

theorem cell21_875715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_875715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875715 prefixEnd_875715 := by exact prefixLift 875715
  have htrace : WordTrace (prefixWord ++ tailWord_875715) baseStart_875715 baseEnd_875715 := by
    simpa [prefixWord, tailWord_875715, baseEnd_875715] using wordTrace_append hprefix tailTrace_875715
  have hstable : (prefixWord ++ tailWord_875715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875715).length < 2 ^ (prefixWord ++ tailWord_875715).sum := by decide
  have hdescent : baseEnd_875715 < baseStart_875715 := by decide
  rcases family_descends (prefixWord ++ tailWord_875715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875729 : List Nat := [1, 2, 2, 1, 2, 2, 1, 10]
def baseStart_875729 : Nat := 118140960795 + 875729 * 2 ^ 59
def prefixEnd_875729 : Nat := 4983230072969 + 3 ^ 40 * 875729 * 2
def baseEnd_875729 : Nat := 66617762975008805920015

theorem tailTrace_875729 : CollatzResearch.WordTrace tailWord_875729 prefixEnd_875729 66617762975008805920015 := by
  unfold tailWord_875729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31940460644390870451022241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21293640429593913634014827 31940460644390870451022241)
  ·
    refine ⟨23955345483293152838266681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31940460644390870451022241 23955345483293152838266681)
    ·
      refine ⟨17966509112469864628700011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23955345483293152838266681 17966509112469864628700011)
      ·
        refine ⟨26949763668704796943050017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17966509112469864628700011 26949763668704796943050017)
        ·
          refine ⟨20212322751528597707287513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26949763668704796943050017 20212322751528597707287513)
          ·
            refine ⟨15159242063646448280465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20212322751528597707287513 15159242063646448280465635)
            ·
              refine ⟨22738863095469672420698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15159242063646448280465635 22738863095469672420698453)
              ·
                refine ⟨66617762975008805920015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22738863095469672420698453 66617762975008805920015)
                ·
                  rfl

theorem cell21_875729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_875729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875729 prefixEnd_875729 := by exact prefixLift 875729
  have htrace : WordTrace (prefixWord ++ tailWord_875729) baseStart_875729 baseEnd_875729 := by
    simpa [prefixWord, tailWord_875729, baseEnd_875729] using wordTrace_append hprefix tailTrace_875729
  have hstable : (prefixWord ++ tailWord_875729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875729).length < 2 ^ (prefixWord ++ tailWord_875729).sum := by decide
  have hdescent : baseEnd_875729 < baseStart_875729 := by decide
  rcases family_descends (prefixWord ++ tailWord_875729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875777 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_875777 : Nat := 118140960795 + 875777 * 2 ^ 59
def prefixEnd_875777 : Nat := 4983230072969 + 3 ^ 40 * 875777 * 2
def baseEnd_875777 : Nat := 199864243178989000959947

theorem tailTrace_875777 : CollatzResearch.WordTrace tailWord_875777 prefixEnd_875777 199864243178989000959947 := by
  unfold tailWord_875777
  simp only [CollatzResearch.WordTrace]
  refine ⟨31942211348216974648769585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21294807565477983099179723 31942211348216974648769585)
  ·
    refine ⟨23956658511162730986577189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31942211348216974648769585 23956658511162730986577189)
    ·
      refine ⟨4491873470843012059983223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23956658511162730986577189 4491873470843012059983223)
      ·
        refine ⟨6737810206264518089974835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491873470843012059983223 6737810206264518089974835)
        ·
          refine ⟨10106715309396777134962253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737810206264518089974835 10106715309396777134962253)
          ·
            refine ⟨3790018241023791425610845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10106715309396777134962253 3790018241023791425610845)
            ·
              refine ⟨1421256840383921784604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3790018241023791425610845 1421256840383921784604067)
              ·
                refine ⟨2131885260575882676906101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421256840383921784604067 2131885260575882676906101)
                ·
                  refine ⟨199864243178989000959947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2131885260575882676906101 199864243178989000959947)
                  ·
                    rfl

theorem cell21_875777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_875777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875777 prefixEnd_875777 := by exact prefixLift 875777
  have htrace : WordTrace (prefixWord ++ tailWord_875777) baseStart_875777 baseEnd_875777 := by
    simpa [prefixWord, tailWord_875777, baseEnd_875777] using wordTrace_append hprefix tailTrace_875777
  have hstable : (prefixWord ++ tailWord_875777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875777).length < 2 ^ (prefixWord ++ tailWord_875777).sum := by decide
  have hdescent : baseEnd_875777 < baseStart_875777 := by decide
  rcases family_descends (prefixWord ++ tailWord_875777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875862 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_875862 : Nat := 118140960795 + 875862 * 2 ^ 59
def prefixEnd_875862 : Nat := 4983230072969 + 3 ^ 40 * 875862 * 2
def baseEnd_875862 : Nat := 199883641337047742043107

theorem tailTrace_875862 : CollatzResearch.WordTrace tailWord_875862 prefixEnd_875862 199883641337047742043107 := by
  unfold tailWord_875862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996581972056814635350865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21296874368606022777075893 1996581972056814635350865)
  ·
    refine ⟨1497436479042610976513149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1996581972056814635350865 1497436479042610976513149)
    ·
      refine ⟨561538679640979116192431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1497436479042610976513149 561538679640979116192431)
      ·
        refine ⟨842308019461468674288647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561538679640979116192431 842308019461468674288647)
        ·
          refine ⟨1263462029192203011432971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842308019461468674288647 1263462029192203011432971)
          ·
            refine ⟨1895193043788304517149457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263462029192203011432971 1895193043788304517149457)
            ·
              refine ⟨1421394782841228387862093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895193043788304517149457 1421394782841228387862093)
              ·
                refine ⟨533023043565460645448285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421394782841228387862093 533023043565460645448285)
                ·
                  refine ⟨199883641337047742043107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533023043565460645448285 199883641337047742043107)
                  ·
                    rfl

theorem cell21_875862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_875862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875862 prefixEnd_875862 := by exact prefixLift 875862
  have htrace : WordTrace (prefixWord ++ tailWord_875862) baseStart_875862 baseEnd_875862 := by
    simpa [prefixWord, tailWord_875862, baseEnd_875862] using wordTrace_append hprefix tailTrace_875862
  have hstable : (prefixWord ++ tailWord_875862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875862).length < 2 ^ (prefixWord ++ tailWord_875862).sum := by decide
  have hdescent : baseEnd_875862 < baseStart_875862 := by decide
  rcases family_descends (prefixWord ++ tailWord_875862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875884 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_875884 : Nat := 118140960795 + 875884 * 2 ^ 59
def prefixEnd_875884 : Nat := 4983230072969 + 3 ^ 40 * 875884 * 2
def baseEnd_875884 : Nat := 199888662036780592676395

theorem tailTrace_875884 : CollatzResearch.WordTrace tailWord_875884 prefixEnd_875884 199888662036780592676395 := by
  unfold tailWord_875884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973056979414665961457353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21297409305886221281943137 15973056979414665961457353)
  ·
    refine ⟨11979792734560999471093015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15973056979414665961457353 11979792734560999471093015)
    ·
      refine ⟨17969689101841499206639523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11979792734560999471093015 17969689101841499206639523)
      ·
        refine ⟨26954533652762248809959285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17969689101841499206639523 26954533652762248809959285)
        ·
          refine ⟨2526987529946460825933683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26954533652762248809959285 2526987529946460825933683)
          ·
            refine ⟨3790481294919691238900525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526987529946460825933683 3790481294919691238900525)
            ·
              refine ⟨1421430485594884214587697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3790481294919691238900525 1421430485594884214587697)
              ·
                refine ⟨1066072864196163160940773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421430485594884214587697 1066072864196163160940773)
                ·
                  refine ⟨199888662036780592676395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066072864196163160940773 199888662036780592676395)
                  ·
                    rfl

theorem cell21_875884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_875884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875884 prefixEnd_875884 := by exact prefixLift 875884
  have htrace : WordTrace (prefixWord ++ tailWord_875884) baseStart_875884 baseEnd_875884 := by
    simpa [prefixWord, tailWord_875884, baseEnd_875884] using wordTrace_append hprefix tailTrace_875884
  have hstable : (prefixWord ++ tailWord_875884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875884).length < 2 ^ (prefixWord ++ tailWord_875884).sum := by decide
  have hdescent : baseEnd_875884 < baseStart_875884 := by decide
  rcases family_descends (prefixWord ++ tailWord_875884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875932 : List Nat := [2, 2, 3, 4, 2, 1, 7]
def baseStart_875932 : Nat := 118140960795 + 875932 * 2 ^ 59
def prefixEnd_875932 : Nat := 4983230072969 + 3 ^ 40 * 875932 * 2
def baseEnd_875932 : Nat := 22211068476749241764033

theorem tailTrace_875932 : CollatzResearch.WordTrace tailWord_875932 prefixEnd_875932 22211068476749241764033 := by
  unfold tailWord_875932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973932331327718060331025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21298576441770290747108033 15973932331327718060331025)
  ·
    refine ⟨11980449248495788545248269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15973932331327718060331025 11980449248495788545248269)
    ·
      refine ⟨4492668468185920704468101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11980449248495788545248269 4492668468185920704468101)
      ·
        refine ⟨842375337784860132087769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4492668468185920704468101 842375337784860132087769)
        ·
          refine ⟨631781503338645099065827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842375337784860132087769 631781503338645099065827)
          ·
            refine ⟨947672255007967648598741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631781503338645099065827 947672255007967648598741)
            ·
              refine ⟨22211068476749241764033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 947672255007967648598741 22211068476749241764033)
              ·
                rfl

theorem cell21_875932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 7].length) (baseStart_875932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875932 prefixEnd_875932 := by exact prefixLift 875932
  have htrace : WordTrace (prefixWord ++ tailWord_875932) baseStart_875932 baseEnd_875932 := by
    simpa [prefixWord, tailWord_875932, baseEnd_875932] using wordTrace_append hprefix tailTrace_875932
  have hstable : (prefixWord ++ tailWord_875932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875932).length < 2 ^ (prefixWord ++ tailWord_875932).sum := by decide
  have hdescent : baseEnd_875932 < baseStart_875932 := by decide
  rcases family_descends (prefixWord ++ tailWord_875932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875943 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_875943 : Nat := 118140960795 + 875943 * 2 ^ 59
def prefixEnd_875943 : Nat := 4983230072969 + 3 ^ 40 * 875943 * 2
def baseEnd_875943 : Nat := 199902126640609601192941

theorem tailTrace_875943 : CollatzResearch.WordTrace tailWord_875943 prefixEnd_875943 199902126640609601192941 := by
  unfold tailWord_875943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31948265865615584999312483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21298843910410389999541655 31948265865615584999312483)
  ·
    refine ⟨47922398798423377498968725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31948265865615584999312483 47922398798423377498968725)
    ·
      refine ⟨2246362443676095820264159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47922398798423377498968725 2246362443676095820264159)
      ·
        refine ⟨3369543665514143730396239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246362443676095820264159 3369543665514143730396239)
        ·
          refine ⟨5054315498271215595594359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369543665514143730396239 5054315498271215595594359)
          ·
            refine ⟨7581473247406823393391539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054315498271215595594359 7581473247406823393391539)
            ·
              refine ⟨11372209871110235090087309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581473247406823393391539 11372209871110235090087309)
              ·
                refine ⟨4264578701666338158782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11372209871110235090087309 4264578701666338158782741)
                ·
                  refine ⟨199902126640609601192941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4264578701666338158782741 199902126640609601192941)
                  ·
                    rfl

theorem cell21_875943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_875943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875943 prefixEnd_875943 := by exact prefixLift 875943
  have htrace : WordTrace (prefixWord ++ tailWord_875943) baseStart_875943 baseEnd_875943 := by
    simpa [prefixWord, tailWord_875943, baseEnd_875943] using wordTrace_append hprefix tailTrace_875943
  have hstable : (prefixWord ++ tailWord_875943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875943).length < 2 ^ (prefixWord ++ tailWord_875943).sum := by decide
  have hdescent : baseEnd_875943 < baseStart_875943 := by decide
  rcases family_descends (prefixWord ++ tailWord_875943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875960 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_875960 : Nat := 118140960795 + 875960 * 2 ^ 59
def prefixEnd_875960 : Nat := 4983230072969 + 3 ^ 40 * 875960 * 2
def baseEnd_875960 : Nat := 199906006272221349409573

theorem tailTrace_875960 : CollatzResearch.WordTrace tailWord_875960 prefixEnd_875960 199906006272221349409573 := by
  unfold tailWord_875960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974442953276998451340667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21299257271035997935120889 15974442953276998451340667)
  ·
    refine ⟨23961664429915497677011001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15974442953276998451340667 23961664429915497677011001)
    ·
      refine ⟨17971248322436623257758251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23961664429915497677011001 17971248322436623257758251)
      ·
        refine ⟨26956872483654934886637377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971248322436623257758251 26956872483654934886637377)
        ·
          refine ⟨20217654362741201164978033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26956872483654934886637377 20217654362741201164978033)
          ·
            refine ⟨15163240772055900873733525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20217654362741201164978033 15163240772055900873733525)
            ·
              refine ⟨710776911190120353456259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15163240772055900873733525 710776911190120353456259)
              ·
                refine ⟨1066165366785180530184389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710776911190120353456259 1066165366785180530184389)
                ·
                  refine ⟨199906006272221349409573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066165366785180530184389 199906006272221349409573)
                  ·
                    rfl

theorem cell21_875960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_875960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_875960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_875960 prefixEnd_875960 := by exact prefixLift 875960
  have htrace : WordTrace (prefixWord ++ tailWord_875960) baseStart_875960 baseEnd_875960 := by
    simpa [prefixWord, tailWord_875960, baseEnd_875960] using wordTrace_append hprefix tailTrace_875960
  have hstable : (prefixWord ++ tailWord_875960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875960).length < 2 ^ (prefixWord ++ tailWord_875960).sum := by decide
  have hdescent : baseEnd_875960 < baseStart_875960 := by decide
  rcases family_descends (prefixWord ++ tailWord_875960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876154 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_876154 : Nat := 118140960795 + 876154 * 2 ^ 59
def prefixEnd_876154 : Nat := 4983230072969 + 3 ^ 40 * 876154 * 2
def baseEnd_876154 : Nat := 199950279715320123175843

theorem tailTrace_876154 : CollatzResearch.WordTrace tailWord_876154 prefixEnd_876154 199950279715320123175843 := by
  unfold tailWord_876154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988990416962792008810879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21303974445234112023495677 7988990416962792008810879)
  ·
    refine ⟨11983485625444188013216319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7988990416962792008810879 11983485625444188013216319)
    ·
      refine ⟨17975228438166282019824479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983485625444188013216319 17975228438166282019824479)
      ·
        refine ⟨26962842657249423029736719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975228438166282019824479 26962842657249423029736719)
        ·
          refine ⟨40444263985874134544605079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26962842657249423029736719 40444263985874134544605079)
          ·
            refine ⟨60666395978811201816907619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40444263985874134544605079 60666395978811201816907619)
            ·
              refine ⟨90999593968216802725361429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60666395978811201816907619 90999593968216802725361429)
              ·
                refine ⟨4265605967260162627751317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90999593968216802725361429 4265605967260162627751317)
                ·
                  refine ⟨199950279715320123175843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4265605967260162627751317 199950279715320123175843)
                  ·
                    rfl

theorem cell21_876154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_876154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876154 prefixEnd_876154 := by exact prefixLift 876154
  have htrace : WordTrace (prefixWord ++ tailWord_876154) baseStart_876154 baseEnd_876154 := by
    simpa [prefixWord, tailWord_876154, baseEnd_876154] using wordTrace_append hprefix tailTrace_876154
  have hstable : (prefixWord ++ tailWord_876154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876154).length < 2 ^ (prefixWord ++ tailWord_876154).sum := by decide
  have hdescent : baseEnd_876154 < baseStart_876154 := by decide
  rcases family_descends (prefixWord ++ tailWord_876154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876171 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_876171 : Nat := 118140960795 + 876171 * 2 ^ 59
def prefixEnd_876171 : Nat := 4983230072969 + 3 ^ 40 * 876171 * 2
def baseEnd_876171 : Nat := 199954159346931871392475

theorem tailTrace_876171 : CollatzResearch.WordTrace tailWord_876171 prefixEnd_876171 199954159346931871392475 := by
  unfold tailWord_876171
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956581708789579938612367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21304387805859719959074911 31956581708789579938612367)
  ·
    refine ⟨47934872563184369907918551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31956581708789579938612367 47934872563184369907918551)
    ·
      refine ⟨71902308844776554861877827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47934872563184369907918551 71902308844776554861877827)
      ·
        refine ⟨107853463267164832292816741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71902308844776554861877827 107853463267164832292816741)
        ·
          refine ⟨20222524362593406054903139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107853463267164832292816741 20222524362593406054903139)
          ·
            refine ⟨30333786543890109082354709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20222524362593406054903139 30333786543890109082354709)
            ·
              refine ⟨1421896244244848863235377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30333786543890109082354709 1421896244244848863235377)
              ·
                refine ⟨1066422183183636647426533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421896244244848863235377 1066422183183636647426533)
                ·
                  refine ⟨199954159346931871392475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066422183183636647426533 199954159346931871392475)
                  ·
                    rfl

theorem cell21_876171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_876171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876171 prefixEnd_876171 := by exact prefixLift 876171
  have htrace : WordTrace (prefixWord ++ tailWord_876171) baseStart_876171 baseEnd_876171 := by
    simpa [prefixWord, tailWord_876171, baseEnd_876171] using wordTrace_append hprefix tailTrace_876171
  have hstable : (prefixWord ++ tailWord_876171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876171).length < 2 ^ (prefixWord ++ tailWord_876171).sum := by decide
  have hdescent : baseEnd_876171 < baseStart_876171 := by decide
  rcases family_descends (prefixWord ++ tailWord_876171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876174 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_876174 : Nat := 118140960795 + 876174 * 2 ^ 59
def prefixEnd_876174 : Nat := 4983230072969 + 3 ^ 40 * 876174 * 2
def baseEnd_876174 : Nat := 199954843987804532842469

theorem tailTrace_876174 : CollatzResearch.WordTrace tailWord_876174 prefixEnd_876174 199954843987804532842469 := by
  unfold tailWord_876174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994586390972338931371447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21304460751852474300647717 3994586390972338931371447)
  ·
    refine ⟨5991879586458508397057171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3994586390972338931371447 5991879586458508397057171)
    ·
      refine ⟨8987819379687762595585757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991879586458508397057171 8987819379687762595585757)
      ·
        refine ⟨3370432267382910973344659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8987819379687762595585757 3370432267382910973344659)
        ·
          refine ⟨5055648401074366460016989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370432267382910973344659 5055648401074366460016989)
          ·
            refine ⟨1895868150402887422506371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055648401074366460016989 1895868150402887422506371)
            ·
              refine ⟨2843802225604331133759557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895868150402887422506371 2843802225604331133759557)
              ·
                refine ⟨533212917300812087579917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2843802225604331133759557 533212917300812087579917)
                ·
                  refine ⟨199954843987804532842469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533212917300812087579917 199954843987804532842469)
                  ·
                    rfl

theorem cell21_876174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_876174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876174 prefixEnd_876174 := by exact prefixLift 876174
  have htrace : WordTrace (prefixWord ++ tailWord_876174) baseStart_876174 baseEnd_876174 := by
    simpa [prefixWord, tailWord_876174, baseEnd_876174] using wordTrace_append hprefix tailTrace_876174
  have hstable : (prefixWord ++ tailWord_876174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876174).length < 2 ^ (prefixWord ++ tailWord_876174).sum := by decide
  have hdescent : baseEnd_876174 < baseStart_876174 := by decide
  rcases family_descends (prefixWord ++ tailWord_876174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876253 : List Nat := [1, 4, 3, 3, 2, 1, 2, 5]
def baseStart_876253 : Nat := 118140960795 + 876253 * 2 ^ 59
def prefixEnd_876253 : Nat := 4983230072969 + 3 ^ 40 * 876253 * 2
def baseEnd_876253 : Nat := 66657624288039317008547

theorem tailTrace_876253 : CollatzResearch.WordTrace tailWord_876253 prefixEnd_876253 66657624288039317008547 := by
  unfold tailWord_876253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959572494492507943097413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306381662995005295398275 31959572494492507943097413)
  ·
    refine ⟨5992419842717345239330765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31959572494492507943097413 5992419842717345239330765)
    ·
      refine ⟨2247157441019004464749037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5992419842717345239330765 2247157441019004464749037)
      ·
        refine ⟨842684040382126674280889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2247157441019004464749037 842684040382126674280889)
        ·
          refine ⟨632013030286595005710667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842684040382126674280889 632013030286595005710667)
          ·
            refine ⟨948019545429892508566001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632013030286595005710667 948019545429892508566001)
            ·
              refine ⟨711014659072419381424501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948019545429892508566001 711014659072419381424501)
              ·
                refine ⟨66657624288039317008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 711014659072419381424501 66657624288039317008547)
                ·
                  rfl

theorem cell21_876253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].length) (baseStart_876253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876253 prefixEnd_876253 := by exact prefixLift 876253
  have htrace : WordTrace (prefixWord ++ tailWord_876253) baseStart_876253 baseEnd_876253 := by
    simpa [prefixWord, tailWord_876253, baseEnd_876253] using wordTrace_append hprefix tailTrace_876253
  have hstable : (prefixWord ++ tailWord_876253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876253).length < 2 ^ (prefixWord ++ tailWord_876253).sum := by decide
  have hdescent : baseEnd_876253 < baseStart_876253 := by decide
  rcases family_descends (prefixWord ++ tailWord_876253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876261 : List Nat := [1, 3, 1, 4, 1, 1, 3, 7]
def baseStart_876261 : Nat := 118140960795 + 876261 * 2 ^ 59
def prefixEnd_876261 : Nat := 4983230072969 + 3 ^ 40 * 876261 * 2
def baseEnd_876261 : Nat := 66658232857703904964097

theorem tailTrace_876261 : CollatzResearch.WordTrace tailWord_876261 prefixEnd_876261 66658232857703904964097 := by
  unfold tailWord_876261
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959864278463525309388637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306576185642350206259091 31959864278463525309388637)
  ·
    refine ⟨11984949104423821991020739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31959864278463525309388637 11984949104423821991020739)
    ·
      refine ⟨17977423656635732986531109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984949104423821991020739 17977423656635732986531109)
      ·
        refine ⟨3370766935619199934974583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17977423656635732986531109 3370766935619199934974583)
        ·
          refine ⟨5056150403428799902461875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370766935619199934974583 5056150403428799902461875)
          ·
            refine ⟨7584225605143199853692813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056150403428799902461875 7584225605143199853692813)
            ·
              refine ⟨2844084601928699945134805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7584225605143199853692813 2844084601928699945134805)
              ·
                refine ⟨66658232857703904964097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2844084601928699945134805 66658232857703904964097)
                ·
                  rfl

theorem cell21_876261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_876261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876261 prefixEnd_876261 := by exact prefixLift 876261
  have htrace : WordTrace (prefixWord ++ tailWord_876261) baseStart_876261 baseEnd_876261 := by
    simpa [prefixWord, tailWord_876261, baseEnd_876261] using wordTrace_append hprefix tailTrace_876261
  have hstable : (prefixWord ++ tailWord_876261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876261).length < 2 ^ (prefixWord ++ tailWord_876261).sum := by decide
  have hdescent : baseEnd_876261 < baseStart_876261 := by decide
  rcases family_descends (prefixWord ++ tailWord_876261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876275 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_876275 : Nat := 118140960795 + 876275 * 2 ^ 59
def prefixEnd_876275 : Nat := 4983230072969 + 3 ^ 40 * 876275 * 2
def baseEnd_876275 : Nat := 199977893563850801658929

theorem tailTrace_876275 : CollatzResearch.WordTrace tailWord_876275 prefixEnd_876275 199977893563850801658929 := by
  unfold tailWord_876275
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960374900412805700398279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306916600275203800265519 31960374900412805700398279)
  ·
    refine ⟨47940562350619208550597419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960374900412805700398279 47940562350619208550597419)
    ·
      refine ⟨71910843525928812825896129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47940562350619208550597419 71910843525928812825896129)
      ·
        refine ⟨53933132644446609619422097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71910843525928812825896129 53933132644446609619422097)
        ·
          refine ⟨40449849483334957214566573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53933132644446609619422097 40449849483334957214566573)
          ·
            refine ⟨15168693556250608955462465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40449849483334957214566573 15168693556250608955462465)
            ·
              refine ⟨11376520167187956716596849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15168693556250608955462465 11376520167187956716596849)
              ·
                refine ⟨8532390125390967537447637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11376520167187956716596849 8532390125390967537447637)
                ·
                  refine ⟨199977893563850801658929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8532390125390967537447637 199977893563850801658929)
                  ·
                    rfl

theorem cell21_876275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_876275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876275 prefixEnd_876275 := by exact prefixLift 876275
  have htrace : WordTrace (prefixWord ++ tailWord_876275) baseStart_876275 baseEnd_876275 := by
    simpa [prefixWord, tailWord_876275, baseEnd_876275] using wordTrace_append hprefix tailTrace_876275
  have hstable : (prefixWord ++ tailWord_876275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876275).length < 2 ^ (prefixWord ++ tailWord_876275).sum := by decide
  have hdescent : baseEnd_876275 < baseStart_876275 := by decide
  rcases family_descends (prefixWord ++ tailWord_876275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876278 : List Nat := [5, 1, 1, 1, 1, 5, 7]
def baseStart_876278 : Nat := 118140960795 + 876278 * 2 ^ 59
def prefixEnd_876278 : Nat := 4983230072969 + 3 ^ 40 * 876278 * 2
def baseEnd_876278 : Nat := 22219842022747051456547

theorem tailTrace_876278 : CollatzResearch.WordTrace tailWord_876278 prefixEnd_876278 22219842022747051456547 := by
  unfold tailWord_876278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997530269962621075797343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21306989546267958141838325 1997530269962621075797343)
  ·
    refine ⟨2996295404943931613696015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997530269962621075797343 2996295404943931613696015)
    ·
      refine ⟨4494443107415897420544023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996295404943931613696015 4494443107415897420544023)
      ·
        refine ⟨6741664661123846130816035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494443107415897420544023 6741664661123846130816035)
        ·
          refine ⟨10112496991685769196224053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741664661123846130816035 10112496991685769196224053)
          ·
            refine ⟨948046592970540862146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10112496991685769196224053 948046592970540862146005)
            ·
              refine ⟨22219842022747051456547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 948046592970540862146005 22219842022747051456547)
              ·
                rfl

theorem cell21_876278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 7].length) (baseStart_876278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876278 prefixEnd_876278 := by exact prefixLift 876278
  have htrace : WordTrace (prefixWord ++ tailWord_876278) baseStart_876278 baseEnd_876278 := by
    simpa [prefixWord, tailWord_876278, baseEnd_876278] using wordTrace_append hprefix tailTrace_876278
  have hstable : (prefixWord ++ tailWord_876278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876278).length < 2 ^ (prefixWord ++ tailWord_876278).sum := by decide
  have hdescent : baseEnd_876278 < baseStart_876278 := by decide
  rcases family_descends (prefixWord ++ tailWord_876278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876340 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_876340 : Nat := 118140960795 + 876340 * 2 ^ 59
def prefixEnd_876340 : Nat := 4983230072969 + 3 ^ 40 * 876340 * 2
def baseEnd_876340 : Nat := 199992727449425133075463

theorem tailTrace_876340 : CollatzResearch.WordTrace tailWord_876340 prefixEnd_876340 199992727449425133075463 := by
  unfold tailWord_876340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981372822588660900757237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21308497096784881201009649 15981372822588660900757237)
  ·
    refine ⟨1498253702117686959445991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15981372822588660900757237 1498253702117686959445991)
    ·
      refine ⟨2247380553176530439168987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1498253702117686959445991 2247380553176530439168987)
      ·
        refine ⟨3371070829764795658753481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247380553176530439168987 3371070829764795658753481)
        ·
          refine ⟨2528303122323596744065111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3371070829764795658753481 2528303122323596744065111)
          ·
            refine ⟨3792454683485395116097667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528303122323596744065111 3792454683485395116097667)
            ·
              refine ⟨5688682025228092674146501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792454683485395116097667 5688682025228092674146501)
              ·
                refine ⟨1066627879730267376402469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5688682025228092674146501 1066627879730267376402469)
                ·
                  refine ⟨199992727449425133075463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066627879730267376402469 199992727449425133075463)
                  ·
                    rfl

theorem cell21_876340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_876340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876340 prefixEnd_876340 := by exact prefixLift 876340
  have htrace : WordTrace (prefixWord ++ tailWord_876340) baseStart_876340 baseEnd_876340 := by
    simpa [prefixWord, tailWord_876340, baseEnd_876340] using wordTrace_append hprefix tailTrace_876340
  have hstable : (prefixWord ++ tailWord_876340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876340).length < 2 ^ (prefixWord ++ tailWord_876340).sum := by decide
  have hdescent : baseEnd_876340 < baseStart_876340 := by decide
  rcases family_descends (prefixWord ++ tailWord_876340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876385 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 3]
def baseStart_876385 : Nat := 118140960795 + 876385 * 2 ^ 59
def prefixEnd_876385 : Nat := 4983230072969 + 3 ^ 40 * 876385 * 2
def baseEnd_876385 : Nat := 200002997062515054825371

theorem tailTrace_876385 : CollatzResearch.WordTrace tailWord_876385 prefixEnd_876385 200002997062515054825371 := by
  unfold tailWord_876385
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964386930014294486902609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21309591286676196324601739 31964386930014294486902609)
  ·
    refine ⟨23973290197510720865176957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31964386930014294486902609 23973290197510720865176957)
    ·
      refine ⟨8989983824066520324441359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23973290197510720865176957 8989983824066520324441359)
      ·
        refine ⟨13484975736099780486662039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989983824066520324441359 13484975736099780486662039)
        ·
          refine ⟨20227463604149670729993059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484975736099780486662039 20227463604149670729993059)
          ·
            refine ⟨30341195406224506094989589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20227463604149670729993059 30341195406224506094989589)
            ·
              refine ⟨1422243534666773723202637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30341195406224506094989589 1422243534666773723202637)
              ·
                refine ⟨533341325500040146200989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422243534666773723202637 533341325500040146200989)
                ·
                  refine ⟨200002997062515054825371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533341325500040146200989 200002997062515054825371)
                  ·
                    rfl

theorem cell21_876385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_876385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876385 prefixEnd_876385 := by exact prefixLift 876385
  have htrace : WordTrace (prefixWord ++ tailWord_876385) baseStart_876385 baseEnd_876385 := by
    simpa [prefixWord, tailWord_876385, baseEnd_876385] using wordTrace_append hprefix tailTrace_876385
  have hstable : (prefixWord ++ tailWord_876385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876385).length < 2 ^ (prefixWord ++ tailWord_876385).sum := by decide
  have hdescent : baseEnd_876385 < baseStart_876385 := by decide
  rcases family_descends (prefixWord ++ tailWord_876385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876554 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_876554 : Nat := 118140960795 + 876554 * 2 ^ 59
def prefixEnd_876554 : Nat := 4983230072969 + 3 ^ 40 * 876554 * 2
def baseEnd_876554 : Nat := 200041565165008316508359

theorem tailTrace_876554 : CollatzResearch.WordTrace tailWord_876554 prefixEnd_876554 200041565165008316508359 := by
  unfold tailWord_876554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992637716600509087451179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21313700577601357566536477 7992637716600509087451179)
  ·
    refine ⟨11988956574900763631176769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992637716600509087451179 11988956574900763631176769)
    ·
      refine ⟨8991717431175572723382577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11988956574900763631176769 8991717431175572723382577)
      ·
        refine ⟨6743788073381679542536933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8991717431175572723382577 6743788073381679542536933)
        ·
          refine ⟨1264460263759064914225675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6743788073381679542536933 1264460263759064914225675)
          ·
            refine ⟨1896690395638597371338513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264460263759064914225675 1896690395638597371338513)
            ·
              refine ⟨1422517796728948028503885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896690395638597371338513 1422517796728948028503885)
              ·
                refine ⟨533444173773355510688957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422517796728948028503885 533444173773355510688957)
                ·
                  refine ⟨200041565165008316508359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533444173773355510688957 200041565165008316508359)
                  ·
                    rfl

theorem cell21_876554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_876554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876554 prefixEnd_876554 := by exact prefixLift 876554
  have htrace : WordTrace (prefixWord ++ tailWord_876554) baseStart_876554 baseEnd_876554 := by
    simpa [prefixWord, tailWord_876554, baseEnd_876554] using wordTrace_append hprefix tailTrace_876554
  have hstable : (prefixWord ++ tailWord_876554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876554).length < 2 ^ (prefixWord ++ tailWord_876554).sum := by decide
  have hdescent : baseEnd_876554 < baseStart_876554 := by decide
  rcases family_descends (prefixWord ++ tailWord_876554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876565 : List Nat := [1, 3, 2, 1, 5, 1, 8]
def baseStart_876565 : Nat := 118140960795 + 876565 * 2 ^ 59
def prefixEnd_876565 : Nat := 4983230072969 + 3 ^ 40 * 876565 * 2
def baseEnd_876565 : Nat := 22227119501652749091667

theorem tailTrace_876565 : CollatzResearch.WordTrace tailWord_876565 prefixEnd_876565 22227119501652749091667 := by
  unfold tailWord_876565
  simp only [CollatzResearch.WordTrace]
  refine ⟨31970952069362185228455149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21313968046241456818970099 31970952069362185228455149)
  ·
    refine ⟨11989107026010819460670681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31970952069362185228455149 11989107026010819460670681)
    ·
      refine ⟨8991830269508114595503011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11989107026010819460670681 8991830269508114595503011)
      ·
        refine ⟨13487745404262171893254517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991830269508114595503011 13487745404262171893254517)
        ·
          refine ⟨1264476131649578614992611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13487745404262171893254517 1264476131649578614992611)
          ·
            refine ⟨1896714197474367922488917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264476131649578614992611 1896714197474367922488917)
            ·
              refine ⟨22227119501652749091667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1896714197474367922488917 22227119501652749091667)
              ·
                rfl

theorem cell21_876565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 8].length) (baseStart_876565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876565 prefixEnd_876565 := by exact prefixLift 876565
  have htrace : WordTrace (prefixWord ++ tailWord_876565) baseStart_876565 baseEnd_876565 := by
    simpa [prefixWord, tailWord_876565, baseEnd_876565] using wordTrace_append hprefix tailTrace_876565
  have hstable : (prefixWord ++ tailWord_876565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876565).length < 2 ^ (prefixWord ++ tailWord_876565).sum := by decide
  have hdescent : baseEnd_876565 < baseStart_876565 := by decide
  rcases family_descends (prefixWord ++ tailWord_876565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876630 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_876630 : Nat := 118140960795 + 876630 * 2 ^ 59
def prefixEnd_876630 : Nat := 4983230072969 + 3 ^ 40 * 876630 * 2
def baseEnd_876630 : Nat := 200058909400449073241537

theorem tailTrace_876630 : CollatzResearch.WordTrace tailWord_876630 prefixEnd_876630 200058909400449073241537 := by
  unfold tailWord_876630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998332675882918833098209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21315548542751134219714229 1998332675882918833098209)
  ·
    refine ⟨1498749506912189124823657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1998332675882918833098209 1498749506912189124823657)
    ·
      refine ⟨1124062130184141843617743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1498749506912189124823657 1124062130184141843617743)
      ·
        refine ⟨1686093195276212765426615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124062130184141843617743 1686093195276212765426615)
        ·
          refine ⟨2529139792914319148139923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686093195276212765426615 2529139792914319148139923)
          ·
            refine ⟨3793709689371478722209885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529139792914319148139923 3793709689371478722209885)
            ·
              refine ⟨1422641133514304520828707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3793709689371478722209885 1422641133514304520828707)
              ·
                refine ⟨2133961700271456781243061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422641133514304520828707 2133961700271456781243061)
                ·
                  refine ⟨200058909400449073241537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133961700271456781243061 200058909400449073241537)
                  ·
                    rfl

theorem cell21_876630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_876630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876630 prefixEnd_876630 := by exact prefixLift 876630
  have htrace : WordTrace (prefixWord ++ tailWord_876630) baseStart_876630 baseEnd_876630 := by
    simpa [prefixWord, tailWord_876630, baseEnd_876630] using wordTrace_append hprefix tailTrace_876630
  have hstable : (prefixWord ++ tailWord_876630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876630).length < 2 ^ (prefixWord ++ tailWord_876630).sum := by decide
  have hdescent : baseEnd_876630 < baseStart_876630 := by decide
  rcases family_descends (prefixWord ++ tailWord_876630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876672 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_876672 : Nat := 118140960795 + 876672 * 2 ^ 59
def prefixEnd_876672 : Nat := 4983230072969 + 3 ^ 40 * 876672 * 2
def baseEnd_876672 : Nat := 200068494372666333541451

theorem tailTrace_876672 : CollatzResearch.WordTrace tailWord_876672 prefixEnd_876672 200068494372666333541451 := by
  unfold tailWord_876672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987427339987271251300135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21316569786649695001733513 15987427339987271251300135)
  ·
    refine ⟨23981141009980906876950203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15987427339987271251300135 23981141009980906876950203)
    ·
      refine ⟨35971711514971360315425305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981141009980906876950203 35971711514971360315425305)
      ·
        refine ⟨26978783636228520236568979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35971711514971360315425305 26978783636228520236568979)
        ·
          refine ⟨40468175454342780354853469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26978783636228520236568979 40468175454342780354853469)
          ·
            refine ⟨15175565795378542633070051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40468175454342780354853469 15175565795378542633070051)
            ·
              refine ⟨22763348693067813949605077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15175565795378542633070051 22763348693067813949605077)
              ·
                refine ⟨533515984993776889443869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22763348693067813949605077 533515984993776889443869)
                ·
                  refine ⟨200068494372666333541451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533515984993776889443869 200068494372666333541451)
                  ·
                    rfl

theorem cell21_876672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_876672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876672 prefixEnd_876672 := by exact prefixLift 876672
  have htrace : WordTrace (prefixWord ++ tailWord_876672) baseStart_876672 baseEnd_876672 := by
    simpa [prefixWord, tailWord_876672, baseEnd_876672] using wordTrace_append hprefix tailTrace_876672
  have hstable : (prefixWord ++ tailWord_876672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876672).length < 2 ^ (prefixWord ++ tailWord_876672).sum := by decide
  have hdescent : baseEnd_876672 < baseStart_876672 := by decide
  rcases family_descends (prefixWord ++ tailWord_876672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876692 : List Nat := [2, 4, 2, 3, 2, 1, 1, 6]
def baseStart_876692 : Nat := 118140960795 + 876692 * 2 ^ 59
def prefixEnd_876692 : Nat := 4983230072969 + 3 ^ 40 * 876692 * 2
def baseEnd_876692 : Nat := 66691019548383581069359

theorem tailTrace_876692 : CollatzResearch.WordTrace tailWord_876692 prefixEnd_876692 66691019548383581069359 := by
  unfold tailWord_876692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987792069951042959164165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21317056093268057278885553 15987792069951042959164165)
  ·
    refine ⟨2997711013115820554843281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15987792069951042959164165 2997711013115820554843281)
    ·
      refine ⟨2248283259836865416132461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2997711013115820554843281 2248283259836865416132461)
      ·
        refine ⟨843106222438824531049673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2248283259836865416132461 843106222438824531049673)
        ·
          refine ⟨632329666829118398287255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843106222438824531049673 632329666829118398287255)
          ·
            refine ⟨948494500243677597430883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632329666829118398287255 948494500243677597430883)
            ·
              refine ⟨1422741750365516396146325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948494500243677597430883 1422741750365516396146325)
              ·
                refine ⟨66691019548383581069359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1422741750365516396146325 66691019548383581069359)
                ·
                  rfl

theorem cell21_876692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_876692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876692 prefixEnd_876692 := by exact prefixLift 876692
  have htrace : WordTrace (prefixWord ++ tailWord_876692) baseStart_876692 baseEnd_876692 := by
    simpa [prefixWord, tailWord_876692, baseEnd_876692] using wordTrace_append hprefix tailTrace_876692
  have hstable : (prefixWord ++ tailWord_876692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876692).length < 2 ^ (prefixWord ++ tailWord_876692).sum := by decide
  have hdescent : baseEnd_876692 < baseStart_876692 := by decide
  rcases family_descends (prefixWord ++ tailWord_876692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876703 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_876703 : Nat := 118140960795 + 876703 * 2 ^ 59
def prefixEnd_876703 : Nat := 4983230072969 + 3 ^ 40 * 876703 * 2
def baseEnd_876703 : Nat := 200075568995017168524721

theorem tailTrace_876703 : CollatzResearch.WordTrace tailWord_876703 prefixEnd_876703 200075568995017168524721 := by
  unfold tailWord_876703
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975985342862234796978763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21317323561908156531319175 31975985342862234796978763)
  ·
    refine ⟨47963978014293352195468145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31975985342862234796978763 47963978014293352195468145)
    ·
      refine ⟨35972983510720014146601109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47963978014293352195468145 35972983510720014146601109)
      ·
        refine ⟨1686233602065000663121927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35972983510720014146601109 1686233602065000663121927)
        ·
          refine ⟨2529350403097500994682891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686233602065000663121927 2529350403097500994682891)
          ·
            refine ⟨3794025604646251492024337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529350403097500994682891 3794025604646251492024337)
            ·
              refine ⟨2845519203484688619018253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794025604646251492024337 2845519203484688619018253)
              ·
                refine ⟨1067069701306758232131845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2845519203484688619018253 1067069701306758232131845)
                ·
                  refine ⟨200075568995017168524721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067069701306758232131845 200075568995017168524721)
                  ·
                    rfl

theorem cell21_876703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_876703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876703 prefixEnd_876703 := by exact prefixLift 876703
  have htrace : WordTrace (prefixWord ++ tailWord_876703) baseStart_876703 baseEnd_876703 := by
    simpa [prefixWord, tailWord_876703, baseEnd_876703] using wordTrace_append hprefix tailTrace_876703
  have hstable : (prefixWord ++ tailWord_876703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876703).length < 2 ^ (prefixWord ++ tailWord_876703).sum := by decide
  have hdescent : baseEnd_876703 < baseStart_876703 := by decide
  rcases family_descends (prefixWord ++ tailWord_876703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876737 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_876737 : Nat := 118140960795 + 876737 * 2 ^ 59
def prefixEnd_876737 : Nat := 4983230072969 + 3 ^ 40 * 876737 * 2
def baseEnd_876737 : Nat := 200083328258240664957985

theorem tailTrace_876737 : CollatzResearch.WordTrace tailWord_876737 prefixEnd_876737 200083328258240664957985 := by
  unfold tailWord_876737
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977225424739058603716465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21318150283159372402477643 31977225424739058603716465)
  ·
    refine ⟨23982919068554293952787349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31977225424739058603716465 23982919068554293952787349)
    ·
      refine ⟨1124199331338482529036907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23982919068554293952787349 1124199331338482529036907)
      ·
        refine ⟨1686298997007723793555361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124199331338482529036907 1686298997007723793555361)
        ·
          refine ⟨1264724247755792845166521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1686298997007723793555361 1264724247755792845166521)
          ·
            refine ⟨948543185816844633874891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264724247755792845166521 948543185816844633874891)
            ·
              refine ⟨1422814778725266950812337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948543185816844633874891 1422814778725266950812337)
              ·
                refine ⟨1067111084043950213109253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422814778725266950812337 1067111084043950213109253)
                ·
                  refine ⟨200083328258240664957985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067111084043950213109253 200083328258240664957985)
                  ·
                    rfl

theorem cell21_876737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_876737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876737 prefixEnd_876737 := by exact prefixLift 876737
  have htrace : WordTrace (prefixWord ++ tailWord_876737) baseStart_876737 baseEnd_876737 := by
    simpa [prefixWord, tailWord_876737, baseEnd_876737] using wordTrace_append hprefix tailTrace_876737
  have hstable : (prefixWord ++ tailWord_876737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876737).length < 2 ^ (prefixWord ++ tailWord_876737).sum := by decide
  have hdescent : baseEnd_876737 < baseStart_876737 := by decide
  rcases family_descends (prefixWord ++ tailWord_876737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876762 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_876762 : Nat := 118140960795 + 876762 * 2 ^ 59
def prefixEnd_876762 : Nat := 4983230072969 + 3 ^ 40 * 876762 * 2
def baseEnd_876762 : Nat := 200089033598846177041267

theorem tailTrace_876762 : CollatzResearch.WordTrace tailWord_876762 prefixEnd_876762 200089033598846177041267 := by
  unfold tailWord_876762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994534312412121968344135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21318758166432325248917693 7994534312412121968344135)
  ·
    refine ⟨11991801468618182952516203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7994534312412121968344135 11991801468618182952516203)
    ·
      refine ⟨17987702202927274428774305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991801468618182952516203 17987702202927274428774305)
      ·
        refine ⟨13490776652195455821580729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17987702202927274428774305 13490776652195455821580729)
        ·
          refine ⟨10118082489146591866185547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13490776652195455821580729 10118082489146591866185547)
          ·
            refine ⟨15177123733719887799278321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118082489146591866185547 15177123733719887799278321)
            ·
              refine ⟨11382842800289915849458741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15177123733719887799278321 11382842800289915849458741)
              ·
                refine ⟨1067141512527179610886757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11382842800289915849458741 1067141512527179610886757)
                ·
                  refine ⟨200089033598846177041267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067141512527179610886757 200089033598846177041267)
                  ·
                    rfl

theorem cell21_876762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_876762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876762 prefixEnd_876762 := by exact prefixLift 876762
  have htrace : WordTrace (prefixWord ++ tailWord_876762) baseStart_876762 baseEnd_876762 := by
    simpa [prefixWord, tailWord_876762, baseEnd_876762] using wordTrace_append hprefix tailTrace_876762
  have hstable : (prefixWord ++ tailWord_876762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876762).length < 2 ^ (prefixWord ++ tailWord_876762).sum := by decide
  have hdescent : baseEnd_876762 < baseStart_876762 := by decide
  rcases family_descends (prefixWord ++ tailWord_876762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876858 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_876858 : Nat := 118140960795 + 876858 * 2 ^ 59
def prefixEnd_876858 : Nat := 4983230072969 + 3 ^ 40 * 876858 * 2
def baseEnd_876858 : Nat := 200110942106771343441071

theorem tailTrace_876858 : CollatzResearch.WordTrace tailWord_876858 prefixEnd_876858 200110942106771343441071 := by
  unfold tailWord_876858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995409664325174067217807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21321092438200464179247485 7995409664325174067217807)
  ·
    refine ⟨11993114496487761100826711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995409664325174067217807 11993114496487761100826711)
    ·
      refine ⟨17989671744731641651240067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993114496487761100826711 17989671744731641651240067)
      ·
        refine ⟨26984507617097462476860101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17989671744731641651240067 26984507617097462476860101)
        ·
          refine ⟨5059595178205774214411269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26984507617097462476860101 5059595178205774214411269)
          ·
            refine ⟨948674095913582665202113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5059595178205774214411269 948674095913582665202113)
            ·
              refine ⟨711505571935186998901585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948674095913582665202113 711505571935186998901585)
              ·
                refine ⟨533629178951390249176189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711505571935186998901585 533629178951390249176189)
                ·
                  refine ⟨200110942106771343441071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533629178951390249176189 200110942106771343441071)
                  ·
                    rfl

theorem cell21_876858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_876858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876858 prefixEnd_876858 := by exact prefixLift 876858
  have htrace : WordTrace (prefixWord ++ tailWord_876858) baseStart_876858 baseEnd_876858 := by
    simpa [prefixWord, tailWord_876858, baseEnd_876858] using wordTrace_append hprefix tailTrace_876858
  have hstable : (prefixWord ++ tailWord_876858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876858).length < 2 ^ (prefixWord ++ tailWord_876858).sum := by decide
  have hdescent : baseEnd_876858 < baseStart_876858 := by decide
  rcases family_descends (prefixWord ++ tailWord_876858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876914 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_876914 : Nat := 118140960795 + 876914 * 2 ^ 59
def prefixEnd_876914 : Nat := 4983230072969 + 3 ^ 40 * 876914 * 2
def baseEnd_876914 : Nat := 200123722069727690507623

theorem tailTrace_876914 : CollatzResearch.WordTrace tailWord_876914 prefixEnd_876914 200123722069727690507623 := by
  unfold tailWord_876914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995920286274454458227449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21322454096731878555273197 7995920286274454458227449)
  ·
    refine ⟨5996940214705840843670587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7995920286274454458227449 5996940214705840843670587)
    ·
      refine ⟨8995410322058761265505881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996940214705840843670587 8995410322058761265505881)
      ·
        refine ⟨6746557741544070949129411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995410322058761265505881 6746557741544070949129411)
        ·
          refine ⟨10119836612316106423694117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746557741544070949129411 10119836612316106423694117)
          ·
            refine ⟨1897469364809269954442647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10119836612316106423694117 1897469364809269954442647)
            ·
              refine ⟨2846204047213904931663971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897469364809269954442647 2846204047213904931663971)
              ·
                refine ⟨4269306070820857397495957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846204047213904931663971 4269306070820857397495957)
                ·
                  refine ⟨200123722069727690507623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4269306070820857397495957 200123722069727690507623)
                  ·
                    rfl

theorem cell21_876914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_876914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876914 prefixEnd_876914 := by exact prefixLift 876914
  have htrace : WordTrace (prefixWord ++ tailWord_876914) baseStart_876914 baseEnd_876914 := by
    simpa [prefixWord, tailWord_876914, baseEnd_876914] using wordTrace_append hprefix tailTrace_876914
  have hstable : (prefixWord ++ tailWord_876914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876914).length < 2 ^ (prefixWord ++ tailWord_876914).sum := by decide
  have hdescent : baseEnd_876914 < baseStart_876914 := by decide
  rcases family_descends (prefixWord ++ tailWord_876914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876917 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 3]
def baseStart_876917 : Nat := 118140960795 + 876917 * 2 ^ 59
def prefixEnd_876917 : Nat := 4983230072969 + 3 ^ 40 * 876917 * 2
def baseEnd_876917 : Nat := 200124406710600351957617

theorem tailTrace_876917 : CollatzResearch.WordTrace tailWord_876917 prefixEnd_876917 200124406710600351957617 := by
  unfold tailWord_876917
  simp only [CollatzResearch.WordTrace]
  refine ⟨31983790564086949345269005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21322527042724632896846003 31983790564086949345269005)
  ·
    refine ⟨11993921461532606004475877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31983790564086949345269005 11993921461532606004475877)
    ·
      refine ⟨2248860274037363625839227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11993921461532606004475877 2248860274037363625839227)
      ·
        refine ⟨3373290411056045438758841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248860274037363625839227 3373290411056045438758841)
        ·
          refine ⟨2529967808292034079069131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3373290411056045438758841 2529967808292034079069131)
          ·
            refine ⟨3794951712438051118603697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529967808292034079069131 3794951712438051118603697)
            ·
              refine ⟨2846213784328538338952773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794951712438051118603697 2846213784328538338952773)
              ·
                refine ⟨533665084561600938553645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2846213784328538338952773 533665084561600938553645)
                ·
                  refine ⟨200124406710600351957617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533665084561600938553645 200124406710600351957617)
                  ·
                    rfl

theorem cell21_876917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_876917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_876917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_876917 prefixEnd_876917 := by exact prefixLift 876917
  have htrace : WordTrace (prefixWord ++ tailWord_876917) baseStart_876917 baseEnd_876917 := by
    simpa [prefixWord, tailWord_876917, baseEnd_876917] using wordTrace_append hprefix tailTrace_876917
  have hstable : (prefixWord ++ tailWord_876917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876917).length < 2 ^ (prefixWord ++ tailWord_876917).sum := by decide
  have hdescent : baseEnd_876917 < baseStart_876917 := by decide
  rcases family_descends (prefixWord ++ tailWord_876917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877027 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 3]
def baseStart_877027 : Nat := 118140960795 + 877027 * 2 ^ 59
def prefixEnd_877027 : Nat := 4983230072969 + 3 ^ 40 * 877027 * 2
def baseEnd_877027 : Nat := 200149510209264605124059

theorem tailTrace_877027 : CollatzResearch.WordTrace tailWord_877027 prefixEnd_877027 200149510209264605124059 := by
  unfold tailWord_877027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31987802593688438131773335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21325201729125625421182223 31987802593688438131773335)
  ·
    refine ⟨47981703890532657197660003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31987802593688438131773335 47981703890532657197660003)
    ·
      refine ⟨71972555835798985796490005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47981703890532657197660003 71972555835798985796490005)
      ·
        refine ⟨3373713554803077459210469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71972555835798985796490005 3373713554803077459210469)
        ·
          refine ⟨632571291525577023601963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3373713554803077459210469 632571291525577023601963)
          ·
            refine ⟨948856937288365535402945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632571291525577023601963 948856937288365535402945)
            ·
              refine ⟨711642702966274151552209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948856937288365535402945 711642702966274151552209)
              ·
                refine ⟨533732027224705613664157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711642702966274151552209 533732027224705613664157)
                ·
                  refine ⟨200149510209264605124059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533732027224705613664157 200149510209264605124059)
                  ·
                    rfl

theorem cell21_877027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].length) (baseStart_877027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877027 prefixEnd_877027 := by exact prefixLift 877027
  have htrace : WordTrace (prefixWord ++ tailWord_877027) baseStart_877027 baseEnd_877027 := by
    simpa [prefixWord, tailWord_877027, baseEnd_877027] using wordTrace_append hprefix tailTrace_877027
  have hstable : (prefixWord ++ tailWord_877027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877027).length < 2 ^ (prefixWord ++ tailWord_877027).sum := by decide
  have hdescent : baseEnd_877027 < baseStart_877027 := by decide
  rcases family_descends (prefixWord ++ tailWord_877027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877080 : List Nat := [2, 1, 2, 3, 3, 2, 8]
def baseStart_877080 : Nat := 118140960795 + 877080 * 2 ^ 59
def prefixEnd_877080 : Nat := 4983230072969 + 3 ^ 40 * 877080 * 2
def baseEnd_877080 : Nat := 22240178392372032304513

theorem tailTrace_877080 : CollatzResearch.WordTrace tailWord_877080 prefixEnd_877080 22240178392372032304513 := by
  unfold tailWord_877080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994867831248214091726347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21326490441664285455635129 15994867831248214091726347)
  ·
    refine ⟨23992301746872321137589521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994867831248214091726347 23992301746872321137589521)
    ·
      refine ⟨17994226310154240853192141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23992301746872321137589521 17994226310154240853192141)
      ·
        refine ⟨6747834866307840319947053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17994226310154240853192141 6747834866307840319947053)
        ·
          refine ⟨2530438074865440119980145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6747834866307840319947053 2530438074865440119980145)
          ·
            refine ⟨1897828556149080089985109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530438074865440119980145 1897828556149080089985109)
            ·
              refine ⟨22240178392372032304513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1897828556149080089985109 22240178392372032304513)
              ·
                rfl

theorem cell21_877080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 8].length) (baseStart_877080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877080 prefixEnd_877080 := by exact prefixLift 877080
  have htrace : WordTrace (prefixWord ++ tailWord_877080) baseStart_877080 baseEnd_877080 := by
    simpa [prefixWord, tailWord_877080, baseEnd_877080] using wordTrace_append hprefix tailTrace_877080
  have hstable : (prefixWord ++ tailWord_877080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877080).length < 2 ^ (prefixWord ++ tailWord_877080).sum := by decide
  have hdescent : baseEnd_877080 < baseStart_877080 := by decide
  rcases family_descends (prefixWord ++ tailWord_877080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877125 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_877125 : Nat := 118140960795 + 877125 * 2 ^ 59
def prefixEnd_877125 : Nat := 4983230072969 + 3 ^ 40 * 877125 * 2
def baseEnd_877125 : Nat := 200171875144438212490525

theorem tailTrace_877125 : CollatzResearch.WordTrace tailWord_877125 prefixEnd_877125 200171875144438212490525 := by
  unfold tailWord_877125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991376947333400868840829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21327584631555600579227219 31991376947333400868840829)
  ·
    refine ⟨11996766355250025325815311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31991376947333400868840829 11996766355250025325815311)
    ·
      refine ⟨17995149532875037988722967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11996766355250025325815311 17995149532875037988722967)
      ·
        refine ⟨26992724299312556983084451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17995149532875037988722967 26992724299312556983084451)
        ·
          refine ⟨40489086448968835474626677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26992724299312556983084451 40489086448968835474626677)
          ·
            refine ⟨3795851854590828325746251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40489086448968835474626677 3795851854590828325746251)
            ·
              refine ⟨5693777781886242488619377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795851854590828325746251 5693777781886242488619377)
              ·
                refine ⟨4270333336414681866464533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693777781886242488619377 4270333336414681866464533)
                ·
                  refine ⟨200171875144438212490525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4270333336414681866464533 200171875144438212490525)
                  ·
                    rfl

theorem cell21_877125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_877125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877125 prefixEnd_877125 := by exact prefixLift 877125
  have htrace : WordTrace (prefixWord ++ tailWord_877125) baseStart_877125 baseEnd_877125 := by
    simpa [prefixWord, tailWord_877125, baseEnd_877125] using wordTrace_append hprefix tailTrace_877125
  have hstable : (prefixWord ++ tailWord_877125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877125).length < 2 ^ (prefixWord ++ tailWord_877125).sum := by decide
  have hdescent : baseEnd_877125 < baseStart_877125 := by decide
  rcases family_descends (prefixWord ++ tailWord_877125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877156 : List Nat := [2, 3, 1, 1, 2, 2, 4, 6]
def baseStart_877156 : Nat := 118140960795 + 877156 * 2 ^ 59
def prefixEnd_877156 : Nat := 4983230072969 + 3 ^ 40 * 877156 * 2
def baseEnd_877156 : Nat := 66726316588929682491265

theorem tailTrace_877156 : CollatzResearch.WordTrace tailWord_877156 prefixEnd_877156 66726316588929682491265 := by
  unfold tailWord_877156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996253805110546581609661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21328338406814062108812881 15996253805110546581609661)
  ·
    refine ⟨5998595176916454968103623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15996253805110546581609661 5998595176916454968103623)
    ·
      refine ⟨8997892765374682452155435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998595176916454968103623 8997892765374682452155435)
      ·
        refine ⟨13496839148062023678233153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997892765374682452155435 13496839148062023678233153)
        ·
          refine ⟨10122629361046517758674865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13496839148062023678233153 10122629361046517758674865)
          ·
            refine ⟨7591972020784888319006149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10122629361046517758674865 7591972020784888319006149)
            ·
              refine ⟨1423494753897166559813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7591972020784888319006149 1423494753897166559813653)
              ·
                refine ⟨66726316588929682491265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1423494753897166559813653 66726316588929682491265)
                ·
                  rfl

theorem cell21_877156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_877156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877156 prefixEnd_877156 := by exact prefixLift 877156
  have htrace : WordTrace (prefixWord ++ tailWord_877156) baseStart_877156 baseEnd_877156 := by
    simpa [prefixWord, tailWord_877156, baseEnd_877156] using wordTrace_append hprefix tailTrace_877156
  have hstable : (prefixWord ++ tailWord_877156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877156).length < 2 ^ (prefixWord ++ tailWord_877156).sum := by decide
  have hdescent : baseEnd_877156 < baseStart_877156 := by decide
  rcases family_descends (prefixWord ++ tailWord_877156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877308 : List Nat := [2, 2, 2, 1, 3, 4, 7]
def baseStart_877308 : Nat := 118140960795 + 877308 * 2 ^ 59
def prefixEnd_877308 : Nat := 4983230072969 + 3 ^ 40 * 877308 * 2
def baseEnd_877308 : Nat := 22245959804185617882239

theorem tailTrace_877308 : CollatzResearch.WordTrace tailWord_877308 prefixEnd_877308 22245959804185617882239 := by
  unfold tailWord_877308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999025752835211561376289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21332034337113615415168385 15999025752835211561376289)
  ·
    refine ⟨11999269314626408671032217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15999025752835211561376289 11999269314626408671032217)
    ·
      refine ⟨8999451985969806503274163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11999269314626408671032217 8999451985969806503274163)
      ·
        refine ⟨13499177978954709754911245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999451985969806503274163 13499177978954709754911245)
        ·
          refine ⟨5062191742108016158091717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13499177978954709754911245 5062191742108016158091717)
          ·
            refine ⟨949160951645253029642197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5062191742108016158091717 949160951645253029642197)
            ·
              refine ⟨22245959804185617882239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 949160951645253029642197 22245959804185617882239)
              ·
                rfl

theorem cell21_877308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 7].length) (baseStart_877308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877308 prefixEnd_877308 := by exact prefixLift 877308
  have htrace : WordTrace (prefixWord ++ tailWord_877308) baseStart_877308 baseEnd_877308 := by
    simpa [prefixWord, tailWord_877308, baseEnd_877308] using wordTrace_append hprefix tailTrace_877308
  have hstable : (prefixWord ++ tailWord_877308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877308).length < 2 ^ (prefixWord ++ tailWord_877308).sum := by decide
  have hdescent : baseEnd_877308 < baseStart_877308 := by decide
  rcases family_descends (prefixWord ++ tailWord_877308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877314 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_877314 : Nat := 118140960795 + 877314 * 2 ^ 59
def prefixEnd_877314 : Nat := 4983230072969 + 3 ^ 40 * 877314 * 2
def baseEnd_877314 : Nat := 200215007519415883840139

theorem tailTrace_877314 : CollatzResearch.WordTrace tailWord_877314 prefixEnd_877314 200215007519415883840139 := by
  unfold tailWord_877314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999567585912171536867749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21332180229099124098313997 7999567585912171536867749)
  ·
    refine ⟨1499918922358532163162703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7999567585912171536867749 1499918922358532163162703)
    ·
      refine ⟨2249878383537798244744055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499918922358532163162703 2249878383537798244744055)
      ·
        refine ⟨3374817575306697367116083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249878383537798244744055 3374817575306697367116083)
        ·
          refine ⟨5062226362960046050674125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374817575306697367116083 5062226362960046050674125)
          ·
            refine ⟨1898334886110017269002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5062226362960046050674125 1898334886110017269002797)
            ·
              refine ⟨711875582291256475876049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1898334886110017269002797 711875582291256475876049)
              ·
                refine ⟨533906686718442356907037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711875582291256475876049 533906686718442356907037)
                ·
                  refine ⟨200215007519415883840139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533906686718442356907037 200215007519415883840139)
                  ·
                    rfl

theorem cell21_877314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_877314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877314 prefixEnd_877314 := by exact prefixLift 877314
  have htrace : WordTrace (prefixWord ++ tailWord_877314) baseStart_877314 baseEnd_877314 := by
    simpa [prefixWord, tailWord_877314, baseEnd_877314] using wordTrace_append hprefix tailTrace_877314
  have hstable : (prefixWord ++ tailWord_877314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877314).length < 2 ^ (prefixWord ++ tailWord_877314).sum := by decide
  have hdescent : baseEnd_877314 < baseStart_877314 := by decide
  rcases family_descends (prefixWord ++ tailWord_877314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877373 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 3]
def baseStart_877373 : Nat := 118140960795 + 877373 * 2 ^ 59
def prefixEnd_877373 : Nat := 4983230072969 + 3 ^ 40 * 877373 * 2
def baseEnd_877373 : Nat := 200228472123244892356685

theorem tailTrace_877373 : CollatzResearch.WordTrace tailWord_877373 prefixEnd_877373 200228472123244892356685 := by
  unfold tailWord_877373
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000422250434939223868773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21333614833623292815912515 32000422250434939223868773)
  ·
    refine ⟨6000079171956551104475395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32000422250434939223868773 6000079171956551104475395)
    ·
      refine ⟨9000118757934826656713093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6000079171956551104475395 9000118757934826656713093)
      ·
        refine ⟨1687522267112779998133705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9000118757934826656713093 1687522267112779998133705)
        ·
          refine ⟨1265641700334584998600279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1687522267112779998133705 1265641700334584998600279)
          ·
            refine ⟨1898462550501877497900419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265641700334584998600279 1898462550501877497900419)
            ·
              refine ⟨2847693825752816246850629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898462550501877497900419 2847693825752816246850629)
              ·
                refine ⟨533942592328653046284493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847693825752816246850629 533942592328653046284493)
                ·
                  refine ⟨200228472123244892356685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533942592328653046284493 200228472123244892356685)
                  ·
                    rfl

theorem cell21_877373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_877373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877373 prefixEnd_877373 := by exact prefixLift 877373
  have htrace : WordTrace (prefixWord ++ tailWord_877373) baseStart_877373 baseEnd_877373 := by
    simpa [prefixWord, tailWord_877373, baseEnd_877373] using wordTrace_append hprefix tailTrace_877373
  have hstable : (prefixWord ++ tailWord_877373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877373).length < 2 ^ (prefixWord ++ tailWord_877373).sum := by decide
  have hdescent : baseEnd_877373 < baseStart_877373 := by decide
  rcases family_descends (prefixWord ++ tailWord_877373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877443 : List Nat := [1, 1, 1, 3, 4, 1, 2, 8]
def baseStart_877443 : Nat := 118140960795 + 877443 * 2 ^ 59
def prefixEnd_877443 : Nat := 4983230072969 + 3 ^ 40 * 877443 * 2
def baseEnd_877443 : Nat := 66748149025646775396625

theorem tailTrace_877443 : CollatzResearch.WordTrace tailWord_877443 prefixEnd_877443 66748149025646775396625 := by
  unfold tailWord_877443
  simp only [CollatzResearch.WordTrace]
  refine ⟨32002975360181341178916983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21335316906787560785944655 32002975360181341178916983)
  ·
    refine ⟨48004463040272011768375475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32002975360181341178916983 48004463040272011768375475)
    ·
      refine ⟨72006694560408017652563213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48004463040272011768375475 72006694560408017652563213)
      ·
        refine ⟨27002510460153006619711205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72006694560408017652563213 27002510460153006619711205)
        ·
          refine ⟨5062970711278688741195851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27002510460153006619711205 5062970711278688741195851)
          ·
            refine ⟨7594456066918033111793777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062970711278688741195851 7594456066918033111793777)
            ·
              refine ⟨5695842050188524833845333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594456066918033111793777 5695842050188524833845333)
              ·
                refine ⟨66748149025646775396625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5695842050188524833845333 66748149025646775396625)
                ·
                  rfl

theorem cell21_877443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_877443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877443 prefixEnd_877443 := by exact prefixLift 877443
  have htrace : WordTrace (prefixWord ++ tailWord_877443) baseStart_877443 baseEnd_877443 := by
    simpa [prefixWord, tailWord_877443, baseEnd_877443] using wordTrace_append hprefix tailTrace_877443
  have hstable : (prefixWord ++ tailWord_877443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877443).length < 2 ^ (prefixWord ++ tailWord_877443).sum := by decide
  have hdescent : baseEnd_877443 < baseStart_877443 := by decide
  rcases family_descends (prefixWord ++ tailWord_877443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877460 : List Nat := [2, 4, 2, 1, 1, 1, 3, 7]
def baseStart_877460 : Nat := 118140960795 + 877460 * 2 ^ 59
def prefixEnd_877460 : Nat := 4983230072969 + 3 ^ 40 * 877460 * 2
def baseEnd_877460 : Nat := 66749442236184024802169

theorem tailTrace_877460 : CollatzResearch.WordTrace tailWord_877460 prefixEnd_877460 66749442236184024802169 := by
  unfold tailWord_877460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001797700559876541142917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21335730267413168721523889 16001797700559876541142917)
  ·
    refine ⟨3000337068854976851464297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16001797700559876541142917 3000337068854976851464297)
    ·
      refine ⟨2250252801641232638598223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000337068854976851464297 2250252801641232638598223)
      ·
        refine ⟨3375379202461848957897335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250252801641232638598223 3375379202461848957897335)
        ·
          refine ⟨5063068803692773436846003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375379202461848957897335 5063068803692773436846003)
          ·
            refine ⟨7594603205539160155269005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063068803692773436846003 7594603205539160155269005)
            ·
              refine ⟨2847976202077185058225877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594603205539160155269005 2847976202077185058225877)
              ·
                refine ⟨66749442236184024802169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2847976202077185058225877 66749442236184024802169)
                ·
                  rfl

theorem cell21_877460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_877460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877460 prefixEnd_877460 := by exact prefixLift 877460
  have htrace : WordTrace (prefixWord ++ tailWord_877460) baseStart_877460 baseEnd_877460 := by
    simpa [prefixWord, tailWord_877460, baseEnd_877460] using wordTrace_append hprefix tailTrace_877460
  have hstable : (prefixWord ++ tailWord_877460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877460).length < 2 ^ (prefixWord ++ tailWord_877460).sum := by decide
  have hdescent : baseEnd_877460 < baseStart_877460 := by decide
  rcases family_descends (prefixWord ++ tailWord_877460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877466 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_877466 : Nat := 118140960795 + 877466 * 2 ^ 59
def prefixEnd_877466 : Nat := 4983230072969 + 3 ^ 40 * 877466 * 2
def baseEnd_877466 : Nat := 200249695990297397306495

theorem tailTrace_877466 : CollatzResearch.WordTrace tailWord_877466 prefixEnd_877466 200249695990297397306495 := by
  unfold tailWord_877466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000953559774504026751063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21335876159398677404669501 8000953559774504026751063)
  ·
    refine ⟨12001430339661756040126595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000953559774504026751063 12001430339661756040126595)
    ·
      refine ⟨18002145509492634060189893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12001430339661756040126595 18002145509492634060189893)
      ·
        refine ⟨3375402283029868886285605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18002145509492634060189893 3375402283029868886285605)
        ·
          refine ⟨632887928068100416178551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3375402283029868886285605 632887928068100416178551)
          ·
            refine ⟨949331892102150624267827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632887928068100416178551 949331892102150624267827)
            ·
              refine ⟨1423997838153225936401741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949331892102150624267827 1423997838153225936401741)
              ·
                refine ⟨533999189307459726150653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1423997838153225936401741 533999189307459726150653)
                ·
                  refine ⟨200249695990297397306495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533999189307459726150653 200249695990297397306495)
                  ·
                    rfl

theorem cell21_877466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_877466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877466 prefixEnd_877466 := by exact prefixLift 877466
  have htrace : WordTrace (prefixWord ++ tailWord_877466) baseStart_877466 baseEnd_877466 := by
    simpa [prefixWord, tailWord_877466, baseEnd_877466] using wordTrace_append hprefix tailTrace_877466
  have hstable : (prefixWord ++ tailWord_877466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877466).length < 2 ^ (prefixWord ++ tailWord_877466).sum := by decide
  have hdescent : baseEnd_877466 < baseStart_877466 := by decide
  rcases family_descends (prefixWord ++ tailWord_877466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877519 : List Nat := [1, 1, 2, 1, 1, 6, 2, 7]
def baseStart_877519 : Nat := 118140960795 + 877519 * 2 ^ 59
def prefixEnd_877519 : Nat := 4983230072969 + 3 ^ 40 * 877519 * 2
def baseEnd_877519 : Nat := 66753930437460360974351

theorem tailTrace_877519 : CollatzResearch.WordTrace tailWord_877519 prefixEnd_877519 66753930437460360974351 := by
  unfold tailWord_877519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32005747307906006158683611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21337164871937337439122407 32005747307906006158683611)
  ·
    refine ⟨48008620961859009238025417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32005747307906006158683611 48008620961859009238025417)
    ·
      refine ⟨36006465721394256928519063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48008620961859009238025417 36006465721394256928519063)
      ·
        refine ⟨54009698582091385392778595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36006465721394256928519063 54009698582091385392778595)
        ·
          refine ⟨81014547873137078089167893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54009698582091385392778595 81014547873137078089167893)
          ·
            refine ⟨3797556931553300535429745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81014547873137078089167893 3797556931553300535429745)
            ·
              refine ⟨2848167698664975401572309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797556931553300535429745 2848167698664975401572309)
              ·
                refine ⟨66753930437460360974351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2848167698664975401572309 66753930437460360974351)
                ·
                  rfl

theorem cell21_877519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_877519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877519 prefixEnd_877519 := by exact prefixLift 877519
  have htrace : WordTrace (prefixWord ++ tailWord_877519) baseStart_877519 baseEnd_877519 := by
    simpa [prefixWord, tailWord_877519, baseEnd_877519] using wordTrace_append hprefix tailTrace_877519
  have hstable : (prefixWord ++ tailWord_877519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877519).length < 2 ^ (prefixWord ++ tailWord_877519).sum := by decide
  have hdescent : baseEnd_877519 < baseStart_877519 := by decide
  rcases family_descends (prefixWord ++ tailWord_877519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877626 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_877626 : Nat := 118140960795 + 877626 * 2 ^ 59
def prefixEnd_877626 : Nat := 4983230072969 + 3 ^ 40 * 877626 * 2
def baseEnd_877626 : Nat := 200286210170172674639501

theorem tailTrace_877626 : CollatzResearch.WordTrace tailWord_877626 prefixEnd_877626 200286210170172674639501 := by
  unfold tailWord_877626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002412479629590858207183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21339766612345575621885821 8002412479629590858207183)
  ·
    refine ⟨12003618719444386287310775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002412479629590858207183 12003618719444386287310775)
    ·
      refine ⟨18005428079166579430966163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12003618719444386287310775 18005428079166579430966163)
      ·
        refine ⟨27008142118749869146449245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18005428079166579430966163 27008142118749869146449245)
        ·
          refine ⟨10128053294531200929918467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27008142118749869146449245 10128053294531200929918467)
          ·
            refine ⟨15192079941796801394877701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128053294531200929918467 15192079941796801394877701)
            ·
              refine ⟨2848514989086900261539569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15192079941796801394877701 2848514989086900261539569)
              ·
                refine ⟨2136386241815175196154677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848514989086900261539569 2136386241815175196154677)
                ·
                  refine ⟨200286210170172674639501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136386241815175196154677 200286210170172674639501)
                  ·
                    rfl

theorem cell21_877626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_877626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877626 prefixEnd_877626 := by exact prefixLift 877626
  have htrace : WordTrace (prefixWord ++ tailWord_877626) baseStart_877626 baseEnd_877626 := by
    simpa [prefixWord, tailWord_877626, baseEnd_877626] using wordTrace_append hprefix tailTrace_877626
  have hstable : (prefixWord ++ tailWord_877626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877626).length < 2 ^ (prefixWord ++ tailWord_877626).sum := by decide
  have hdescent : baseEnd_877626 < baseStart_877626 := by decide
  rcases family_descends (prefixWord ++ tailWord_877626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877629 : List Nat := [1, 4, 1, 3, 1, 4, 2, 5]
def baseStart_877629 : Nat := 118140960795 + 877629 * 2 ^ 59
def prefixEnd_877629 : Nat := 4983230072969 + 3 ^ 40 * 877629 * 2
def baseEnd_877629 : Nat := 66762298270348445363165

theorem tailTrace_877629 : CollatzResearch.WordTrace tailWord_877629 prefixEnd_877629 66762298270348445363165 := by
  unfold tailWord_877629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009759337507494945187941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21339839558338329963458627 32009759337507494945187941)
  ·
    refine ⟨6001829875782655302222739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32009759337507494945187941 6001829875782655302222739)
    ·
      refine ⟨9002744813673982953334109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001829875782655302222739 9002744813673982953334109)
      ·
        refine ⟨3376029305127743607500291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9002744813673982953334109 3376029305127743607500291)
        ·
          refine ⟨5064043957691615411250437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376029305127743607500291 5064043957691615411250437)
          ·
            refine ⟨949508242067177889609457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5064043957691615411250437 949508242067177889609457)
            ·
              refine ⟨712131181550383417207093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949508242067177889609457 712131181550383417207093)
              ·
                refine ⟨66762298270348445363165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 712131181550383417207093 66762298270348445363165)
                ·
                  rfl

theorem cell21_877629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].length) (baseStart_877629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877629 prefixEnd_877629 := by exact prefixLift 877629
  have htrace : WordTrace (prefixWord ++ tailWord_877629) baseStart_877629 baseEnd_877629 := by
    simpa [prefixWord, tailWord_877629, baseEnd_877629] using wordTrace_append hprefix tailTrace_877629
  have hstable : (prefixWord ++ tailWord_877629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877629).length < 2 ^ (prefixWord ++ tailWord_877629).sum := by decide
  have hdescent : baseEnd_877629 < baseStart_877629 := by decide
  rcases family_descends (prefixWord ++ tailWord_877629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877640 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_877640 : Nat := 118140960795 + 877640 * 2 ^ 59
def prefixEnd_877640 : Nat := 4983230072969 + 3 ^ 40 * 877640 * 2
def baseEnd_877640 : Nat := 200289405160911761406139

theorem tailTrace_877640 : CollatzResearch.WordTrace tailWord_877640 prefixEnd_877640 200289405160911761406139 := by
  unfold tailWord_877640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005080270233821911919187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21340107026978429215892249 16005080270233821911919187)
  ·
    refine ⟨24007620405350732867878781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16005080270233821911919187 24007620405350732867878781)
    ·
      refine ⟨9002857652006524825454543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24007620405350732867878781 9002857652006524825454543)
      ·
        refine ⟨13504286478009787238181815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002857652006524825454543 13504286478009787238181815)
        ·
          refine ⟨20256429717014680857272723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504286478009787238181815 20256429717014680857272723)
          ·
            refine ⟨30384644575522021285909085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256429717014680857272723 30384644575522021285909085)
            ·
              refine ⟨11394241715820757982215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30384644575522021285909085 11394241715820757982215907)
              ·
                refine ⟨17091362573731136973323861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394241715820757982215907 17091362573731136973323861)
                ·
                  refine ⟨200289405160911761406139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17091362573731136973323861 200289405160911761406139)
                  ·
                    rfl

theorem cell21_877640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_877640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877640 prefixEnd_877640 := by exact prefixLift 877640
  have htrace : WordTrace (prefixWord ++ tailWord_877640) baseStart_877640 baseEnd_877640 := by
    simpa [prefixWord, tailWord_877640, baseEnd_877640] using wordTrace_append hprefix tailTrace_877640
  have hstable : (prefixWord ++ tailWord_877640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877640).length < 2 ^ (prefixWord ++ tailWord_877640).sum := by decide
  have hdescent : baseEnd_877640 < baseStart_877640 := by decide
  rcases family_descends (prefixWord ++ tailWord_877640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877671 : List Nat := [1, 1, 5, 1, 1, 3, 1, 8]
def baseStart_877671 : Nat := 118140960795 + 877671 * 2 ^ 59
def prefixEnd_877671 : Nat := 4983230072969 + 3 ^ 40 * 877671 * 2
def baseEnd_877671 : Nat := 66765493261087532129803

theorem tailTrace_877671 : CollatzResearch.WordTrace tailWord_877671 prefixEnd_877671 66765493261087532129803 := by
  unfold tailWord_877671
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011291203355336118216867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21340860802236890745477911 32011291203355336118216867)
  ·
    refine ⟨48016936805033004177325301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011291203355336118216867 48016936805033004177325301)
    ·
      refine ⟨4501587825471844141624247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48016936805033004177325301 4501587825471844141624247)
      ·
        refine ⟨6752381738207766212436371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501587825471844141624247 6752381738207766212436371)
        ·
          refine ⟨10128572607311649318654557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752381738207766212436371 10128572607311649318654557)
          ·
            refine ⟨3798214727741868494495459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10128572607311649318654557 3798214727741868494495459)
            ·
              refine ⟨5697322091612802741743189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798214727741868494495459 5697322091612802741743189)
              ·
                refine ⟨66765493261087532129803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5697322091612802741743189 66765493261087532129803)
                ·
                  rfl

theorem cell21_877671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_877671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877671 prefixEnd_877671 := by exact prefixLift 877671
  have htrace : WordTrace (prefixWord ++ tailWord_877671) baseStart_877671 baseEnd_877671 := by
    simpa [prefixWord, tailWord_877671, baseEnd_877671] using wordTrace_append hprefix tailTrace_877671
  have hstable : (prefixWord ++ tailWord_877671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877671).length < 2 ^ (prefixWord ++ tailWord_877671).sum := by decide
  have hdescent : baseEnd_877671 < baseStart_877671 := by decide
  rcases family_descends (prefixWord ++ tailWord_877671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877674 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_877674 : Nat := 118140960795 + 877674 * 2 ^ 59
def prefixEnd_877674 : Nat := 4983230072969 + 3 ^ 40 * 877674 * 2
def baseEnd_877674 : Nat := 200297164424135257839403

theorem tailTrace_877674 : CollatzResearch.WordTrace tailWord_877674 prefixEnd_877674 200297164424135257839403 := by
  unfold tailWord_877674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002850155586116907644019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21340933748229645087050717 8002850155586116907644019)
  ·
    refine ⟨12004275233379175361466029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002850155586116907644019 12004275233379175361466029)
    ·
      refine ⟨4501603212517190760549761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12004275233379175361466029 4501603212517190760549761)
      ·
        refine ⟨3376202409387893070412321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501603212517190760549761 3376202409387893070412321)
        ·
          refine ⟨2532151807040919802809241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376202409387893070412321 2532151807040919802809241)
          ·
            refine ⟨1899113855280689852106931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532151807040919802809241 1899113855280689852106931)
            ·
              refine ⟨2848670782921034778160397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899113855280689852106931 2848670782921034778160397)
              ·
                refine ⟨1068251543595388041810149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848670782921034778160397 1068251543595388041810149)
                ·
                  refine ⟨200297164424135257839403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068251543595388041810149 200297164424135257839403)
                  ·
                    rfl

theorem cell21_877674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_877674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877674 prefixEnd_877674 := by exact prefixLift 877674
  have htrace : WordTrace (prefixWord ++ tailWord_877674) baseStart_877674 baseEnd_877674 := by
    simpa [prefixWord, tailWord_877674, baseEnd_877674] using wordTrace_append hprefix tailTrace_877674
  have hstable : (prefixWord ++ tailWord_877674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877674).length < 2 ^ (prefixWord ++ tailWord_877674).sum := by decide
  have hdescent : baseEnd_877674 < baseStart_877674 := by decide
  rcases family_descends (prefixWord ++ tailWord_877674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877733 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_877733 : Nat := 118140960795 + 877733 * 2 ^ 59
def prefixEnd_877733 : Nat := 4983230072969 + 3 ^ 40 * 877733 * 2
def baseEnd_877733 : Nat := 200310629027964266355949

theorem tailTrace_877733 : CollatzResearch.WordTrace tailWord_877733 prefixEnd_877733 200310629027964266355949 := by
  unfold tailWord_877733
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013552529130720706973853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21342368352753813804649235 32013552529130720706973853)
  ·
    refine ⟨12005082198424020265115195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32013552529130720706973853 12005082198424020265115195)
    ·
      refine ⟨18007623297636030397672793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005082198424020265115195 18007623297636030397672793)
      ·
        refine ⟨13505717473227022798254595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18007623297636030397672793 13505717473227022798254595)
        ·
          refine ⟨20258576209840534197381893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13505717473227022798254595 20258576209840534197381893)
          ·
            refine ⟨3798483039345100162009105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20258576209840534197381893 3798483039345100162009105)
            ·
              refine ⟨2848862279508825121506829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798483039345100162009105 2848862279508825121506829)
              ·
                refine ⟨1068323354815809420565061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848862279508825121506829 1068323354815809420565061)
                ·
                  refine ⟨200310629027964266355949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068323354815809420565061 200310629027964266355949)
                  ·
                    rfl

theorem cell21_877733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_877733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877733 prefixEnd_877733 := by exact prefixLift 877733
  have htrace : WordTrace (prefixWord ++ tailWord_877733) baseStart_877733 baseEnd_877733 := by
    simpa [prefixWord, tailWord_877733, baseEnd_877733] using wordTrace_append hprefix tailTrace_877733
  have hstable : (prefixWord ++ tailWord_877733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877733).length < 2 ^ (prefixWord ++ tailWord_877733).sum := by decide
  have hdescent : baseEnd_877733 < baseStart_877733 := by decide
  rcases family_descends (prefixWord ++ tailWord_877733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877764 : List Nat := [2, 3, 3, 1, 3, 1, 8]
def baseStart_877764 : Nat := 118140960795 + 877764 * 2 ^ 59
def prefixEnd_877764 : Nat := 4983230072969 + 3 ^ 40 * 877764 * 2
def baseEnd_877764 : Nat := 22257522627812789037691

theorem tailTrace_877764 : CollatzResearch.WordTrace tailWord_877764 prefixEnd_877764 22257522627812789037691 := by
  unfold tailWord_877764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007341596009206500676173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21343122128012275334234897 16007341596009206500676173)
  ·
    refine ⟨6002753098503452437753565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16007341596009206500676173 6002753098503452437753565)
    ·
      refine ⟨2251032411938794664157587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6002753098503452437753565 2251032411938794664157587)
      ·
        refine ⟨3376548617908191996236381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251032411938794664157587 3376548617908191996236381)
        ·
          refine ⟨1266205731715571998588643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3376548617908191996236381 1266205731715571998588643)
          ·
            refine ⟨1899308597573357997882965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266205731715571998588643 1899308597573357997882965)
            ·
              refine ⟨22257522627812789037691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1899308597573357997882965 22257522627812789037691)
              ·
                rfl

theorem cell21_877764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 8].length) (baseStart_877764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877764 prefixEnd_877764 := by exact prefixLift 877764
  have htrace : WordTrace (prefixWord ++ tailWord_877764) baseStart_877764 baseEnd_877764 := by
    simpa [prefixWord, tailWord_877764, baseEnd_877764] using wordTrace_append hprefix tailTrace_877764
  have hstable : (prefixWord ++ tailWord_877764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877764).length < 2 ^ (prefixWord ++ tailWord_877764).sum := by decide
  have hdescent : baseEnd_877764 < baseStart_877764 := by decide
  rcases family_descends (prefixWord ++ tailWord_877764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877823 : List Nat := [1, 1, 2, 2, 1, 7, 7]
def baseStart_877823 : Nat := 118140960795 + 877823 * 2 ^ 59
def prefixEnd_877823 : Nat := 4983230072969 + 3 ^ 40 * 877823 * 2
def baseEnd_877823 : Nat := 22259018694904901095085

theorem tailTrace_877823 : CollatzResearch.WordTrace tailWord_877823 prefixEnd_877823 22259018694904901095085 := by
  unfold tailWord_877823
  simp only [CollatzResearch.WordTrace]
  refine ⟨32016835098804666077750123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21344556732536444051833415 32016835098804666077750123)
  ·
    refine ⟨48025252648206999116625185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32016835098804666077750123 48025252648206999116625185)
    ·
      refine ⟨36018939486155249337468889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48025252648206999116625185 36018939486155249337468889)
      ·
        refine ⟨27014204614616437003101667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36018939486155249337468889 27014204614616437003101667)
        ·
          refine ⟨40521306921924655504652501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27014204614616437003101667 40521306921924655504652501)
          ·
            refine ⟨949718130982609113390293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 40521306921924655504652501 949718130982609113390293)
            ·
              refine ⟨22259018694904901095085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 949718130982609113390293 22259018694904901095085)
              ·
                rfl

theorem cell21_877823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 7].length) (baseStart_877823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877823 prefixEnd_877823 := by exact prefixLift 877823
  have htrace : WordTrace (prefixWord ++ tailWord_877823) baseStart_877823 baseEnd_877823 := by
    simpa [prefixWord, tailWord_877823, baseEnd_877823] using wordTrace_append hprefix tailTrace_877823
  have hstable : (prefixWord ++ tailWord_877823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877823).length < 2 ^ (prefixWord ++ tailWord_877823).sum := by decide
  have hdescent : baseEnd_877823 < baseStart_877823 := by decide
  rcases family_descends (prefixWord ++ tailWord_877823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877913 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_877913 : Nat := 118140960795 + 877913 * 2 ^ 59
def prefixEnd_877913 : Nat := 4983230072969 + 3 ^ 40 * 877913 * 2
def baseEnd_877913 : Nat := 200351707480323953355581

theorem tailTrace_877913 : CollatzResearch.WordTrace tailWord_877913 prefixEnd_877913 200351707480323953355581 := by
  unfold tailWord_877913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020117668478611448526393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21346745112319074299017595 32020117668478611448526393)
  ·
    refine ⟨24015088251358958586394795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32020117668478611448526393 24015088251358958586394795)
    ·
      refine ⟨36022632377038437879592193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24015088251358958586394795 36022632377038437879592193)
      ·
        refine ⟨27016974282778828409694145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36022632377038437879592193 27016974282778828409694145)
        ·
          refine ⟨20262730712084121307270609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27016974282778828409694145 20262730712084121307270609)
          ·
            refine ⟨15197048034063090980452957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20262730712084121307270609 15197048034063090980452957)
            ·
              refine ⟨5698893012773659117669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15197048034063090980452957 5698893012773659117669859)
              ·
                refine ⟨8548339519160488676504789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698893012773659117669859 8548339519160488676504789)
                ·
                  refine ⟨200351707480323953355581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8548339519160488676504789 200351707480323953355581)
                  ·
                    rfl

theorem cell21_877913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_877913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_877913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_877913 prefixEnd_877913 := by exact prefixLift 877913
  have htrace : WordTrace (prefixWord ++ tailWord_877913) baseStart_877913 baseEnd_877913 := by
    simpa [prefixWord, tailWord_877913, baseEnd_877913] using wordTrace_append hprefix tailTrace_877913
  have hstable : (prefixWord ++ tailWord_877913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877913).length < 2 ^ (prefixWord ++ tailWord_877913).sum := by decide
  have hdescent : baseEnd_877913 < baseStart_877913 := by decide
  rcases family_descends (prefixWord ++ tailWord_877913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878012 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_878012 : Nat := 118140960795 + 878012 * 2 ^ 59
def prefixEnd_878012 : Nat := 4983230072969 + 3 ^ 40 * 878012 * 2
def baseEnd_878012 : Nat := 200374300629121781205379

theorem tailTrace_878012 : CollatzResearch.WordTrace tailWord_878012 prefixEnd_878012 200374300629121781205379 := by
  unfold tailWord_878012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16011864247559975678190145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21349152330079967570920193 16011864247559975678190145)
  ·
    refine ⟨12008898185669981758642609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16011864247559975678190145 12008898185669981758642609)
    ·
      refine ⟨9006673639252486318981957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12008898185669981758642609 9006673639252486318981957)
      ·
        refine ⟨1688751307359841184809117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9006673639252486318981957 1688751307359841184809117)
        ·
          refine ⟨633281740259940444303419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688751307359841184809117 633281740259940444303419)
          ·
            refine ⟨949922610389910666455129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633281740259940444303419 949922610389910666455129)
            ·
              refine ⟨712441957792432999841347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949922610389910666455129 712441957792432999841347)
              ·
                refine ⟨1068662936688649499762021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712441957792432999841347 1068662936688649499762021)
                ·
                  refine ⟨200374300629121781205379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068662936688649499762021 200374300629121781205379)
                  ·
                    rfl

theorem cell21_878012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_878012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878012 prefixEnd_878012 := by exact prefixLift 878012
  have htrace : WordTrace (prefixWord ++ tailWord_878012) baseStart_878012 baseEnd_878012 := by
    simpa [prefixWord, tailWord_878012, baseEnd_878012] using wordTrace_append hprefix tailTrace_878012
  have hstable : (prefixWord ++ tailWord_878012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878012).length < 2 ^ (prefixWord ++ tailWord_878012).sum := by decide
  have hdescent : baseEnd_878012 < baseStart_878012 := by decide
  rcases family_descends (prefixWord ++ tailWord_878012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878099 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 3]
def baseStart_878099 : Nat := 118140960795 + 878099 * 2 ^ 59
def prefixEnd_878099 : Nat := 4983230072969 + 3 ^ 40 * 878099 * 2
def baseEnd_878099 : Nat := 200394155214428963255201

theorem tailTrace_878099 : CollatzResearch.WordTrace tailWord_878099 prefixEnd_878099 200394155214428963255201 := by
  unfold tailWord_878099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026901645804765214797351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21351267763869843476531567 32026901645804765214797351)
  ·
    refine ⟨48040352468707147822196027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32026901645804765214797351 48040352468707147822196027)
    ·
      refine ⟨72060528703060721733294041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48040352468707147822196027 72060528703060721733294041)
      ·
        refine ⟨54045396527295541299970531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72060528703060721733294041 54045396527295541299970531)
        ·
          refine ⟨81068094790943311949955797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54045396527295541299970531 81068094790943311949955797)
          ·
            refine ⟨1900033471662733873827089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81068094790943311949955797 1900033471662733873827089)
            ·
              refine ⟨1425025103747050405370317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900033471662733873827089 1425025103747050405370317)
              ·
                refine ⟨534384413905143902013869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425025103747050405370317 534384413905143902013869)
                ·
                  refine ⟨200394155214428963255201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534384413905143902013869 200394155214428963255201)
                  ·
                    rfl

theorem cell21_878099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].length) (baseStart_878099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878099 prefixEnd_878099 := by exact prefixLift 878099
  have htrace : WordTrace (prefixWord ++ tailWord_878099) baseStart_878099 baseEnd_878099 := by
    simpa [prefixWord, tailWord_878099, baseEnd_878099] using wordTrace_append hprefix tailTrace_878099
  have hstable : (prefixWord ++ tailWord_878099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878099).length < 2 ^ (prefixWord ++ tailWord_878099).sum := by decide
  have hdescent : baseEnd_878099 < baseStart_878099 := by decide
  rcases family_descends (prefixWord ++ tailWord_878099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878113 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_878113 : Nat := 118140960795 + 878113 * 2 ^ 59
def prefixEnd_878113 : Nat := 4983230072969 + 3 ^ 40 * 878113 * 2
def baseEnd_878113 : Nat := 200397350205168050021839

theorem tailTrace_878113 : CollatzResearch.WordTrace tailWord_878113 prefixEnd_878113 200397350205168050021839 := by
  unfold tailWord_878113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027412267754045605806993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21351608178502697070537995 32027412267754045605806993)
  ·
    refine ⟨24020559200815534204355245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32027412267754045605806993 24020559200815534204355245)
    ·
      refine ⟨9007709700305825326633217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24020559200815534204355245 9007709700305825326633217)
      ·
        refine ⟨6755782275229368994974913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9007709700305825326633217 6755782275229368994974913)
        ·
          refine ⟨5066836706422026746231185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6755782275229368994974913 5066836706422026746231185)
          ·
            refine ⟨3800127529816520059673389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066836706422026746231185 3800127529816520059673389)
            ·
              refine ⟨1425047823681195022377521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3800127529816520059673389 1425047823681195022377521)
              ·
                refine ⟨1068785867760896266783141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425047823681195022377521 1068785867760896266783141)
                ·
                  refine ⟨200397350205168050021839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068785867760896266783141 200397350205168050021839)
                  ·
                    rfl

theorem cell21_878113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_878113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878113 prefixEnd_878113 := by exact prefixLift 878113
  have htrace : WordTrace (prefixWord ++ tailWord_878113) baseStart_878113 baseEnd_878113 := by
    simpa [prefixWord, tailWord_878113, baseEnd_878113] using wordTrace_append hprefix tailTrace_878113
  have hstable : (prefixWord ++ tailWord_878113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878113).length < 2 ^ (prefixWord ++ tailWord_878113).sum := by decide
  have hdescent : baseEnd_878113 < baseStart_878113 := by decide
  rcases family_descends (prefixWord ++ tailWord_878113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878150 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_878150 : Nat := 118140960795 + 878150 * 2 ^ 59
def prefixEnd_878150 : Nat := 4983230072969 + 3 ^ 40 * 878150 * 2
def baseEnd_878150 : Nat := 200405794109264207905097

theorem tailTrace_878150 : CollatzResearch.WordTrace tailWord_878150 prefixEnd_878150 200405794109264207905097 := by
  unfold tailWord_878150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000898805269375028903247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21352507845746667283269269 1000898805269375028903247)
  ·
    refine ⟨1501348207904062543354871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000898805269375028903247 1501348207904062543354871)
    ·
      refine ⟨2252022311856093815032307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501348207904062543354871 2252022311856093815032307)
      ·
        refine ⟨3378033467784140722548461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252022311856093815032307 3378033467784140722548461)
        ·
          refine ⟨1266762550419052770955673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3378033467784140722548461 1266762550419052770955673)
          ·
            refine ⟨950071912814289578216755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266762550419052770955673 950071912814289578216755)
            ·
              refine ⟨1425107869221434367325133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950071912814289578216755 1425107869221434367325133)
              ·
                refine ⟨534415450958037887746925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425107869221434367325133 534415450958037887746925)
                ·
                  refine ⟨200405794109264207905097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534415450958037887746925 200405794109264207905097)
                  ·
                    rfl

theorem cell21_878150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_878150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878150 prefixEnd_878150 := by exact prefixLift 878150
  have htrace : WordTrace (prefixWord ++ tailWord_878150) baseStart_878150 baseEnd_878150 := by
    simpa [prefixWord, tailWord_878150, baseEnd_878150] using wordTrace_append hprefix tailTrace_878150
  have hstable : (prefixWord ++ tailWord_878150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878150).length < 2 ^ (prefixWord ++ tailWord_878150).sum := by decide
  have hdescent : baseEnd_878150 < baseStart_878150 := by decide
  rcases family_descends (prefixWord ++ tailWord_878150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878226 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_878226 : Nat := 118140960795 + 878226 * 2 ^ 59
def prefixEnd_878226 : Nat := 4983230072969 + 3 ^ 40 * 878226 * 2
def baseEnd_878226 : Nat := 200423138344704964638275

theorem tailTrace_878226 : CollatzResearch.WordTrace tailWord_878226 prefixEnd_878226 200423138344704964638275 := by
  unfold tailWord_878226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007883429086166476167633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21354355810896443936447021 8007883429086166476167633)
  ·
    refine ⟨6005912571814624857125725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8007883429086166476167633 6005912571814624857125725)
    ·
      refine ⟨2252217214430484321422147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005912571814624857125725 2252217214430484321422147)
      ·
        refine ⟨3378325821645726482133221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252217214430484321422147 3378325821645726482133221)
        ·
          refine ⟨633436091558573715399979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3378325821645726482133221 633436091558573715399979)
          ·
            refine ⟨950154137337860573099969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633436091558573715399979 950154137337860573099969)
            ·
              refine ⟨712615603003395429824977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950154137337860573099969 712615603003395429824977)
              ·
                refine ⟨534461702252546572368733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712615603003395429824977 534461702252546572368733)
                ·
                  refine ⟨200423138344704964638275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534461702252546572368733 200423138344704964638275)
                  ·
                    rfl

theorem cell21_878226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_878226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878226 prefixEnd_878226 := by exact prefixLift 878226
  have htrace : WordTrace (prefixWord ++ tailWord_878226) baseStart_878226 baseEnd_878226 := by
    simpa [prefixWord, tailWord_878226, baseEnd_878226] using wordTrace_append hprefix tailTrace_878226
  have hstable : (prefixWord ++ tailWord_878226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878226).length < 2 ^ (prefixWord ++ tailWord_878226).sum := by decide
  have hdescent : baseEnd_878226 < baseStart_878226 := by decide
  rcases family_descends (prefixWord ++ tailWord_878226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878282 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_878282 : Nat := 118140960795 + 878282 * 2 ^ 59
def prefixEnd_878282 : Nat := 4983230072969 + 3 ^ 40 * 878282 * 2
def baseEnd_878282 : Nat := 200435918307661311704827

theorem tailTrace_878282 : CollatzResearch.WordTrace tailWord_878282 prefixEnd_878282 200435918307661311704827 := by
  unfold tailWord_878282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008394051035446867177275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21355717469427858312472733 8008394051035446867177275)
  ·
    refine ⟨12012591076553170300765913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8008394051035446867177275 12012591076553170300765913)
    ·
      refine ⟨9009443307414877725574435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12012591076553170300765913 9009443307414877725574435)
      ·
        refine ⟨13514164961122316588361653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009443307414877725574435 13514164961122316588361653)
        ·
          refine ⟨1266952965105217180158905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13514164961122316588361653 1266952965105217180158905)
          ·
            refine ⟨950214723828912885119179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266952965105217180158905 950214723828912885119179)
            ·
              refine ⟨1425322085743369327678769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950214723828912885119179 1425322085743369327678769)
              ·
                refine ⟨1068991564307526995759077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425322085743369327678769 1068991564307526995759077)
                ·
                  refine ⟨200435918307661311704827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068991564307526995759077 200435918307661311704827)
                  ·
                    rfl

theorem cell21_878282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_878282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878282 prefixEnd_878282 := by exact prefixLift 878282
  have htrace : WordTrace (prefixWord ++ tailWord_878282) baseStart_878282 baseEnd_878282 := by
    simpa [prefixWord, tailWord_878282, baseEnd_878282] using wordTrace_append hprefix tailTrace_878282
  have hstable : (prefixWord ++ tailWord_878282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878282).length < 2 ^ (prefixWord ++ tailWord_878282).sum := by decide
  have hdescent : baseEnd_878282 < baseStart_878282 := by decide
  rcases family_descends (prefixWord ++ tailWord_878282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878403 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 3]
def baseStart_878403 : Nat := 118140960795 + 878403 * 2 ^ 59
def prefixEnd_878403 : Nat := 4983230072969 + 3 ^ 40 * 878403 * 2
def baseEnd_878403 : Nat := 200463532156191990187913

theorem tailTrace_878403 : CollatzResearch.WordTrace tailWord_878403 prefixEnd_878403 200463532156191990187913 := by
  unfold tailWord_878403
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037989436703425133863863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21358659624468950089242575 32037989436703425133863863)
  ·
    refine ⟨48056984155055137700795795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32037989436703425133863863 48056984155055137700795795)
    ·
      refine ⟨72085476232582706551193693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48056984155055137700795795 72085476232582706551193693)
      ·
        refine ⟨27032053587218514956697635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72085476232582706551193693 27032053587218514956697635)
        ·
          refine ⟨40548080380827772435046453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032053587218514956697635 40548080380827772435046453)
          ·
            refine ⟨3801382535702603665785605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40548080380827772435046453 3801382535702603665785605)
            ·
              refine ⟨712759225444238187334801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3801382535702603665785605 712759225444238187334801)
              ·
                refine ⟨534569419083178640501101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712759225444238187334801 534569419083178640501101)
                ·
                  refine ⟨200463532156191990187913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534569419083178640501101 200463532156191990187913)
                  ·
                    rfl

theorem cell21_878403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].length) (baseStart_878403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878403 prefixEnd_878403 := by exact prefixLift 878403
  have htrace : WordTrace (prefixWord ++ tailWord_878403) baseStart_878403 baseEnd_878403 := by
    simpa [prefixWord, tailWord_878403, baseEnd_878403] using wordTrace_append hprefix tailTrace_878403
  have hstable : (prefixWord ++ tailWord_878403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878403).length < 2 ^ (prefixWord ++ tailWord_878403).sum := by decide
  have hdescent : baseEnd_878403 < baseStart_878403 := by decide
  rcases family_descends (prefixWord ++ tailWord_878403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878431 : List Nat := [1, 1, 2, 3, 1, 5, 3, 5]
def baseStart_878431 : Nat := 118140960795 + 878431 * 2 ^ 59
def prefixEnd_878431 : Nat := 4983230072969 + 3 ^ 40 * 878431 * 2
def baseEnd_878431 : Nat := 66823307379223387907063

theorem tailTrace_878431 : CollatzResearch.WordTrace tailWord_878431 prefixEnd_878431 66823307379223387907063 := by
  unfold tailWord_878431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32039010680601985915883147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21359340453734657277255431 32039010680601985915883147)
  ·
    refine ⟨48058516020902978873824721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32039010680601985915883147 48058516020902978873824721)
    ·
      refine ⟨36043887015677234155368541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48058516020902978873824721 36043887015677234155368541)
      ·
        refine ⟨13516457630878962808263203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36043887015677234155368541 13516457630878962808263203)
        ·
          refine ⟨20274686446318444212394805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516457630878962808263203 20274686446318444212394805)
          ·
            refine ⟨1900751854342354144912013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20274686446318444212394805 1900751854342354144912013)
            ·
              refine ⟨712781945378382804342005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900751854342354144912013 712781945378382804342005)
              ·
                refine ⟨66823307379223387907063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 712781945378382804342005 66823307379223387907063)
                ·
                  rfl

theorem cell21_878431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].length) (baseStart_878431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878431 prefixEnd_878431 := by exact prefixLift 878431
  have htrace : WordTrace (prefixWord ++ tailWord_878431) baseStart_878431 baseEnd_878431 := by
    simpa [prefixWord, tailWord_878431, baseEnd_878431] using wordTrace_append hprefix tailTrace_878431
  have hstable : (prefixWord ++ tailWord_878431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878431).length < 2 ^ (prefixWord ++ tailWord_878431).sum := by decide
  have hdescent : baseEnd_878431 < baseStart_878431 := by decide
  rcases family_descends (prefixWord ++ tailWord_878431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878524 : List Nat := [2, 2, 2, 5, 1, 1, 2, 6]
def baseStart_878524 : Nat := 118140960795 + 878524 * 2 ^ 59
def prefixEnd_878524 : Nat := 4983230072969 + 3 ^ 40 * 878524 * 2
def baseEnd_878524 : Nat := 66830382001574222890333

theorem tailTrace_878524 : CollatzResearch.WordTrace tailWord_878524 prefixEnd_878524 66830382001574222890333 := by
  unfold tailWord_878524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021201334632531399509313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21361601779510041866012417 16021201334632531399509313)
  ·
    refine ⟨12015901000974398549631985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16021201334632531399509313 12015901000974398549631985)
    ·
      refine ⟨9011925750730798912223989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015901000974398549631985 9011925750730798912223989)
      ·
        refine ⟨844868039131012398020999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9011925750730798912223989 844868039131012398020999)
        ·
          refine ⟨1267302058696518597031499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844868039131012398020999 1267302058696518597031499)
          ·
            refine ⟨1900953088044777895547249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267302058696518597031499 1900953088044777895547249)
            ·
              refine ⟨1425714816033583421660437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900953088044777895547249 1425714816033583421660437)
              ·
                refine ⟨66830382001574222890333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1425714816033583421660437 66830382001574222890333)
                ·
                  rfl

theorem cell21_878524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_878524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878524 prefixEnd_878524 := by exact prefixLift 878524
  have htrace : WordTrace (prefixWord ++ tailWord_878524) baseStart_878524 baseEnd_878524 := by
    simpa [prefixWord, tailWord_878524, baseEnd_878524] using wordTrace_append hprefix tailTrace_878524
  have hstable : (prefixWord ++ tailWord_878524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878524).length < 2 ^ (prefixWord ++ tailWord_878524).sum := by decide
  have hdescent : baseEnd_878524 < baseStart_878524 := by decide
  rcases family_descends (prefixWord ++ tailWord_878524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878597 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_878597 : Nat := 118140960795 + 878597 * 2 ^ 59
def prefixEnd_878597 : Nat := 4983230072969 + 3 ^ 40 * 878597 * 2
def baseEnd_878597 : Nat := 200507805599290763954183

theorem tailTrace_878597 : CollatzResearch.WordTrace tailWord_878597 prefixEnd_878597 200507805599290763954183 := by
  unfold tailWord_878597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32045065198000596266426045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21363376798667064177617363 32045065198000596266426045)
  ·
    refine ⟨12016899449250223599909767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32045065198000596266426045 12016899449250223599909767)
    ·
      refine ⟨18025349173875335399864651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12016899449250223599909767 18025349173875335399864651)
      ·
        refine ⟨27038023760813003099796977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18025349173875335399864651 27038023760813003099796977)
        ·
          refine ⟨20278517820609752324847733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27038023760813003099796977 20278517820609752324847733)
          ·
            refine ⟨1901111045682164280454475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20278517820609752324847733 1901111045682164280454475)
            ·
              refine ⟨2851666568523246420681713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901111045682164280454475 2851666568523246420681713)
              ·
                refine ⟨2138749926392434815511285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851666568523246420681713 2138749926392434815511285)
                ·
                  refine ⟨200507805599290763954183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138749926392434815511285 200507805599290763954183)
                  ·
                    rfl

theorem cell21_878597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_878597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878597 prefixEnd_878597 := by exact prefixLift 878597
  have htrace : WordTrace (prefixWord ++ tailWord_878597) baseStart_878597 baseEnd_878597 := by
    simpa [prefixWord, tailWord_878597, baseEnd_878597] using wordTrace_append hprefix tailTrace_878597
  have hstable : (prefixWord ++ tailWord_878597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878597).length < 2 ^ (prefixWord ++ tailWord_878597).sum := by decide
  have hdescent : baseEnd_878597 < baseStart_878597 := by decide
  rcases family_descends (prefixWord ++ tailWord_878597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878631 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_878631 : Nat := 118140960795 + 878631 * 2 ^ 59
def prefixEnd_878631 : Nat := 4983230072969 + 3 ^ 40 * 878631 * 2
def baseEnd_878631 : Nat := 200515564862514260387447

theorem tailTrace_878631 : CollatzResearch.WordTrace tailWord_878631 prefixEnd_878631 200515564862514260387447 := by
  unfold tailWord_878631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046305279877420073163747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21364203519918280048775831 32046305279877420073163747)
  ·
    refine ⟨48069457919816130109745621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32046305279877420073163747 48069457919816130109745621)
    ·
      refine ⟨1126627919995690549447163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48069457919816130109745621 1126627919995690549447163)
      ·
        refine ⟨1689941879993535824170745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126627919995690549447163 1689941879993535824170745)
        ·
          refine ⟨1267456409995151868128059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689941879993535824170745 1267456409995151868128059)
          ·
            refine ⟨1901184614992727802192089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267456409995151868128059 1901184614992727802192089)
            ·
              refine ⟨1425888461244545851644067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901184614992727802192089 1425888461244545851644067)
              ·
                refine ⟨2138832691866818777466101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425888461244545851644067 2138832691866818777466101)
                ·
                  refine ⟨200515564862514260387447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138832691866818777466101 200515564862514260387447)
                  ·
                    rfl

theorem cell21_878631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_878631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878631 prefixEnd_878631 := by exact prefixLift 878631
  have htrace : WordTrace (prefixWord ++ tailWord_878631) baseStart_878631 baseEnd_878631 := by
    simpa [prefixWord, tailWord_878631, baseEnd_878631] using wordTrace_append hprefix tailTrace_878631
  have hstable : (prefixWord ++ tailWord_878631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878631).length < 2 ^ (prefixWord ++ tailWord_878631).sum := by decide
  have hdescent : baseEnd_878631 < baseStart_878631 := by decide
  rcases family_descends (prefixWord ++ tailWord_878631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878704 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_878704 : Nat := 118140960795 + 878704 * 2 ^ 59
def prefixEnd_878704 : Nat := 4983230072969 + 3 ^ 40 * 878704 * 2
def baseEnd_878704 : Nat := 200532224457082355670631

theorem tailTrace_878704 : CollatzResearch.WordTrace tailWord_878704 prefixEnd_878704 200532224457082355670631 := by
  unfold tailWord_878704
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024483904306476770285583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21365978539075302360380777 16024483904306476770285583)
  ·
    refine ⟨24036725856459715155428375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16024483904306476770285583 24036725856459715155428375)
    ·
      refine ⟨36055088784689572733142563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036725856459715155428375 36055088784689572733142563)
      ·
        refine ⟨54082633177034359099713845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36055088784689572733142563 54082633177034359099713845)
        ·
          refine ⟨5070246860346971165598173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54082633177034359099713845 5070246860346971165598173)
          ·
            refine ⟨1901342572630114187099315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5070246860346971165598173 1901342572630114187099315)
            ·
              refine ⟨2852013858945171280648973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901342572630114187099315 2852013858945171280648973)
              ·
                refine ⟨1069505197104439230243365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852013858945171280648973 1069505197104439230243365)
                ·
                  refine ⟨200532224457082355670631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069505197104439230243365 200532224457082355670631)
                  ·
                    rfl

theorem cell21_878704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_878704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878704 prefixEnd_878704 := by exact prefixLift 878704
  have htrace : WordTrace (prefixWord ++ tailWord_878704) baseStart_878704 baseEnd_878704 := by
    simpa [prefixWord, tailWord_878704, baseEnd_878704] using wordTrace_append hprefix tailTrace_878704
  have hstable : (prefixWord ++ tailWord_878704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878704).length < 2 ^ (prefixWord ++ tailWord_878704).sum := by decide
  have hdescent : baseEnd_878704 < baseStart_878704 := by decide
  rcases family_descends (prefixWord ++ tailWord_878704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878842 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_878842 : Nat := 118140960795 + 878842 * 2 ^ 59
def prefixEnd_878842 : Nat := 4983230072969 + 3 ^ 40 * 878842 * 2
def baseEnd_878842 : Nat := 200563717937224782370349

theorem tailTrace_878842 : CollatzResearch.WordTrace tailWord_878842 prefixEnd_878842 200563717937224782370349 := by
  unfold tailWord_878842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013500270528250777273695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21369334054742002072729853 8013500270528250777273695)
  ·
    refine ⟨12020250405792376165910543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8013500270528250777273695 12020250405792376165910543)
    ·
      refine ⟨18030375608688564248865815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12020250405792376165910543 18030375608688564248865815)
      ·
        refine ⟨27045563413032846373298723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18030375608688564248865815 27045563413032846373298723)
        ·
          refine ⟨40568345119549269559948085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27045563413032846373298723 40568345119549269559948085)
          ·
            refine ⟨3803282354957744021245133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40568345119549269559948085 3803282354957744021245133)
            ·
              refine ⟨1426230883109154007966925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3803282354957744021245133 1426230883109154007966925)
              ·
                refine ⟨534836581165932752987597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426230883109154007966925 534836581165932752987597)
                ·
                  refine ⟨200563717937224782370349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534836581165932752987597 200563717937224782370349)
                  ·
                    rfl

theorem cell21_878842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_878842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878842 prefixEnd_878842 := by exact prefixLift 878842
  have htrace : WordTrace (prefixWord ++ tailWord_878842) baseStart_878842 baseEnd_878842 := by
    simpa [prefixWord, tailWord_878842, baseEnd_878842] using wordTrace_append hprefix tailTrace_878842
  have hstable : (prefixWord ++ tailWord_878842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878842).length < 2 ^ (prefixWord ++ tailWord_878842).sum := by decide
  have hdescent : baseEnd_878842 < baseStart_878842 := by decide
  rcases family_descends (prefixWord ++ tailWord_878842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878915 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_878915 : Nat := 118140960795 + 878915 * 2 ^ 59
def prefixEnd_878915 : Nat := 4983230072969 + 3 ^ 40 * 878915 * 2
def baseEnd_878915 : Nat := 200580377531792877653533

theorem tailTrace_878915 : CollatzResearch.WordTrace tailWord_878915 prefixEnd_878915 200580377531792877653533 := by
  unfold tailWord_878915
  simp only [CollatzResearch.WordTrace]
  refine ⟨32056663610848536576502199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21371109073899024384334799 32056663610848536576502199)
  ·
    refine ⟨48084995416272804864753299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32056663610848536576502199 48084995416272804864753299)
    ·
      refine ⟨72127493124409207297129949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48084995416272804864753299 72127493124409207297129949)
      ·
        refine ⟨27047809921653452736423731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72127493124409207297129949 27047809921653452736423731)
        ·
          refine ⟨40571714882480179104635597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27047809921653452736423731 40571714882480179104635597)
          ·
            refine ⟨15214393080930067164238349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40571714882480179104635597 15214393080930067164238349)
            ·
              refine ⟨5705397405348775186589381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15214393080930067164238349 5705397405348775186589381)
              ·
                refine ⟨1069762013502895347485509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5705397405348775186589381 1069762013502895347485509)
                ·
                  refine ⟨200580377531792877653533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069762013502895347485509 200580377531792877653533)
                  ·
                    rfl

theorem cell21_878915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_878915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878915 prefixEnd_878915 := by exact prefixLift 878915
  have htrace : WordTrace (prefixWord ++ tailWord_878915) baseStart_878915 baseEnd_878915 := by
    simpa [prefixWord, tailWord_878915, baseEnd_878915] using wordTrace_append hprefix tailTrace_878915
  have hstable : (prefixWord ++ tailWord_878915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878915).length < 2 ^ (prefixWord ++ tailWord_878915).sum := by decide
  have hdescent : baseEnd_878915 < baseStart_878915 := by decide
  rcases family_descends (prefixWord ++ tailWord_878915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878932 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_878932 : Nat := 118140960795 + 878932 * 2 ^ 59
def prefixEnd_878932 : Nat := 4983230072969 + 3 ^ 40 * 878932 * 2
def baseEnd_878932 : Nat := 200584257163404625870165

theorem tailTrace_878932 : CollatzResearch.WordTrace tailWord_878932 prefixEnd_878932 200584257163404625870165 := by
  unfold tailWord_878932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028641825893474239935525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21371522434524632319914033 16028641825893474239935525)
  ·
    refine ⟨3005370342355026419987911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16028641825893474239935525 3005370342355026419987911)
    ·
      refine ⟨4508055513532539629981867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005370342355026419987911 4508055513532539629981867)
      ·
        refine ⟨6762083270298809444972801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4508055513532539629981867 6762083270298809444972801)
        ·
          refine ⟨5071562452724107083729601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762083270298809444972801 5071562452724107083729601)
          ·
            refine ⟨3803671839543080312797201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5071562452724107083729601 3803671839543080312797201)
            ·
              refine ⟨2852753879657310234597901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803671839543080312797201 2852753879657310234597901)
              ·
                refine ⟨1069782704871491337974213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852753879657310234597901 1069782704871491337974213)
                ·
                  refine ⟨200584257163404625870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069782704871491337974213 200584257163404625870165)
                  ·
                    rfl

theorem cell21_878932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_878932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878932 prefixEnd_878932 := by exact prefixLift 878932
  have htrace : WordTrace (prefixWord ++ tailWord_878932) baseStart_878932 baseEnd_878932 := by
    simpa [prefixWord, tailWord_878932, baseEnd_878932] using wordTrace_append hprefix tailTrace_878932
  have hstable : (prefixWord ++ tailWord_878932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878932).length < 2 ^ (prefixWord ++ tailWord_878932).sum := by decide
  have hdescent : baseEnd_878932 < baseStart_878932 := by decide
  rcases family_descends (prefixWord ++ tailWord_878932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878977 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_878977 : Nat := 118140960795 + 878977 * 2 ^ 59
def prefixEnd_878977 : Nat := 4983230072969 + 3 ^ 40 * 878977 * 2
def baseEnd_878977 : Nat := 200594526776494547620073

theorem tailTrace_878977 : CollatzResearch.WordTrace tailWord_878977 prefixEnd_878977 200594526776494547620073 := by
  unfold tailWord_878977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058924936623921165259185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21372616624415947443506123 32058924936623921165259185)
  ·
    refine ⟨24044193702467940873944389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32058924936623921165259185 24044193702467940873944389)
    ·
      refine ⟨4508286319212738913864573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24044193702467940873944389 4508286319212738913864573)
      ·
        refine ⟨1690607369704777092699215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4508286319212738913864573 1690607369704777092699215)
        ·
          refine ⟨2535911054557165639048823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690607369704777092699215 2535911054557165639048823)
          ·
            refine ⟨3803866581835748458573235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535911054557165639048823 3803866581835748458573235)
            ·
              refine ⟨5705799872753622687859853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803866581835748458573235 5705799872753622687859853)
              ·
                refine ⟨2139674952282608507947445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5705799872753622687859853 2139674952282608507947445)
                ·
                  refine ⟨200594526776494547620073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2139674952282608507947445 200594526776494547620073)
                  ·
                    rfl

theorem cell21_878977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_878977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_878977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_878977 prefixEnd_878977 := by exact prefixLift 878977
  have htrace : WordTrace (prefixWord ++ tailWord_878977) baseStart_878977 baseEnd_878977 := by
    simpa [prefixWord, tailWord_878977, baseEnd_878977] using wordTrace_append hprefix tailTrace_878977
  have hstable : (prefixWord ++ tailWord_878977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878977).length < 2 ^ (prefixWord ++ tailWord_878977).sum := by decide
  have hdescent : baseEnd_878977 < baseStart_878977 := by decide
  rcases family_descends (prefixWord ++ tailWord_878977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879028 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_879028 : Nat := 118140960795 + 879028 * 2 ^ 59
def prefixEnd_879028 : Nat := 4983230072969 + 3 ^ 40 * 879028 * 2
def baseEnd_879028 : Nat := 200606165671329792269969

theorem tailTrace_879028 : CollatzResearch.WordTrace tailWord_879028 prefixEnd_879028 200606165671329792269969 := by
  unfold tailWord_879028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030392529719578437682869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21373856706292771250243825 16030392529719578437682869)
  ·
    refine ⟨1502849299661210478532769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16030392529719578437682869 1502849299661210478532769)
    ·
      refine ⟨1127136974745907858899577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502849299661210478532769 1127136974745907858899577)
      ·
        refine ⟨845352731059430894174683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127136974745907858899577 845352731059430894174683)
        ·
          refine ⟨1268029096589146341262025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845352731059430894174683 1268029096589146341262025)
          ·
            refine ⟨951021822441859755946519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268029096589146341262025 951021822441859755946519)
            ·
              refine ⟨1426532733662789633919779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951021822441859755946519 1426532733662789633919779)
              ·
                refine ⟨2139799100494184450879669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426532733662789633919779 2139799100494184450879669)
                ·
                  refine ⟨200606165671329792269969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2139799100494184450879669 200606165671329792269969)
                  ·
                    rfl

theorem cell21_879028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_879028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879028 prefixEnd_879028 := by exact prefixLift 879028
  have htrace : WordTrace (prefixWord ++ tailWord_879028) baseStart_879028 baseEnd_879028 := by
    simpa [prefixWord, tailWord_879028, baseEnd_879028] using wordTrace_append hprefix tailTrace_879028
  have hstable : (prefixWord ++ tailWord_879028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879028).length < 2 ^ (prefixWord ++ tailWord_879028).sum := by decide
  have hdescent : baseEnd_879028 < baseStart_879028 := by decide
  rcases family_descends (prefixWord ++ tailWord_879028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879146 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_879146 : Nat := 118140960795 + 879146 * 2 ^ 59
def prefixEnd_879146 : Nat := 4983230072969 + 3 ^ 40 * 879146 * 2
def baseEnd_879146 : Nat := 200633094878987809303061

theorem tailTrace_879146 : CollatzResearch.WordTrace tailWord_879146 prefixEnd_879146 200633094878987809303061 := by
  unfold tailWord_879146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8016272218252915757040323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21376725915341108685440861 8016272218252915757040323)
  ·
    refine ⟨12024408327379373635560485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8016272218252915757040323 12024408327379373635560485)
    ·
      refine ⟨2254576561383632556667591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12024408327379373635560485 2254576561383632556667591)
      ·
        refine ⟨3381864842075448835001387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254576561383632556667591 3381864842075448835001387)
        ·
          refine ⟨5072797263113173252502081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381864842075448835001387 5072797263113173252502081)
          ·
            refine ⟨3804597947334879939376561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072797263113173252502081 3804597947334879939376561)
            ·
              refine ⟨2853448460501159954532421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804597947334879939376561 2853448460501159954532421)
              ·
                refine ⟨535021586343967491474829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2853448460501159954532421 535021586343967491474829)
                ·
                  refine ⟨200633094878987809303061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535021586343967491474829 200633094878987809303061)
                  ·
                    rfl

theorem cell21_879146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_879146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879146 prefixEnd_879146 := by exact prefixLift 879146
  have htrace : WordTrace (prefixWord ++ tailWord_879146) baseStart_879146 baseEnd_879146 := by
    simpa [prefixWord, tailWord_879146, baseEnd_879146] using wordTrace_append hprefix tailTrace_879146
  have hstable : (prefixWord ++ tailWord_879146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879146).length < 2 ^ (prefixWord ++ tailWord_879146).sum := by decide
  have hdescent : baseEnd_879146 < baseStart_879146 := by decide
  rcases family_descends (prefixWord ++ tailWord_879146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879157 : List Nat := [1, 3, 3, 1, 1, 2, 2, 8]
def baseStart_879157 : Nat := 118140960795 + 879157 * 2 ^ 59
def prefixEnd_879157 : Nat := 4983230072969 + 3 ^ 40 * 879157 * 2
def baseEnd_879157 : Nat := 66878535076284744873235

theorem tailTrace_879157 : CollatzResearch.WordTrace tailWord_879157 prefixEnd_879157 66878535076284744873235 := by
  unfold tailWord_879157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32065490075971811906811725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21376993383981207937874483 32065490075971811906811725)
  ·
    refine ⟨12024558778489429465054397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32065490075971811906811725 12024558778489429465054397)
    ·
      refine ⟨4509209541933536049395399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12024558778489429465054397 4509209541933536049395399)
      ·
        refine ⟨6763814312900304074093099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509209541933536049395399 6763814312900304074093099)
        ·
          refine ⟨10145721469350456111139649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763814312900304074093099 10145721469350456111139649)
          ·
            refine ⟨7609291102012842083354737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145721469350456111139649 7609291102012842083354737)
            ·
              refine ⟨5706968326509631562516053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609291102012842083354737 5706968326509631562516053)
              ·
                refine ⟨66878535076284744873235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5706968326509631562516053 66878535076284744873235)
                ·
                  rfl

theorem cell21_879157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_879157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879157 prefixEnd_879157 := by exact prefixLift 879157
  have htrace : WordTrace (prefixWord ++ tailWord_879157) baseStart_879157 baseEnd_879157 := by
    simpa [prefixWord, tailWord_879157, baseEnd_879157] using wordTrace_append hprefix tailTrace_879157
  have hstable : (prefixWord ++ tailWord_879157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879157).length < 2 ^ (prefixWord ++ tailWord_879157).sum := by decide
  have hdescent : baseEnd_879157 < baseStart_879157 := by decide
  rcases family_descends (prefixWord ++ tailWord_879157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879160 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_879160 : Nat := 118140960795 + 879160 * 2 ^ 59
def prefixEnd_879160 : Nat := 4983230072969 + 3 ^ 40 * 879160 * 2
def baseEnd_879160 : Nat := 200636289869726896069699

theorem tailTrace_879160 : CollatzResearch.WordTrace tailWord_879160 prefixEnd_879160 200636289869726896069699 := by
  unfold tailWord_879160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032799747480471709585467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21377066329973962279447289 16032799747480471709585467)
  ·
    refine ⟨24049199621220707564378201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16032799747480471709585467 24049199621220707564378201)
    ·
      refine ⟨18036899715915530673283651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24049199621220707564378201 18036899715915530673283651)
      ·
        refine ⟨27055349573873296009925477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18036899715915530673283651 27055349573873296009925477)
        ·
          refine ⟨5072878045101243001861027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27055349573873296009925477 5072878045101243001861027)
          ·
            refine ⟨7609317067651864502791541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072878045101243001861027 7609317067651864502791541)
            ·
              refine ⟨713373475092362297136707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7609317067651864502791541 713373475092362297136707)
              ·
                refine ⟨1070060212638543445705061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713373475092362297136707 1070060212638543445705061)
                ·
                  refine ⟨200636289869726896069699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070060212638543445705061 200636289869726896069699)
                  ·
                    rfl

theorem cell21_879160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_879160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879160 prefixEnd_879160 := by exact prefixLift 879160
  have htrace : WordTrace (prefixWord ++ tailWord_879160) baseStart_879160 baseEnd_879160 := by
    simpa [prefixWord, tailWord_879160, baseEnd_879160] using wordTrace_append hprefix tailTrace_879160
  have hstable : (prefixWord ++ tailWord_879160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879160).length < 2 ^ (prefixWord ++ tailWord_879160).sum := by decide
  have hdescent : baseEnd_879160 < baseStart_879160 := by decide
  rcases family_descends (prefixWord ++ tailWord_879160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879233 : List Nat := [1, 2, 4, 2, 1, 1, 1, 9]
def baseStart_879233 : Nat := 118140960795 + 879233 * 2 ^ 59
def prefixEnd_879233 : Nat := 4983230072969 + 3 ^ 40 * 879233 * 2
def baseEnd_879233 : Nat := 66884316488098330450961

theorem tailTrace_879233 : CollatzResearch.WordTrace tailWord_879233 prefixEnd_879233 66884316488098330450961 := by
  unfold tailWord_879233
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068262023696476886578353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21378841349130984591052235 32068262023696476886578353)
  ·
    refine ⟨24051196517772357664933765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32068262023696476886578353 24051196517772357664933765)
    ·
      refine ⟨4509599347082317062175081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24051196517772357664933765 4509599347082317062175081)
      ·
        refine ⟨3382199510311737796631311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4509599347082317062175081 3382199510311737796631311)
        ·
          refine ⟨5073299265467606694946967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382199510311737796631311 5073299265467606694946967)
          ·
            refine ⟨7609948898201410042420451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073299265467606694946967 7609948898201410042420451)
            ·
              refine ⟨11414923347302115063630677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609948898201410042420451 11414923347302115063630677)
              ·
                refine ⟨66884316488098330450961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11414923347302115063630677 66884316488098330450961)
                ·
                  rfl

theorem cell21_879233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_879233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879233 prefixEnd_879233 := by exact prefixLift 879233
  have htrace : WordTrace (prefixWord ++ tailWord_879233) baseStart_879233 baseEnd_879233 := by
    simpa [prefixWord, tailWord_879233, baseEnd_879233] using wordTrace_append hprefix tailTrace_879233
  have hstable : (prefixWord ++ tailWord_879233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879233).length < 2 ^ (prefixWord ++ tailWord_879233).sum := by decide
  have hdescent : baseEnd_879233 < baseStart_879233 := by decide
  rcases family_descends (prefixWord ++ tailWord_879233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879247 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_879247 : Nat := 118140960795 + 879247 * 2 ^ 59
def prefixEnd_879247 : Nat := 4983230072969 + 3 ^ 40 * 879247 * 2
def baseEnd_879247 : Nat := 200656144455034078119521

theorem tailTrace_879247 : CollatzResearch.WordTrace tailWord_879247 prefixEnd_879247 200656144455034078119521 := by
  unfold tailWord_879247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068772645645757277587995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21379181763763838185058663 32068772645645757277587995)
  ·
    refine ⟨48103158968468635916381993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068772645645757277587995 48103158968468635916381993)
    ·
      refine ⟨36077369226351476937286495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48103158968468635916381993 36077369226351476937286495)
      ·
        refine ⟨54116053839527215405929743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36077369226351476937286495 54116053839527215405929743)
        ·
          refine ⟨81174080759290823108894615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54116053839527215405929743 81174080759290823108894615)
          ·
            refine ⟨121761121138936234663341923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81174080759290823108894615 121761121138936234663341923)
            ·
              refine ⟨182641681708404351995012885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121761121138936234663341923 182641681708404351995012885)
              ·
                refine ⟨8561328830081453999766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182641681708404351995012885 8561328830081453999766229)
                ·
                  refine ⟨200656144455034078119521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8561328830081453999766229 200656144455034078119521)
                  ·
                    rfl

theorem cell21_879247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_879247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879247 prefixEnd_879247 := by exact prefixLift 879247
  have htrace : WordTrace (prefixWord ++ tailWord_879247) baseStart_879247 baseEnd_879247 := by
    simpa [prefixWord, tailWord_879247, baseEnd_879247] using wordTrace_append hprefix tailTrace_879247
  have hstable : (prefixWord ++ tailWord_879247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879247).length < 2 ^ (prefixWord ++ tailWord_879247).sum := by decide
  have hdescent : baseEnd_879247 < baseStart_879247 := by decide
  rcases family_descends (prefixWord ++ tailWord_879247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879349 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 3]
def baseStart_879349 : Nat := 118140960795 + 879349 * 2 ^ 59
def prefixEnd_879349 : Nat := 4983230072969 + 3 ^ 40 * 879349 * 2
def baseEnd_879349 : Nat := 200679422244704567419313

theorem tailTrace_879349 : CollatzResearch.WordTrace tailWord_879349 prefixEnd_879349 200679422244704567419313 := by
  unfold tailWord_879349
  simp only [CollatzResearch.WordTrace]
  refine ⟨32072492891276228697801101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21381661927517485798534067 32072492891276228697801101)
  ·
    refine ⟨12027184834228585761675413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32072492891276228697801101 12027184834228585761675413)
    ·
      refine ⟨563774289104464957578535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12027184834228585761675413 563774289104464957578535)
      ·
        refine ⟨845661433656697436367803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563774289104464957578535 845661433656697436367803)
        ·
          refine ⟨1268492150485046154551705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845661433656697436367803 1268492150485046154551705)
          ·
            refine ⟨951369112863784615913779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268492150485046154551705 951369112863784615913779)
            ·
              refine ⟨1427053669295676923870669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951369112863784615913779 1427053669295676923870669)
              ·
                refine ⟨535145125985878846451501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427053669295676923870669 535145125985878846451501)
                ·
                  refine ⟨200679422244704567419313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535145125985878846451501 200679422244704567419313)
                  ·
                    rfl

theorem cell21_879349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_879349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879349 prefixEnd_879349 := by exact prefixLift 879349
  have htrace : WordTrace (prefixWord ++ tailWord_879349) baseStart_879349 baseEnd_879349 := by
    simpa [prefixWord, tailWord_879349, baseEnd_879349] using wordTrace_append hprefix tailTrace_879349
  have hstable : (prefixWord ++ tailWord_879349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879349).length < 2 ^ (prefixWord ++ tailWord_879349).sum := by decide
  have hdescent : baseEnd_879349 < baseStart_879349 := by decide
  rcases family_descends (prefixWord ++ tailWord_879349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879354 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_879354 : Nat := 118140960795 + 879354 * 2 ^ 59
def prefixEnd_879354 : Nat := 4983230072969 + 3 ^ 40 * 879354 * 2
def baseEnd_879354 : Nat := 200680563312825669835969

theorem tailTrace_879354 : CollatzResearch.WordTrace tailWord_879354 prefixEnd_879354 200680563312825669835969 := by
  unfold tailWord_879354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018168814064528637933279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21381783504172076367822077 8018168814064528637933279)
  ·
    refine ⟨12027253221096792956899919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8018168814064528637933279 12027253221096792956899919)
    ·
      refine ⟨18040879831645189435349879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12027253221096792956899919 18040879831645189435349879)
      ·
        refine ⟨27061319747467784153024819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18040879831645189435349879 27061319747467784153024819)
        ·
          refine ⟨40591979621201676229537229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27061319747467784153024819 40591979621201676229537229)
          ·
            refine ⟨15221992357950628586076461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40591979621201676229537229 15221992357950628586076461)
            ·
              refine ⟨5708247134231485719778673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15221992357950628586076461 5708247134231485719778673)
              ·
                refine ⟨4281185350673614289834005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708247134231485719778673 4281185350673614289834005)
                ·
                  refine ⟨200680563312825669835969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4281185350673614289834005 200680563312825669835969)
                  ·
                    rfl

theorem cell21_879354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_879354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879354 prefixEnd_879354 := by exact prefixLift 879354
  have htrace : WordTrace (prefixWord ++ tailWord_879354) baseStart_879354 baseEnd_879354 := by
    simpa [prefixWord, tailWord_879354, baseEnd_879354] using wordTrace_append hprefix tailTrace_879354
  have hstable : (prefixWord ++ tailWord_879354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879354).length < 2 ^ (prefixWord ++ tailWord_879354).sum := by decide
  have hdescent : baseEnd_879354 < baseStart_879354 := by decide
  rcases family_descends (prefixWord ++ tailWord_879354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879388 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_879388 : Nat := 118140960795 + 879388 * 2 ^ 59
def prefixEnd_879388 : Nat := 4983230072969 + 3 ^ 40 * 879388 * 2
def baseEnd_879388 : Nat := 200688322576049166269233

theorem tailTrace_879388 : CollatzResearch.WordTrace tailWord_879388 prefixEnd_879388 200688322576049166269233 := by
  unfold tailWord_879388
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036957669067469179235409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21382610225423292238980545 16036957669067469179235409)
  ·
    refine ⟨12027718251800601884426557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16036957669067469179235409 12027718251800601884426557)
    ·
      refine ⟨4510394344425225706659959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12027718251800601884426557 4510394344425225706659959)
      ·
        refine ⟨6765591516637838559989939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4510394344425225706659959 6765591516637838559989939)
        ·
          refine ⟨10148387274956757839984909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765591516637838559989939 10148387274956757839984909)
          ·
            refine ⟨3805645228108784189994341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10148387274956757839984909 3805645228108784189994341)
            ·
              refine ⟨713558480270397035623939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3805645228108784189994341 713558480270397035623939)
              ·
                refine ⟨1070337720405595553435909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713558480270397035623939 1070337720405595553435909)
                ·
                  refine ⟨200688322576049166269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070337720405595553435909 200688322576049166269233)
                  ·
                    rfl

theorem cell21_879388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_879388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879388 prefixEnd_879388 := by exact prefixLift 879388
  have htrace : WordTrace (prefixWord ++ tailWord_879388) baseStart_879388 baseEnd_879388 := by
    simpa [prefixWord, tailWord_879388, baseEnd_879388] using wordTrace_append hprefix tailTrace_879388
  have hstable : (prefixWord ++ tailWord_879388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879388).length < 2 ^ (prefixWord ++ tailWord_879388).sum := by decide
  have hdescent : baseEnd_879388 < baseStart_879388 := by decide
  rcases family_descends (prefixWord ++ tailWord_879388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879425 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 3]
def baseStart_879425 : Nat := 118140960795 + 879425 * 2 ^ 59
def prefixEnd_879425 : Nat := 4983230072969 + 3 ^ 40 * 879425 * 2
def baseEnd_879425 : Nat := 200696766480145324152491

theorem tailTrace_879425 : CollatzResearch.WordTrace tailWord_879425 prefixEnd_879425 200696766480145324152491 := by
  unfold tailWord_879425
  simp only [CollatzResearch.WordTrace]
  refine ⟨32075264839000893677567729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21383509892667262451711819 32075264839000893677567729)
  ·
    refine ⟨24056448629250670258175797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32075264839000893677567729 24056448629250670258175797)
    ·
      refine ⟨2255292058992250336703981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24056448629250670258175797 2255292058992250336703981)
      ·
        refine ⟨845734522122093876263993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2255292058992250336703981 845734522122093876263993)
        ·
          refine ⟨634300891591570407197995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845734522122093876263993 634300891591570407197995)
          ·
            refine ⟨951451337387355610796993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634300891591570407197995 951451337387355610796993)
            ·
              refine ⟨713588503040516708097745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951451337387355610796993 713588503040516708097745)
              ·
                refine ⟨535191377280387531073309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713588503040516708097745 535191377280387531073309)
                ·
                  refine ⟨200696766480145324152491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535191377280387531073309 200696766480145324152491)
                  ·
                    rfl

theorem cell21_879425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_879425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879425 prefixEnd_879425 := by exact prefixLift 879425
  have htrace : WordTrace (prefixWord ++ tailWord_879425) baseStart_879425 baseEnd_879425 := by
    simpa [prefixWord, tailWord_879425, baseEnd_879425] using wordTrace_append hprefix tailTrace_879425
  have hstable : (prefixWord ++ tailWord_879425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879425).length < 2 ^ (prefixWord ++ tailWord_879425).sum := by decide
  have hdescent : baseEnd_879425 < baseStart_879425 := by decide
  rcases family_descends (prefixWord ++ tailWord_879425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879433 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 3]
def baseStart_879433 : Nat := 118140960795 + 879433 * 2 ^ 59
def prefixEnd_879433 : Nat := 4983230072969 + 3 ^ 40 * 879433 * 2
def baseEnd_879433 : Nat := 200698592189139088019141

theorem tailTrace_879433 : CollatzResearch.WordTrace tailWord_879433 prefixEnd_879433 200698592189139088019141 := by
  unfold tailWord_879433
  simp only [CollatzResearch.WordTrace]
  refine ⟨32075556622971911043858953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21383704415314607362572635 32075556622971911043858953)
  ·
    refine ⟨24056667467228933282894215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32075556622971911043858953 24056667467228933282894215)
    ·
      refine ⟨36085001200843399924341323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24056667467228933282894215 36085001200843399924341323)
      ·
        refine ⟨54127501801265099886511985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36085001200843399924341323 54127501801265099886511985)
        ·
          refine ⟨40595626350948824914883989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54127501801265099886511985 40595626350948824914883989)
          ·
            refine ⟨1902919985200726167885187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40595626350948824914883989 1902919985200726167885187)
            ·
              refine ⟨2854379977801089251827781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902919985200726167885187 2854379977801089251827781)
              ·
                refine ⟨535196245837704234717709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2854379977801089251827781 535196245837704234717709)
                ·
                  refine ⟨200698592189139088019141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535196245837704234717709 200698592189139088019141)
                  ·
                    rfl

theorem cell21_879433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_879433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879433 prefixEnd_879433 := by exact prefixLift 879433
  have htrace : WordTrace (prefixWord ++ tailWord_879433) baseStart_879433 baseEnd_879433 := by
    simpa [prefixWord, tailWord_879433, baseEnd_879433] using wordTrace_append hprefix tailTrace_879433
  have hstable : (prefixWord ++ tailWord_879433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879433).length < 2 ^ (prefixWord ++ tailWord_879433).sum := by decide
  have hdescent : baseEnd_879433 < baseStart_879433 := by decide
  rcases family_descends (prefixWord ++ tailWord_879433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879447 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_879447 : Nat := 118140960795 + 879447 * 2 ^ 59
def prefixEnd_879447 : Nat := 4983230072969 + 3 ^ 40 * 879447 * 2
def baseEnd_879447 : Nat := 200701787179878174785779

theorem tailTrace_879447 : CollatzResearch.WordTrace tailWord_879447 prefixEnd_879447 200701787179878174785779 := by
  unfold tailWord_879447
  simp only [CollatzResearch.WordTrace]
  refine ⟨32076067244921191434868595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21384044829947460956579063 32076067244921191434868595)
  ·
    refine ⟨48114100867381787152302893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32076067244921191434868595 48114100867381787152302893)
    ·
      refine ⟨18042787825268170182113585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48114100867381787152302893 18042787825268170182113585)
      ·
        refine ⟨13532090868951127636585189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18042787825268170182113585 13532090868951127636585189)
        ·
          refine ⟨2537267037928336431859723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13532090868951127636585189 2537267037928336431859723)
          ·
            refine ⟨3805900556892504647789585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537267037928336431859723 3805900556892504647789585)
            ·
              refine ⟨2854425417669378485842189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805900556892504647789585 2854425417669378485842189)
              ·
                refine ⟨1070409531626016932190821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2854425417669378485842189 1070409531626016932190821)
                ·
                  refine ⟨200701787179878174785779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070409531626016932190821 200701787179878174785779)
                  ·
                    rfl

theorem cell21_879447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_879447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879447 prefixEnd_879447 := by exact prefixLift 879447
  have htrace : WordTrace (prefixWord ++ tailWord_879447) baseStart_879447 baseEnd_879447 := by
    simpa [prefixWord, tailWord_879447, baseEnd_879447] using wordTrace_append hprefix tailTrace_879447
  have hstable : (prefixWord ++ tailWord_879447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879447).length < 2 ^ (prefixWord ++ tailWord_879447).sum := by decide
  have hdescent : baseEnd_879447 < baseStart_879447 := by decide
  rcases family_descends (prefixWord ++ tailWord_879447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879478 : List Nat := [5, 1, 1, 3, 1, 2, 8]
def baseStart_879478 : Nat := 118140960795 + 879478 * 2 ^ 59
def prefixEnd_879478 : Nat := 4983230072969 + 3 ^ 40 * 879478 * 2
def baseEnd_879478 : Nat := 22300984644692112196561

theorem tailTrace_879478 : CollatzResearch.WordTrace tailWord_879478 prefixEnd_879478 22300984644692112196561 := by
  unfold tailWord_879478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004824869238055233077943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21384798605205922486164725 2004824869238055233077943)
  ·
    refine ⟨3007237303857082849616915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004824869238055233077943 3007237303857082849616915)
    ·
      refine ⟨4510855955785624274425373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007237303857082849616915 4510855955785624274425373)
      ·
        refine ⟨1691570983419609102909515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4510855955785624274425373 1691570983419609102909515)
        ·
          refine ⟨2537356475129413654364273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691570983419609102909515 2537356475129413654364273)
          ·
            refine ⟨1903017356347060240773205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537356475129413654364273 1903017356347060240773205)
            ·
              refine ⟨22300984644692112196561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1903017356347060240773205 22300984644692112196561)
              ·
                rfl

theorem cell21_879478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 8].length) (baseStart_879478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879478 prefixEnd_879478 := by exact prefixLift 879478
  have htrace : WordTrace (prefixWord ++ tailWord_879478) baseStart_879478 baseEnd_879478 := by
    simpa [prefixWord, tailWord_879478, baseEnd_879478] using wordTrace_append hprefix tailTrace_879478
  have hstable : (prefixWord ++ tailWord_879478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879478).length < 2 ^ (prefixWord ++ tailWord_879478).sum := by decide
  have hdescent : baseEnd_879478 < baseStart_879478 := by decide
  rcases family_descends (prefixWord ++ tailWord_879478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879540 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_879540 : Nat := 118140960795 + 879540 * 2 ^ 59
def prefixEnd_879540 : Nat := 4983230072969 + 3 ^ 40 * 879540 * 2
def baseEnd_879540 : Nat := 200723011046930679735589

theorem tailTrace_879540 : CollatzResearch.WordTrace tailWord_879540 prefixEnd_879540 200723011046930679735589 := by
  unfold tailWord_879540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039729616792134159002037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21386306155722845545336049 16039729616792134159002037)
  ·
    refine ⟨1503724651574262577406441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16039729616792134159002037 1503724651574262577406441)
    ·
      refine ⟨1127793488680696933054831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1503724651574262577406441 1127793488680696933054831)
      ·
        refine ⟨1691690233021045399582247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127793488680696933054831 1691690233021045399582247)
        ·
          refine ⟨2537535349531568099373371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691690233021045399582247 2537535349531568099373371)
          ·
            refine ⟨3806303024297352149060057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537535349531568099373371 3806303024297352149060057)
            ·
              refine ⟨2854727268223014111795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806303024297352149060057 2854727268223014111795043)
              ·
                refine ⟨4282090902334521167692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854727268223014111795043 4282090902334521167692565)
                ·
                  refine ⟨200723011046930679735589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4282090902334521167692565 200723011046930679735589)
                  ·
                    rfl

theorem cell21_879540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_879540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879540 prefixEnd_879540 := by exact prefixLift 879540
  have htrace : WordTrace (prefixWord ++ tailWord_879540) baseStart_879540 baseEnd_879540 := by
    simpa [prefixWord, tailWord_879540, baseEnd_879540] using wordTrace_append hprefix tailTrace_879540
  have hstable : (prefixWord ++ tailWord_879540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879540).length < 2 ^ (prefixWord ++ tailWord_879540).sum := by decide
  have hdescent : baseEnd_879540 < baseStart_879540 := by decide
  rcases family_descends (prefixWord ++ tailWord_879540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879551 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_879551 : Nat := 118140960795 + 879551 * 2 ^ 59
def prefixEnd_879551 : Nat := 4983230072969 + 3 ^ 40 * 879551 * 2
def baseEnd_879551 : Nat := 200725521396797105052233

theorem tailTrace_879551 : CollatzResearch.WordTrace tailWord_879551 prefixEnd_879551 200725521396797105052233 := by
  unfold tailWord_879551
  simp only [CollatzResearch.WordTrace]
  refine ⟨32079860436544417196654507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21386573624362944797769671 32079860436544417196654507)
  ·
    refine ⟨48119790654816625794981761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32079860436544417196654507 48119790654816625794981761)
    ·
      refine ⟨36089842991112469346236321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48119790654816625794981761 36089842991112469346236321)
      ·
        refine ⟨27067382243334352009677241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36089842991112469346236321 27067382243334352009677241)
        ·
          refine ⟨20300536682500764007257931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27067382243334352009677241 20300536682500764007257931)
          ·
            refine ⟨30450805023751146010886897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20300536682500764007257931 30450805023751146010886897)
            ·
              refine ⟨22838103767813359508165173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30450805023751146010886897 22838103767813359508165173)
              ·
                refine ⟨2141072228232502453890485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22838103767813359508165173 2141072228232502453890485)
                ·
                  refine ⟨200725521396797105052233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141072228232502453890485 200725521396797105052233)
                  ·
                    rfl

theorem cell21_879551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_879551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879551 prefixEnd_879551 := by exact prefixLift 879551
  have htrace : WordTrace (prefixWord ++ tailWord_879551) baseStart_879551 baseEnd_879551 := by
    simpa [prefixWord, tailWord_879551, baseEnd_879551] using wordTrace_append hprefix tailTrace_879551
  have hstable : (prefixWord ++ tailWord_879551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879551).length < 2 ^ (prefixWord ++ tailWord_879551).sum := by decide
  have hdescent : baseEnd_879551 < baseStart_879551 := by decide
  rcases family_descends (prefixWord ++ tailWord_879551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879599 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_879599 : Nat := 118140960795 + 879599 * 2 ^ 59
def prefixEnd_879599 : Nat := 4983230072969 + 3 ^ 40 * 879599 * 2
def baseEnd_879599 : Nat := 200736475650759688252135

theorem tailTrace_879599 : CollatzResearch.WordTrace tailWord_879599 prefixEnd_879599 200736475650759688252135 := by
  unfold tailWord_879599
  simp only [CollatzResearch.WordTrace]
  refine ⟨32081611140370521394401851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21387740760247014262934567 32081611140370521394401851)
  ·
    refine ⟨48122416710555782091602777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32081611140370521394401851 48122416710555782091602777)
    ·
      refine ⟨36091812532916836568702083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48122416710555782091602777 36091812532916836568702083)
      ·
        refine ⟨54137718799375254853053125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091812532916836568702083 54137718799375254853053125)
        ·
          refine ⟨10150822274882860284947461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54137718799375254853053125 10150822274882860284947461)
          ·
            refine ⟨1903279176540536303427649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10150822274882860284947461 1903279176540536303427649)
            ·
              refine ⟨1427459382405402227570737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903279176540536303427649 1427459382405402227570737)
              ·
                refine ⟨1070594536804051670678053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427459382405402227570737 1070594536804051670678053)
                ·
                  refine ⟨200736475650759688252135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070594536804051670678053 200736475650759688252135)
                  ·
                    rfl

theorem cell21_879599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_879599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879599 prefixEnd_879599 := by exact prefixLift 879599
  have htrace : WordTrace (prefixWord ++ tailWord_879599) baseStart_879599 baseEnd_879599 := by
    simpa [prefixWord, tailWord_879599, baseEnd_879599] using wordTrace_append hprefix tailTrace_879599
  have hstable : (prefixWord ++ tailWord_879599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879599).length < 2 ^ (prefixWord ++ tailWord_879599).sum := by decide
  have hdescent : baseEnd_879599 < baseStart_879599 := by decide
  rcases family_descends (prefixWord ++ tailWord_879599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879627 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_879627 : Nat := 118140960795 + 879627 * 2 ^ 59
def prefixEnd_879627 : Nat := 4983230072969 + 3 ^ 40 * 879627 * 2
def baseEnd_879627 : Nat := 200742865632237861785411

theorem tailTrace_879627 : CollatzResearch.WordTrace tailWord_879627 prefixEnd_879627 200742865632237861785411 := by
  unfold tailWord_879627
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082632384269082176421135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21388421589512721450947423 32082632384269082176421135)
  ·
    refine ⟨48123948576403623264631703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32082632384269082176421135 48123948576403623264631703)
    ·
      refine ⟨72185922864605434896947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48123948576403623264631703 72185922864605434896947555)
      ·
        refine ⟨108278884296908152345421333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72185922864605434896947555 108278884296908152345421333)
        ·
          refine ⟨5075572701417569641191625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108278884296908152345421333 5075572701417569641191625)
          ·
            refine ⟨3806679526063177230893719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5075572701417569641191625 3806679526063177230893719)
            ·
              refine ⟨5710019289094765846340579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806679526063177230893719 5710019289094765846340579)
              ·
                refine ⟨8565028933642148769510869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710019289094765846340579 8565028933642148769510869)
                ·
                  refine ⟨200742865632237861785411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8565028933642148769510869 200742865632237861785411)
                  ·
                    rfl

theorem cell21_879627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_879627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879627 prefixEnd_879627 := by exact prefixLift 879627
  have htrace : WordTrace (prefixWord ++ tailWord_879627) baseStart_879627 baseEnd_879627 := by
    simpa [prefixWord, tailWord_879627, baseEnd_879627] using wordTrace_append hprefix tailTrace_879627
  have hstable : (prefixWord ++ tailWord_879627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879627).length < 2 ^ (prefixWord ++ tailWord_879627).sum := by decide
  have hdescent : baseEnd_879627 < baseStart_879627 := by decide
  rcases family_descends (prefixWord ++ tailWord_879627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879630 : List Nat := [4, 1, 1, 2, 2, 3, 3, 5]
def baseStart_879630 : Nat := 118140960795 + 879630 * 2 ^ 59
def prefixEnd_879630 : Nat := 4983230072969 + 3 ^ 40 * 879630 * 2
def baseEnd_879630 : Nat := 66914516757703507745135

theorem tailTrace_879630 : CollatzResearch.WordTrace tailWord_879630 prefixEnd_879630 66914516757703507745135 := by
  unfold tailWord_879630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010342725407276711097543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21388494535505475792520229 4010342725407276711097543)
  ·
    refine ⟨6015514088110915066646315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010342725407276711097543 6015514088110915066646315)
    ·
      refine ⟨9023271132166372599969473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6015514088110915066646315 9023271132166372599969473)
      ·
        refine ⟨6767453349124779449977105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9023271132166372599969473 6767453349124779449977105)
        ·
          refine ⟨5075590011843584587482829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6767453349124779449977105 5075590011843584587482829)
          ·
            refine ⟨1903346254441344220306061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5075590011843584587482829 1903346254441344220306061)
            ·
              refine ⟨713754845415504082614773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903346254441344220306061 713754845415504082614773)
              ·
                refine ⟨66914516757703507745135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 713754845415504082614773 66914516757703507745135)
                ·
                  rfl

theorem cell21_879630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_879630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879630 prefixEnd_879630 := by exact prefixLift 879630
  have htrace : WordTrace (prefixWord ++ tailWord_879630) baseStart_879630 baseEnd_879630 := by
    simpa [prefixWord, tailWord_879630, baseEnd_879630] using wordTrace_append hprefix tailTrace_879630
  have hstable : (prefixWord ++ tailWord_879630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879630).length < 2 ^ (prefixWord ++ tailWord_879630).sum := by decide
  have hdescent : baseEnd_879630 < baseStart_879630 := by decide
  rcases family_descends (prefixWord ++ tailWord_879630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879830 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_879830 : Nat := 118140960795 + 879830 * 2 ^ 59
def prefixEnd_879830 : Nat := 4983230072969 + 3 ^ 40 * 879830 * 2
def baseEnd_879830 : Nat := 200789192997954619901663

theorem tailTrace_879830 : CollatzResearch.WordTrace tailWord_879830 prefixEnd_879830 200789192997954619901663 := by
  unfold tailWord_879830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005627275158352990378809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21393357601689098564040629 2005627275158352990378809)
  ·
    refine ⟨1504220456368764742784107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2005627275158352990378809 1504220456368764742784107)
    ·
      refine ⟨2256330684553147114176161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504220456368764742784107 2256330684553147114176161)
      ·
        refine ⟨1692248013414860335632121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256330684553147114176161 1692248013414860335632121)
        ·
          refine ⟨1269186010061145251724091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692248013414860335632121 1269186010061145251724091)
          ·
            refine ⟨1903779015091717877586137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269186010061145251724091 1903779015091717877586137)
            ·
              refine ⟨1427834261318788408189603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903779015091717877586137 1427834261318788408189603)
              ·
                refine ⟨2141751391978182612284405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427834261318788408189603 2141751391978182612284405)
                ·
                  refine ⟨200789192997954619901663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141751391978182612284405 200789192997954619901663)
                  ·
                    rfl

theorem cell21_879830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_879830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879830 prefixEnd_879830 := by exact prefixLift 879830
  have htrace : WordTrace (prefixWord ++ tailWord_879830) baseStart_879830 baseEnd_879830 := by
    simpa [prefixWord, tailWord_879830, baseEnd_879830] using wordTrace_append hprefix tailTrace_879830
  have hstable : (prefixWord ++ tailWord_879830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879830).length < 2 ^ (prefixWord ++ tailWord_879830).sum := by decide
  have hdescent : baseEnd_879830 < baseStart_879830 := by decide
  rcases family_descends (prefixWord ++ tailWord_879830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879886 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_879886 : Nat := 118140960795 + 879886 * 2 ^ 59
def prefixEnd_879886 : Nat := 4983230072969 + 3 ^ 40 * 879886 * 2
def baseEnd_879886 : Nat := 200801972960910966968215

theorem tailTrace_879886 : CollatzResearch.WordTrace tailWord_879886 prefixEnd_879886 200801972960910966968215 := by
  unfold tailWord_879886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011509861291346176262439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21394719260220512940066341 4011509861291346176262439)
  ·
    refine ⟨6017264791937019264393659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4011509861291346176262439 6017264791937019264393659)
    ·
      refine ⟨9025897187905528896590489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6017264791937019264393659 9025897187905528896590489)
      ·
        refine ⟨6769422890929146672442867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9025897187905528896590489 6769422890929146672442867)
        ·
          refine ⟨10154134336393720008664301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769422890929146672442867 10154134336393720008664301)
          ·
            refine ⟨3807800376147645003249113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10154134336393720008664301 3807800376147645003249113)
            ·
              refine ⟨2855850282110733752436835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807800376147645003249113 2855850282110733752436835)
              ·
                refine ⟨4283775423166100628655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855850282110733752436835 4283775423166100628655253)
                ·
                  refine ⟨200801972960910966968215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4283775423166100628655253 200801972960910966968215)
                  ·
                    rfl

theorem cell21_879886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_879886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879886 prefixEnd_879886 := by exact prefixLift 879886
  have htrace : WordTrace (prefixWord ++ tailWord_879886) baseStart_879886 baseEnd_879886 := by
    simpa [prefixWord, tailWord_879886, baseEnd_879886] using wordTrace_append hprefix tailTrace_879886
  have hstable : (prefixWord ++ tailWord_879886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879886).length < 2 ^ (prefixWord ++ tailWord_879886).sum := by decide
  have hdescent : baseEnd_879886 < baseStart_879886 := by decide
  rcases family_descends (prefixWord ++ tailWord_879886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879889 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 3]
def baseStart_879889 : Nat := 118140960795 + 879889 * 2 ^ 59
def prefixEnd_879889 : Nat := 4983230072969 + 3 ^ 40 * 879889 * 2
def baseEnd_879889 : Nat := 200802657601783628418209

theorem tailTrace_879889 : CollatzResearch.WordTrace tailWord_879889 prefixEnd_879889 200802657601783628418209 := by
  unfold tailWord_879889
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092188309319900922458721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21394792206213267281639147 32092188309319900922458721)
  ·
    refine ⟨24069141231989925691844041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32092188309319900922458721 24069141231989925691844041)
    ·
      refine ⟨18051855923992444268883031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24069141231989925691844041 18051855923992444268883031)
      ·
        refine ⟨27077783885988666403324547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18051855923992444268883031 27077783885988666403324547)
        ·
          refine ⟨40616675828982999604986821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27077783885988666403324547 40616675828982999604986821)
          ·
            refine ⟨7615626717934312425935029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40616675828982999604986821 7615626717934312425935029)
            ·
              refine ⟨713965004806341789931409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7615626717934312425935029 713965004806341789931409)
              ·
                refine ⟨535473753604756342448557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713965004806341789931409 535473753604756342448557)
                ·
                  refine ⟨200802657601783628418209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535473753604756342448557 200802657601783628418209)
                  ·
                    rfl

theorem cell21_879889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_879889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879889 prefixEnd_879889 := by exact prefixLift 879889
  have htrace : WordTrace (prefixWord ++ tailWord_879889) baseStart_879889 baseEnd_879889 := by
    simpa [prefixWord, tailWord_879889, baseEnd_879889] using wordTrace_append hprefix tailTrace_879889
  have hstable : (prefixWord ++ tailWord_879889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879889).length < 2 ^ (prefixWord ++ tailWord_879889).sum := by decide
  have hdescent : baseEnd_879889 < baseStart_879889 := by decide
  rcases family_descends (prefixWord ++ tailWord_879889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879900 : List Nat := [2, 2, 3, 1, 1, 1, 3, 8]
def baseStart_879900 : Nat := 118140960795 + 879900 * 2 ^ 59
def prefixEnd_879900 : Nat := 4983230072969 + 3 ^ 40 * 879900 * 2
def baseEnd_879900 : Nat := 66935055983883351244951

theorem tailTrace_879900 : CollatzResearch.WordTrace tailWord_879900 prefixEnd_879900 66935055983883351244951 := by
  unfold tailWord_879900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046294756140024900554577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21395059674853366534072769 16046294756140024900554577)
  ·
    refine ⟨12034721067105018675415933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16046294756140024900554577 12034721067105018675415933)
    ·
      refine ⟨4513020400164382003280975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12034721067105018675415933 4513020400164382003280975)
      ·
        refine ⟨6769530600246573004921463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513020400164382003280975 6769530600246573004921463)
        ·
          refine ⟨10154295900369859507382195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769530600246573004921463 10154295900369859507382195)
          ·
            refine ⟨15231443850554789261073293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154295900369859507382195 15231443850554789261073293)
            ·
              refine ⟨5711791443958045972902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15231443850554789261073293 5711791443958045972902485)
              ·
                refine ⟨66935055983883351244951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5711791443958045972902485 66935055983883351244951)
                ·
                  rfl

theorem cell21_879900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_879900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879900 prefixEnd_879900 := by exact prefixLift 879900
  have htrace : WordTrace (prefixWord ++ tailWord_879900) baseStart_879900 baseEnd_879900 := by
    simpa [prefixWord, tailWord_879900, baseEnd_879900] using wordTrace_append hprefix tailTrace_879900
  have hstable : (prefixWord ++ tailWord_879900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879900).length < 2 ^ (prefixWord ++ tailWord_879900).sum := by decide
  have hdescent : baseEnd_879900 < baseStart_879900 := by decide
  rcases family_descends (prefixWord ++ tailWord_879900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879903 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_879903 : Nat := 118140960795 + 879903 * 2 ^ 59
def prefixEnd_879903 : Nat := 4983230072969 + 3 ^ 40 * 879903 * 2
def baseEnd_879903 : Nat := 200805852592522715184847

theorem tailTrace_879903 : CollatzResearch.WordTrace tailWord_879903 prefixEnd_879903 200805852592522715184847 := by
  unfold tailWord_879903
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092698931269181313468363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395132620846120875645575 32092698931269181313468363)
  ·
    refine ⟨48139048396903771970202545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32092698931269181313468363 48139048396903771970202545)
    ·
      refine ⟨36104286297677828977651909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48139048396903771970202545 36104286297677828977651909)
      ·
        refine ⟨6769553680814592933309733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36104286297677828977651909 6769553680814592933309733)
        ·
          refine ⟨1269291315152736174995575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6769553680814592933309733 1269291315152736174995575)
          ·
            refine ⟨1903936972729104262493363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269291315152736174995575 1903936972729104262493363)
            ·
              refine ⟨2855905459093656393740045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903936972729104262493363 2855905459093656393740045)
              ·
                refine ⟨1070964547160121147652517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2855905459093656393740045 1070964547160121147652517)
                ·
                  refine ⟨200805852592522715184847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070964547160121147652517 200805852592522715184847)
                  ·
                    rfl

theorem cell21_879903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_879903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879903 prefixEnd_879903 := by exact prefixLift 879903
  have htrace : WordTrace (prefixWord ++ tailWord_879903) baseStart_879903 baseEnd_879903 := by
    simpa [prefixWord, tailWord_879903, baseEnd_879903] using wordTrace_append hprefix tailTrace_879903
  have hstable : (prefixWord ++ tailWord_879903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879903).length < 2 ^ (prefixWord ++ tailWord_879903).sum := by decide
  have hdescent : baseEnd_879903 < baseStart_879903 := by decide
  rcases family_descends (prefixWord ++ tailWord_879903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879945 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_879945 : Nat := 118140960795 + 879945 * 2 ^ 59
def prefixEnd_879945 : Nat := 4983230072969 + 3 ^ 40 * 879945 * 2
def baseEnd_879945 : Nat := 200815437564739975484761

theorem tailTrace_879945 : CollatzResearch.WordTrace tailWord_879945 prefixEnd_879945 200815437564739975484761 := by
  unfold tailWord_879945
  simp only [CollatzResearch.WordTrace]
  refine ⟨32094230797117022486497289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21396153864744681657664859 32094230797117022486497289)
  ·
    refine ⟨24070673097837766864872967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32094230797117022486497289 24070673097837766864872967)
    ·
      refine ⟨36106009646756650297309451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24070673097837766864872967 36106009646756650297309451)
      ·
        refine ⟨54159014470134975445964177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36106009646756650297309451 54159014470134975445964177)
        ·
          refine ⟨40619260852601231584473133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54159014470134975445964177 40619260852601231584473133)
          ·
            refine ⟨15232222819725461844177425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40619260852601231584473133 15232222819725461844177425)
            ·
              refine ⟨11424167114794096383133069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15232222819725461844177425 11424167114794096383133069)
              ·
                refine ⟨4284062668047786143674901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424167114794096383133069 4284062668047786143674901)
                ·
                  refine ⟨200815437564739975484761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4284062668047786143674901 200815437564739975484761)
                  ·
                    rfl

theorem cell21_879945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_879945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879945 prefixEnd_879945 := by exact prefixLift 879945
  have htrace : WordTrace (prefixWord ++ tailWord_879945) baseStart_879945 baseEnd_879945 := by
    simpa [prefixWord, tailWord_879945, baseEnd_879945] using wordTrace_append hprefix tailTrace_879945
  have hstable : (prefixWord ++ tailWord_879945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879945).length < 2 ^ (prefixWord ++ tailWord_879945).sum := by decide
  have hdescent : baseEnd_879945 < baseStart_879945 := by decide
  rcases family_descends (prefixWord ++ tailWord_879945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879962 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_879962 : Nat := 118140960795 + 879962 * 2 ^ 59
def prefixEnd_879962 : Nat := 4983230072969 + 3 ^ 40 * 879962 * 2
def baseEnd_879962 : Nat := 200819317196351723701393

theorem tailTrace_879962 : CollatzResearch.WordTrace tailWord_879962 prefixEnd_879962 200819317196351723701393 := by
  unfold tailWord_879962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023712709513858597466535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21396567225370289593244093 8023712709513858597466535)
  ·
    refine ⟨12035569064270787896199803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8023712709513858597466535 12035569064270787896199803)
    ·
      refine ⟨18053353596406181844299705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12035569064270787896199803 18053353596406181844299705)
      ·
        refine ⟨13540015197304636383224779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18053353596406181844299705 13540015197304636383224779)
        ·
          refine ⟨20310022795956954574837169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540015197304636383224779 20310022795956954574837169)
          ·
            refine ⟨15232517096967715931127877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20310022795956954574837169 15232517096967715931127877)
            ·
              refine ⟨2856096955681446737086477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15232517096967715931127877 2856096955681446737086477)
              ·
                refine ⟨1071036358380542526407429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2856096955681446737086477 1071036358380542526407429)
                ·
                  refine ⟨200819317196351723701393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071036358380542526407429 200819317196351723701393)
                  ·
                    rfl

theorem cell21_879962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_879962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_879962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_879962 prefixEnd_879962 := by exact prefixLift 879962
  have htrace : WordTrace (prefixWord ++ tailWord_879962) baseStart_879962 baseEnd_879962 := by
    simpa [prefixWord, tailWord_879962, baseEnd_879962] using wordTrace_append hprefix tailTrace_879962
  have hstable : (prefixWord ++ tailWord_879962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879962).length < 2 ^ (prefixWord ++ tailWord_879962).sum := by decide
  have hdescent : baseEnd_879962 < baseStart_879962 := by decide
  rcases family_descends (prefixWord ++ tailWord_879962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880007 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_880007 : Nat := 118140960795 + 880007 * 2 ^ 59
def prefixEnd_880007 : Nat := 4983230072969 + 3 ^ 40 * 880007 * 2
def baseEnd_880007 : Nat := 200829586809441645451301

theorem tailTrace_880007 : CollatzResearch.WordTrace tailWord_880007 prefixEnd_880007 200829586809441645451301 := by
  unfold tailWord_880007
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096492122892407075254275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21397661415261604716836183 32096492122892407075254275)
  ·
    refine ⟨48144738184338610612881413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32096492122892407075254275 48144738184338610612881413)
    ·
      refine ⟨9027138409563489489915265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48144738184338610612881413 9027138409563489489915265)
      ·
        refine ⟨6770353807172617117436449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9027138409563489489915265 6770353807172617117436449)
        ·
          refine ⟨5077765355379462838077337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770353807172617117436449 5077765355379462838077337)
          ·
            refine ⟨3808324016534597128558003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077765355379462838077337 3808324016534597128558003)
            ·
              refine ⟨5712486024801895692837005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808324016534597128558003 5712486024801895692837005)
              ·
                refine ⟨2142182259300710884813877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712486024801895692837005 2142182259300710884813877)
                ·
                  refine ⟨200829586809441645451301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142182259300710884813877 200829586809441645451301)
                  ·
                    rfl

theorem cell21_880007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_880007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880007 prefixEnd_880007 := by exact prefixLift 880007
  have htrace : WordTrace (prefixWord ++ tailWord_880007) baseStart_880007 baseEnd_880007 := by
    simpa [prefixWord, tailWord_880007, baseEnd_880007] using wordTrace_append hprefix tailTrace_880007
  have hstable : (prefixWord ++ tailWord_880007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880007).length < 2 ^ (prefixWord ++ tailWord_880007).sum := by decide
  have hdescent : baseEnd_880007 < baseStart_880007 := by decide
  rcases family_descends (prefixWord ++ tailWord_880007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880204 : List Nat := [2, 2, 1, 3, 1, 4, 1, 7]
def baseStart_880204 : Nat := 118140960795 + 880204 * 2 ^ 59
def prefixEnd_880204 : Nat := 4983230072969 + 3 ^ 40 * 880204 * 2
def baseEnd_880204 : Nat := 66958181631137693555855

theorem tailTrace_880204 : CollatzResearch.WordTrace tailWord_880204 prefixEnd_880204 66958181631137693555855 := by
  unfold tailWord_880204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16051838651589354860087833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21402451535452473146783777 16051838651589354860087833)
  ·
    refine ⟨12038878988692016145065875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16051838651589354860087833 12038878988692016145065875)
    ·
      refine ⟨18058318483038024217598813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038878988692016145065875 18058318483038024217598813)
      ·
        refine ⟨6771869431139259081599555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18058318483038024217598813 6771869431139259081599555)
        ·
          refine ⟨10157804146708888622399333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771869431139259081599555 10157804146708888622399333)
          ·
            refine ⟨1904588277507916616699875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10157804146708888622399333 1904588277507916616699875)
            ·
              refine ⟨2856882416261874925049813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904588277507916616699875 2856882416261874925049813)
              ·
                refine ⟨66958181631137693555855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2856882416261874925049813 66958181631137693555855)
                ·
                  rfl

theorem cell21_880204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_880204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880204 prefixEnd_880204 := by exact prefixLift 880204
  have htrace : WordTrace (prefixWord ++ tailWord_880204) baseStart_880204 baseEnd_880204 := by
    simpa [prefixWord, tailWord_880204, baseEnd_880204] using wordTrace_append hprefix tailTrace_880204
  have hstable : (prefixWord ++ tailWord_880204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880204).length < 2 ^ (prefixWord ++ tailWord_880204).sum := by decide
  have hdescent : baseEnd_880204 < baseStart_880204 := by decide
  rcases family_descends (prefixWord ++ tailWord_880204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880218 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_880218 : Nat := 118140960795 + 880218 * 2 ^ 59
def prefixEnd_880218 : Nat := 4983230072969 + 3 ^ 40 * 880218 * 2
def baseEnd_880218 : Nat := 200877739884152167434203

theorem tailTrace_880218 : CollatzResearch.WordTrace tailWord_880218 prefixEnd_880218 200877739884152167434203 := by
  unfold tailWord_880218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026046981281997527796327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21402791950085326740790205 8026046981281997527796327)
  ·
    refine ⟨12039070471922996291694491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8026046981281997527796327 12039070471922996291694491)
    ·
      refine ⟨18058605707884494437541737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039070471922996291694491 18058605707884494437541737)
      ·
        refine ⟨13543954280913370828156303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18058605707884494437541737 13543954280913370828156303)
        ·
          refine ⟨20315931421370056242234455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543954280913370828156303 20315931421370056242234455)
          ·
            refine ⟨30473897132055084363351683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20315931421370056242234455 30473897132055084363351683)
            ·
              refine ⟨45710845698082626545027525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30473897132055084363351683 45710845698082626545027525)
              ·
                refine ⟨8570783568390492477192661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45710845698082626545027525 8570783568390492477192661)
                ·
                  refine ⟨200877739884152167434203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8570783568390492477192661 200877739884152167434203)
                  ·
                    rfl

theorem cell21_880218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_880218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880218 prefixEnd_880218 := by exact prefixLift 880218
  have htrace : WordTrace (prefixWord ++ tailWord_880218) baseStart_880218 baseEnd_880218 := by
    simpa [prefixWord, tailWord_880218, baseEnd_880218] using wordTrace_append hprefix tailTrace_880218
  have hstable : (prefixWord ++ tailWord_880218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880218).length < 2 ^ (prefixWord ++ tailWord_880218).sum := by decide
  have hdescent : baseEnd_880218 < baseStart_880218 := by decide
  rcases family_descends (prefixWord ++ tailWord_880218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880286 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_880286 : Nat := 118140960795 + 880286 * 2 ^ 59
def prefixEnd_880286 : Nat := 4983230072969 + 3 ^ 40 * 880286 * 2
def baseEnd_880286 : Nat := 200893258410599160300731

theorem tailTrace_880286 : CollatzResearch.WordTrace tailWord_880286 prefixEnd_880286 200893258410599160300731 := by
  unfold tailWord_880286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013333511110204715582589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21404445392587758483107141 4013333511110204715582589)
  ·
    refine ⟨1505000066666326768343471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4013333511110204715582589 1505000066666326768343471)
    ·
      refine ⟨2257500099999490152515207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505000066666326768343471 2257500099999490152515207)
      ·
        refine ⟨3386250149999235228772811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257500099999490152515207 3386250149999235228772811)
        ·
          refine ⟨5079375224998852843159217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386250149999235228772811 5079375224998852843159217)
          ·
            refine ⟨3809531418749139632369413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5079375224998852843159217 3809531418749139632369413)
            ·
              refine ⟨714287141015463681069265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3809531418749139632369413 714287141015463681069265)
              ·
                refine ⟨535715355761597760801949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714287141015463681069265 535715355761597760801949)
                ·
                  refine ⟨200893258410599160300731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535715355761597760801949 200893258410599160300731)
                  ·
                    rfl

theorem cell21_880286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_880286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880286 prefixEnd_880286 := by exact prefixLift 880286
  have htrace : WordTrace (prefixWord ++ tailWord_880286) baseStart_880286 baseEnd_880286 := by
    simpa [prefixWord, tailWord_880286, baseEnd_880286] using wordTrace_append hprefix tailTrace_880286
  have hstable : (prefixWord ++ tailWord_880286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880286).length < 2 ^ (prefixWord ++ tailWord_880286).sum := by decide
  have hdescent : baseEnd_880286 < baseStart_880286 := by decide
  rcases family_descends (prefixWord ++ tailWord_880286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880311 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_880311 : Nat := 118140960795 + 880311 * 2 ^ 59
def prefixEnd_880311 : Nat := 4983230072969 + 3 ^ 40 * 880311 * 2
def baseEnd_880311 : Nat := 200898963751204672384013

theorem tailTrace_880311 : CollatzResearch.WordTrace tailWord_880311 prefixEnd_880311 200898963751204672384013 := by
  unfold tailWord_880311
  simp only [CollatzResearch.WordTrace]
  refine ⟨32107579913791066994320787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21405053275860711329547191 32107579913791066994320787)
  ·
    refine ⟨48161369870686600491481181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32107579913791066994320787 48161369870686600491481181)
    ·
      refine ⟨18060513701507475184305443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48161369870686600491481181 18060513701507475184305443)
      ·
        refine ⟨27090770552261212776458165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18060513701507475184305443 27090770552261212776458165)
        ·
          refine ⟨2539759739274488697792953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27090770552261212776458165 2539759739274488697792953)
          ·
            refine ⟨1904819804455866523344715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2539759739274488697792953 1904819804455866523344715)
            ·
              refine ⟨2857229706683799785017073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904819804455866523344715 2857229706683799785017073)
              ·
                refine ⟨2142922280012849838762805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857229706683799785017073 2142922280012849838762805)
                ·
                  refine ⟨200898963751204672384013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142922280012849838762805 200898963751204672384013)
                  ·
                    rfl

theorem cell21_880311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_880311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880311 prefixEnd_880311 := by exact prefixLift 880311
  have htrace : WordTrace (prefixWord ++ tailWord_880311) baseStart_880311 baseEnd_880311 := by
    simpa [prefixWord, tailWord_880311, baseEnd_880311] using wordTrace_append hprefix tailTrace_880311
  have hstable : (prefixWord ++ tailWord_880311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880311).length < 2 ^ (prefixWord ++ tailWord_880311).sum := by decide
  have hdescent : baseEnd_880311 < baseStart_880311 := by decide
  rcases family_descends (prefixWord ++ tailWord_880311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880328 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_880328 : Nat := 118140960795 + 880328 * 2 ^ 59
def prefixEnd_880328 : Nat := 4983230072969 + 3 ^ 40 * 880328 * 2
def baseEnd_880328 : Nat := 200902843382816420600645

theorem tailTrace_880328 : CollatzResearch.WordTrace tailWord_880328 prefixEnd_880328 200902843382816420600645 := by
  unfold tailWord_880328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054099977364739448844819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21405466636486319265126425 16054099977364739448844819)
  ·
    refine ⟨24081149966047109173267229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054099977364739448844819 24081149966047109173267229)
    ·
      refine ⟨9030431237267665939975211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24081149966047109173267229 9030431237267665939975211)
      ·
        refine ⟨13545646855901498909962817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030431237267665939975211 13545646855901498909962817)
        ·
          refine ⟨10159235141926124182472113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13545646855901498909962817 10159235141926124182472113)
          ·
            refine ⟨7619426356444593136854085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10159235141926124182472113 7619426356444593136854085)
            ·
              refine ⟨1428642441833361213160141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7619426356444593136854085 1428642441833361213160141)
              ·
                refine ⟨535740915687510454935053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428642441833361213160141 535740915687510454935053)
                ·
                  refine ⟨200902843382816420600645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535740915687510454935053 200902843382816420600645)
                  ·
                    rfl

theorem cell21_880328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_880328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880328 prefixEnd_880328 := by exact prefixLift 880328
  have htrace : WordTrace (prefixWord ++ tailWord_880328) baseStart_880328 baseEnd_880328 := by
    simpa [prefixWord, tailWord_880328, baseEnd_880328] using wordTrace_append hprefix tailTrace_880328
  have hstable : (prefixWord ++ tailWord_880328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880328).length < 2 ^ (prefixWord ++ tailWord_880328).sum := by decide
  have hdescent : baseEnd_880328 < baseStart_880328 := by decide
  rcases family_descends (prefixWord ++ tailWord_880328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880401 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_880401 : Nat := 118140960795 + 880401 * 2 ^ 59
def prefixEnd_880401 : Nat := 4983230072969 + 3 ^ 40 * 880401 * 2
def baseEnd_880401 : Nat := 200919502977384515883829

theorem tailTrace_880401 : CollatzResearch.WordTrace tailWord_880401 prefixEnd_880401 200919502977384515883829 := by
  unfold tailWord_880401
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110862483465012365097057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21407241655643341576731371 32110862483465012365097057)
  ·
    refine ⟨24083146862598759273822793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32110862483465012365097057 24083146862598759273822793)
    ·
      refine ⟨18062360146949069455367095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24083146862598759273822793 18062360146949069455367095)
      ·
        refine ⟨27093540220423604183050643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18062360146949069455367095 27093540220423604183050643)
        ·
          refine ⟨40640310330635406274575965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27093540220423604183050643 40640310330635406274575965)
          ·
            refine ⟨15240116373988277352965987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40640310330635406274575965 15240116373988277352965987)
            ·
              refine ⟨22860174560982416029448981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240116373988277352965987 22860174560982416029448981)
              ·
                refine ⟨1071570682546050751380421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22860174560982416029448981 1071570682546050751380421)
                ·
                  refine ⟨200919502977384515883829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071570682546050751380421 200919502977384515883829)
                  ·
                    rfl

theorem cell21_880401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_880401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880401 prefixEnd_880401 := by exact prefixLift 880401
  have htrace : WordTrace (prefixWord ++ tailWord_880401) baseStart_880401 baseEnd_880401 := by
    simpa [prefixWord, tailWord_880401, baseEnd_880401] using wordTrace_append hprefix tailTrace_880401
  have hstable : (prefixWord ++ tailWord_880401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880401).length < 2 ^ (prefixWord ++ tailWord_880401).sum := by decide
  have hdescent : baseEnd_880401 < baseStart_880401 := by decide
  rcases family_descends (prefixWord ++ tailWord_880401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880418 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_880418 : Nat := 118140960795 + 880418 * 2 ^ 59
def prefixEnd_880418 : Nat := 4983230072969 + 3 ^ 40 * 880418 * 2
def baseEnd_880418 : Nat := 200923382608996264100461

theorem tailTrace_880418 : CollatzResearch.WordTrace tailWord_880418 prefixEnd_880418 200923382608996264100461 := by
  unfold tailWord_880418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027870631100856067116477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21407655016268949512310605 8027870631100856067116477)
  ·
    refine ⟨3010451486662821025168679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8027870631100856067116477 3010451486662821025168679)
    ·
      refine ⟨4515677229994231537753019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010451486662821025168679 4515677229994231537753019)
      ·
        refine ⟨6773515844991347306629529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515677229994231537753019 6773515844991347306629529)
        ·
          refine ⟨5080136883743510479972147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773515844991347306629529 5080136883743510479972147)
          ·
            refine ⟨7620205325615265719958221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080136883743510479972147 7620205325615265719958221)
            ·
              refine ⟨2857576997105724644984333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7620205325615265719958221 2857576997105724644984333)
              ·
                refine ⟨1071591373914646741869125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2857576997105724644984333 1071591373914646741869125)
                ·
                  refine ⟨200923382608996264100461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071591373914646741869125 200923382608996264100461)
                  ·
                    rfl

theorem cell21_880418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_880418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880418 prefixEnd_880418 := by exact prefixLift 880418
  have htrace : WordTrace (prefixWord ++ tailWord_880418) baseStart_880418 baseEnd_880418 := by
    simpa [prefixWord, tailWord_880418, baseEnd_880418] using wordTrace_append hprefix tailTrace_880418
  have hstable : (prefixWord ++ tailWord_880418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880418).length < 2 ^ (prefixWord ++ tailWord_880418).sum := by decide
  have hdescent : baseEnd_880418 < baseStart_880418 := by decide
  rcases family_descends (prefixWord ++ tailWord_880418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880542 : List Nat := [4, 3, 1, 3, 1, 1, 1, 7]
def baseStart_880542 : Nat := 118140960795 + 880542 * 2 ^ 59
def prefixEnd_880542 : Nat := 4983230072969 + 3 ^ 40 * 880542 * 2
def baseEnd_880542 : Nat := 66983893699466534677847

theorem tailTrace_880542 : CollatzResearch.WordTrace tailWord_880542 prefixEnd_880542 66983893699466534677847 := by
  unfold tailWord_880542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014500646994274180747485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21410670117302795630653253 4014500646994274180747485)
  ·
    refine ⟨1505437742622852817780307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4014500646994274180747485 1505437742622852817780307)
    ·
      refine ⟨2258156613934279226670461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505437742622852817780307 2258156613934279226670461)
      ·
        refine ⟨846808730225354710001423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2258156613934279226670461 846808730225354710001423)
        ·
          refine ⟨1270213095338032065002135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846808730225354710001423 1270213095338032065002135)
          ·
            refine ⟨1905319643007048097503203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270213095338032065002135 1905319643007048097503203)
            ·
              refine ⟨2857979464510572146254805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905319643007048097503203 2857979464510572146254805)
              ·
                refine ⟨66983893699466534677847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2857979464510572146254805 66983893699466534677847)
                ·
                  rfl

theorem cell21_880542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_880542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880542 prefixEnd_880542 := by exact prefixLift 880542
  have htrace : WordTrace (prefixWord ++ tailWord_880542) baseStart_880542 baseEnd_880542 := by
    simpa [prefixWord, tailWord_880542, baseEnd_880542] using wordTrace_append hprefix tailTrace_880542
  have hstable : (prefixWord ++ tailWord_880542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880542).length < 2 ^ (prefixWord ++ tailWord_880542).sum := by decide
  have hdescent : baseEnd_880542 < baseStart_880542 := by decide
  rcases family_descends (prefixWord ++ tailWord_880542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880573 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 3]
def baseStart_880573 : Nat := 118140960795 + 880573 * 2 ^ 59
def prefixEnd_880573 : Nat := 4983230072969 + 3 ^ 40 * 880573 * 2
def baseEnd_880573 : Nat := 200958755720750439016811

theorem tailTrace_880573 : CollatzResearch.WordTrace tailWord_880573 prefixEnd_880573 200958755720750439016811 := by
  unfold tailWord_880573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32117135838841885740358373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411423892561257160238915 32117135838841885740358373)
  ·
    refine ⟨6021962969782853576317195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32117135838841885740358373 6021962969782853576317195)
    ·
      refine ⟨9032944454674280364475793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021962969782853576317195 9032944454674280364475793)
      ·
        refine ⟨6774708341005710273356845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9032944454674280364475793 6774708341005710273356845)
        ·
          refine ⟨2540515627877141352508817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6774708341005710273356845 2540515627877141352508817)
          ·
            refine ⟨1905386720907856014381613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2540515627877141352508817 1905386720907856014381613)
            ·
              refine ⟨714520020340446005393105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1905386720907856014381613 714520020340446005393105)
              ·
                refine ⟨535890015255334504044829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714520020340446005393105 535890015255334504044829)
                ·
                  refine ⟨200958755720750439016811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535890015255334504044829 200958755720750439016811)
                  ·
                    rfl

theorem cell21_880573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_880573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880573 prefixEnd_880573 := by exact prefixLift 880573
  have htrace : WordTrace (prefixWord ++ tailWord_880573) baseStart_880573 baseEnd_880573 := by
    simpa [prefixWord, tailWord_880573, baseEnd_880573] using wordTrace_append hprefix tailTrace_880573
  have hstable : (prefixWord ++ tailWord_880573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880573).length < 2 ^ (prefixWord ++ tailWord_880573).sum := by decide
  have hdescent : baseEnd_880573 < baseStart_880573 := by decide
  rcases family_descends (prefixWord ++ tailWord_880573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880584 : List Nat := [2, 1, 3, 1, 4, 2, 2, 6]
def baseStart_880584 : Nat := 118140960795 + 880584 * 2 ^ 59
def prefixEnd_880584 : Nat := 4983230072969 + 3 ^ 40 * 880584 * 2
def baseEnd_880584 : Nat := 66987088690205621444485

theorem tailTrace_880584 : CollatzResearch.WordTrace tailWord_880584 prefixEnd_880584 66987088690205621444485 := by
  unfold tailWord_880584
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058768520901017309504403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21411691361201356412672537 16058768520901017309504403)
  ·
    refine ⟨24088152781351525964256605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058768520901017309504403 24088152781351525964256605)
    ·
      refine ⟨9033057293006822236596227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24088152781351525964256605 9033057293006822236596227)
      ·
        refine ⟨13549585939510233354894341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033057293006822236596227 13549585939510233354894341)
        ·
          refine ⟨2540547363658168754042689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13549585939510233354894341 2540547363658168754042689)
          ·
            refine ⟨1905410522743626565532017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2540547363658168754042689 1905410522743626565532017)
            ·
              refine ⟨1429057892057719924149013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905410522743626565532017 1429057892057719924149013)
              ·
                refine ⟨66987088690205621444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1429057892057719924149013 66987088690205621444485)
                ·
                  rfl

theorem cell21_880584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_880584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880584 prefixEnd_880584 := by exact prefixLift 880584
  have htrace : WordTrace (prefixWord ++ tailWord_880584) baseStart_880584 baseEnd_880584 := by
    simpa [prefixWord, tailWord_880584, baseEnd_880584] using wordTrace_append hprefix tailTrace_880584
  have hstable : (prefixWord ++ tailWord_880584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880584).length < 2 ^ (prefixWord ++ tailWord_880584).sum := by decide
  have hdescent : baseEnd_880584 < baseStart_880584 := by decide
  rcases family_descends (prefixWord ++ tailWord_880584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880632 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_880632 : Nat := 118140960795 + 880632 * 2 ^ 59
def prefixEnd_880632 : Nat := 4983230072969 + 3 ^ 40 * 880632 * 2
def baseEnd_880632 : Nat := 200972220324579447533357

theorem tailTrace_880632 : CollatzResearch.WordTrace tailWord_880632 prefixEnd_880632 200972220324579447533357 := by
  unfold tailWord_880632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059643872814069408378075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21412858497085425877837433 16059643872814069408378075)
  ·
    refine ⟨24089465809221104112567113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16059643872814069408378075 24089465809221104112567113)
    ·
      refine ⟨18067099356915828084425335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24089465809221104112567113 18067099356915828084425335)
      ·
        refine ⟨27100649035373742126638003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18067099356915828084425335 27100649035373742126638003)
        ·
          refine ⟨40650973553060613189957005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27100649035373742126638003 40650973553060613189957005)
          ·
            refine ⟨15244115082397729946233877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40650973553060613189957005 15244115082397729946233877)
            ·
              refine ⟨714567894487393591229713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15244115082397729946233877 714567894487393591229713)
              ·
                refine ⟨535925920865545193422285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714567894487393591229713 535925920865545193422285)
                ·
                  refine ⟨200972220324579447533357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535925920865545193422285 200972220324579447533357)
                  ·
                    rfl

theorem cell21_880632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_880632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880632 prefixEnd_880632 := by exact prefixLift 880632
  have htrace : WordTrace (prefixWord ++ tailWord_880632) baseStart_880632 baseEnd_880632 := by
    simpa [prefixWord, tailWord_880632, baseEnd_880632] using wordTrace_append hprefix tailTrace_880632
  have hstable : (prefixWord ++ tailWord_880632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880632).length < 2 ^ (prefixWord ++ tailWord_880632).sum := by decide
  have hdescent : baseEnd_880632 < baseStart_880632 := by decide
  rcases family_descends (prefixWord ++ tailWord_880632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880674 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_880674 : Nat := 118140960795 + 880674 * 2 ^ 59
def prefixEnd_880674 : Nat := 4983230072969 + 3 ^ 40 * 880674 * 2
def baseEnd_880674 : Nat := 200981805296796707833271

theorem tailTrace_880674 : CollatzResearch.WordTrace tailWord_880674 prefixEnd_880674 200981805296796707833271 := by
  unfold tailWord_880674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030204902868994997446269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21413879740983986659856717 8030204902868994997446269)
  ·
    refine ⟨3011326838575873124042351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8030204902868994997446269 3011326838575873124042351)
    ·
      refine ⟨4516990257863809686063527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011326838575873124042351 4516990257863809686063527)
      ·
        refine ⟨6775485386795714529095291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516990257863809686063527 6775485386795714529095291)
        ·
          refine ⟨10163228080193571793642937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6775485386795714529095291 10163228080193571793642937)
          ·
            refine ⟨7622421060145178845232203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10163228080193571793642937 7622421060145178845232203)
            ·
              refine ⟨11433631590217768267848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622421060145178845232203 11433631590217768267848305)
              ·
                refine ⟨8575223692663326200886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433631590217768267848305 8575223692663326200886229)
                ·
                  refine ⟨200981805296796707833271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8575223692663326200886229 200981805296796707833271)
                  ·
                    rfl

theorem cell21_880674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_880674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880674 prefixEnd_880674 := by exact prefixLift 880674
  have htrace : WordTrace (prefixWord ++ tailWord_880674) baseStart_880674 baseEnd_880674 := by
    simpa [prefixWord, tailWord_880674, baseEnd_880674] using wordTrace_append hprefix tailTrace_880674
  have hstable : (prefixWord ++ tailWord_880674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880674).length < 2 ^ (prefixWord ++ tailWord_880674).sum := by decide
  have hdescent : baseEnd_880674 < baseStart_880674 := by decide
  rcases family_descends (prefixWord ++ tailWord_880674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880680 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_880680 : Nat := 118140960795 + 880680 * 2 ^ 59
def prefixEnd_880680 : Nat := 4983230072969 + 3 ^ 40 * 880680 * 2
def baseEnd_880680 : Nat := 200983174578542030733259

theorem tailTrace_880680 : CollatzResearch.WordTrace tailWord_880680 prefixEnd_880680 200983174578542030733259 := by
  unfold tailWord_880680
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060519224727121507251747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21414025632969495343002329 16060519224727121507251747)
  ·
    refine ⟨24090778837090682260877621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16060519224727121507251747 24090778837090682260877621)
    ·
      refine ⟨2258510515977251461957277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24090778837090682260877621 2258510515977251461957277)
      ·
        refine ⟨846941443491469298233979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2258510515977251461957277 846941443491469298233979)
        ·
          refine ⟨1270412165237203947350969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846941443491469298233979 1270412165237203947350969)
          ·
            refine ⟨952809123927902960513227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270412165237203947350969 952809123927902960513227)
            ·
              refine ⟨1429213685891854440769841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952809123927902960513227 1429213685891854440769841)
              ·
                refine ⟨1071910264418890830577381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429213685891854440769841 1071910264418890830577381)
                ·
                  refine ⟨200983174578542030733259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071910264418890830577381 200983174578542030733259)
                  ·
                    rfl

theorem cell21_880680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_880680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880680 prefixEnd_880680 := by exact prefixLift 880680
  have htrace : WordTrace (prefixWord ++ tailWord_880680) baseStart_880680 baseEnd_880680 := by
    simpa [prefixWord, tailWord_880680, baseEnd_880680] using wordTrace_append hprefix tailTrace_880680
  have hstable : (prefixWord ++ tailWord_880680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880680).length < 2 ^ (prefixWord ++ tailWord_880680).sum := by decide
  have hdescent : baseEnd_880680 < baseStart_880680 := by decide
  rcases family_descends (prefixWord ++ tailWord_880680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880691 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 3]
def baseStart_880691 : Nat := 118140960795 + 880691 * 2 ^ 59
def prefixEnd_880691 : Nat := 4983230072969 + 3 ^ 40 * 880691 * 2
def baseEnd_880691 : Nat := 200985684928408456049903

theorem tailTrace_880691 : CollatzResearch.WordTrace tailWord_880691 prefixEnd_880691 200985684928408456049903 := by
  unfold tailWord_880691
  simp only [CollatzResearch.WordTrace]
  refine ⟨32121439652414391893153927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21414293101609594595435951 32121439652414391893153927)
  ·
    refine ⟨48182159478621587839730891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32121439652414391893153927 48182159478621587839730891)
    ·
      refine ⟨72273239217932381759596337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48182159478621587839730891 72273239217932381759596337)
      ·
        refine ⟨54204929413449286319697253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72273239217932381759596337 54204929413449286319697253)
        ·
          refine ⟨10163424265021741184943235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54204929413449286319697253 10163424265021741184943235)
          ·
            refine ⟨15245136397532611777414853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163424265021741184943235 15245136397532611777414853)
            ·
              refine ⟨2858463074537364708265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15245136397532611777414853 2858463074537364708265285)
              ·
                refine ⟨535961826475755882799741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2858463074537364708265285 535961826475755882799741)
                ·
                  refine ⟨200985684928408456049903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535961826475755882799741 200985684928408456049903)
                  ·
                    rfl

theorem cell21_880691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].length) (baseStart_880691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880691 prefixEnd_880691 := by exact prefixLift 880691
  have htrace : WordTrace (prefixWord ++ tailWord_880691) baseStart_880691 baseEnd_880691 := by
    simpa [prefixWord, tailWord_880691, baseEnd_880691] using wordTrace_append hprefix tailTrace_880691
  have hstable : (prefixWord ++ tailWord_880691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880691).length < 2 ^ (prefixWord ++ tailWord_880691).sum := by decide
  have hdescent : baseEnd_880691 < baseStart_880691 := by decide
  rcases family_descends (prefixWord ++ tailWord_880691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880790 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_880790 : Nat := 118140960795 + 880790 * 2 ^ 59
def prefixEnd_880790 : Nat := 4983230072969 + 3 ^ 40 * 880790 * 2
def baseEnd_880790 : Nat := 201008278077206283899701

theorem tailTrace_880790 : CollatzResearch.WordTrace tailWord_880790 prefixEnd_880790 201008278077206283899701 := by
  unfold tailWord_880790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007815654940983237562989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21416700319370487867338549 2007815654940983237562989)
  ·
    refine ⟨752930870602868714086121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2007815654940983237562989 752930870602868714086121)
    ·
      refine ⟨564698152952151535564591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752930870602868714086121 564698152952151535564591)
      ·
        refine ⟨847047229428227303346887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564698152952151535564591 847047229428227303346887)
        ·
          refine ⟨1270570844142340955020331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847047229428227303346887 1270570844142340955020331)
          ·
            refine ⟨1905856266213511432530497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270570844142340955020331 1905856266213511432530497)
            ·
              refine ⟨1429392199660133574397873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905856266213511432530497 1429392199660133574397873)
              ·
                refine ⟨1072044149745100180798405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429392199660133574397873 1072044149745100180798405)
                ·
                  refine ⟨201008278077206283899701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072044149745100180798405 201008278077206283899701)
                  ·
                    rfl

theorem cell21_880790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_880790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880790 prefixEnd_880790 := by exact prefixLift 880790
  have htrace : WordTrace (prefixWord ++ tailWord_880790) baseStart_880790 baseEnd_880790 := by
    simpa [prefixWord, tailWord_880790, baseEnd_880790] using wordTrace_append hprefix tailTrace_880790
  have hstable : (prefixWord ++ tailWord_880790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880790).length < 2 ^ (prefixWord ++ tailWord_880790).sum := by decide
  have hdescent : baseEnd_880790 < baseStart_880790 := by decide
  rcases family_descends (prefixWord ++ tailWord_880790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880801 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 3]
def baseStart_880801 : Nat := 118140960795 + 880801 * 2 ^ 59
def prefixEnd_880801 : Nat := 4983230072969 + 3 ^ 40 * 880801 * 2
def baseEnd_880801 : Nat := 201010788427072709216345

theorem tailTrace_880801 : CollatzResearch.WordTrace tailWord_880801 prefixEnd_880801 201010788427072709216345 := by
  unfold tailWord_880801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125451682015880679658257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21416967788010587119772171 32125451682015880679658257)
  ·
    refine ⟨24094088761511910509743693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32125451682015880679658257 24094088761511910509743693)
    ·
      refine ⟨9035283285566966441153885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24094088761511910509743693 9035283285566966441153885)
      ·
        refine ⟨3388231232087612415432707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9035283285566966441153885 3388231232087612415432707)
        ·
          refine ⟨5082346848131418623149061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388231232087612415432707 5082346848131418623149061)
          ·
            refine ⟨952940034024640991840449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5082346848131418623149061 952940034024640991840449)
            ·
              refine ⟨714705025518480743880337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952940034024640991840449 714705025518480743880337)
              ·
                refine ⟨536028769138860557910253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714705025518480743880337 536028769138860557910253)
                ·
                  refine ⟨201010788427072709216345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536028769138860557910253 201010788427072709216345)
                  ·
                    rfl

theorem cell21_880801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_880801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880801 prefixEnd_880801 := by exact prefixLift 880801
  have htrace : WordTrace (prefixWord ++ tailWord_880801) baseStart_880801 baseEnd_880801 := by
    simpa [prefixWord, tailWord_880801, baseEnd_880801] using wordTrace_append hprefix tailTrace_880801
  have hstable : (prefixWord ++ tailWord_880801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880801).length < 2 ^ (prefixWord ++ tailWord_880801).sum := by decide
  have hdescent : baseEnd_880801 < baseStart_880801 := by decide
  rcases family_descends (prefixWord ++ tailWord_880801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880840 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_880840 : Nat := 118140960795 + 880840 * 2 ^ 59
def prefixEnd_880840 : Nat := 4983230072969 + 3 ^ 40 * 880840 * 2
def baseEnd_880840 : Nat := 201019688758417308066265

theorem tailTrace_880840 : CollatzResearch.WordTrace tailWord_880840 prefixEnd_880840 201019688758417308066265 := by
  unfold tailWord_880840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063437064437295170163987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21417916085916393560218649 16063437064437295170163987)
  ·
    refine ⟨24095155596655942755245981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16063437064437295170163987 24095155596655942755245981)
    ·
      refine ⟨9035683348745978533217243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24095155596655942755245981 9035683348745978533217243)
      ·
        refine ⟨13553525023118967799825865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035683348745978533217243 13553525023118967799825865)
        ·
          refine ⟨10165143767339225849869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13553525023118967799825865 10165143767339225849869399)
          ·
            refine ⟨15247715651008838774804099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165143767339225849869399 15247715651008838774804099)
            ·
              refine ⟨22871573476513258162206149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15247715651008838774804099 22871573476513258162206149)
              ·
                refine ⟨4288420026846235905413653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22871573476513258162206149 4288420026846235905413653)
                ·
                  refine ⟨201019688758417308066265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4288420026846235905413653 201019688758417308066265)
                  ·
                    rfl

theorem cell21_880840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_880840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880840 prefixEnd_880840 := by exact prefixLift 880840
  have htrace : WordTrace (prefixWord ++ tailWord_880840) baseStart_880840 baseEnd_880840 := by
    simpa [prefixWord, tailWord_880840, baseEnd_880840] using wordTrace_append hprefix tailTrace_880840
  have hstable : (prefixWord ++ tailWord_880840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880840).length < 2 ^ (prefixWord ++ tailWord_880840).sum := by decide
  have hdescent : baseEnd_880840 < baseStart_880840 := by decide
  rcases family_descends (prefixWord ++ tailWord_880840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880843 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 3]
def baseStart_880843 : Nat := 118140960795 + 880843 * 2 ^ 59
def prefixEnd_880843 : Nat := 4983230072969 + 3 ^ 40 * 880843 * 2
def baseEnd_880843 : Nat := 201020373399289969516259

theorem tailTrace_880843 : CollatzResearch.WordTrace tailWord_880843 prefixEnd_880843 201020373399289969516259 := by
  unfold tailWord_880843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126983547863721852687183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21417989031909147901791455 32126983547863721852687183)
  ·
    refine ⟨48190475321795582779030775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32126983547863721852687183 48190475321795582779030775)
    ·
      refine ⟨72285712982693374168546163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48190475321795582779030775 72285712982693374168546163)
      ·
        refine ⟨108428569474040061252819245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72285712982693374168546163 108428569474040061252819245)
        ·
          refine ⟨40660713552765022969807217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108428569474040061252819245 40660713552765022969807217)
          ·
            refine ⟨30495535164573767227355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40660713552765022969807217 30495535164573767227355413)
            ·
              refine ⟨1429478210839395338782285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30495535164573767227355413 1429478210839395338782285)
              ·
                refine ⟨536054329064773252043357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1429478210839395338782285 536054329064773252043357)
                ·
                  refine ⟨201020373399289969516259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536054329064773252043357 201020373399289969516259)
                  ·
                    rfl

theorem cell21_880843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].length) (baseStart_880843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880843 prefixEnd_880843 := by exact prefixLift 880843
  have htrace : WordTrace (prefixWord ++ tailWord_880843) baseStart_880843 baseEnd_880843 := by
    simpa [prefixWord, tailWord_880843, baseEnd_880843] using wordTrace_append hprefix tailTrace_880843
  have hstable : (prefixWord ++ tailWord_880843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880843).length < 2 ^ (prefixWord ++ tailWord_880843).sum := by decide
  have hdescent : baseEnd_880843 < baseStart_880843 := by decide
  rcases family_descends (prefixWord ++ tailWord_880843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880857 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_880857 : Nat := 118140960795 + 880857 * 2 ^ 59
def prefixEnd_880857 : Nat := 4983230072969 + 3 ^ 40 * 880857 * 2
def baseEnd_880857 : Nat := 201023568390029056282897

theorem tailTrace_880857 : CollatzResearch.WordTrace tailWord_880857 prefixEnd_880857 201023568390029056282897 := by
  unfold tailWord_880857
  simp only [CollatzResearch.WordTrace]
  refine ⟨32127494169813002243696825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21418329446542001495797883 32127494169813002243696825)
  ·
    refine ⟨24095620627359751682772619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32127494169813002243696825 24095620627359751682772619)
    ·
      refine ⟨36143430941039627524158929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24095620627359751682772619 36143430941039627524158929)
      ·
        refine ⟨27107573205779720643119197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36143430941039627524158929 27107573205779720643119197)
        ·
          refine ⟨10165339952167395241169699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27107573205779720643119197 10165339952167395241169699)
          ·
            refine ⟨15248009928251092861754549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165339952167395241169699 15248009928251092861754549)
            ·
              refine ⟨1429500930773539955789489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15248009928251092861754549 1429500930773539955789489)
              ·
                refine ⟨1072125698080154966842117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429500930773539955789489 1072125698080154966842117)
                ·
                  refine ⟨201023568390029056282897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072125698080154966842117 201023568390029056282897)
                  ·
                    rfl

theorem cell21_880857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_880857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880857 prefixEnd_880857 := by exact prefixLift 880857
  have htrace : WordTrace (prefixWord ++ tailWord_880857) baseStart_880857 baseEnd_880857 := by
    simpa [prefixWord, tailWord_880857, baseEnd_880857] using wordTrace_append hprefix tailTrace_880857
  have hstable : (prefixWord ++ tailWord_880857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880857).length < 2 ^ (prefixWord ++ tailWord_880857).sum := by decide
  have hdescent : baseEnd_880857 < baseStart_880857 := by decide
  rcases family_descends (prefixWord ++ tailWord_880857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880874 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_880874 : Nat := 118140960795 + 880874 * 2 ^ 59
def prefixEnd_880874 : Nat := 4983230072969 + 3 ^ 40 * 880874 * 2
def baseEnd_880874 : Nat := 201027448021640804499529

theorem tailTrace_880874 : CollatzResearch.WordTrace tailWord_880874 prefixEnd_880874 201027448021640804499529 := by
  unfold tailWord_880874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032028552687853536766419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21418742807167609431377117 8032028552687853536766419)
  ·
    refine ⟨12048042829031780305149629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8032028552687853536766419 12048042829031780305149629)
    ·
      refine ⟨4518016060886917614431111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12048042829031780305149629 4518016060886917614431111)
      ·
        refine ⟨6777024091330376421646667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518016060886917614431111 6777024091330376421646667)
        ·
          refine ⟨10165536136995564632470001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777024091330376421646667 10165536136995564632470001)
          ·
            refine ⟨7624152102746673474352501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10165536136995564632470001 7624152102746673474352501)
            ·
              refine ⟨714764259632500638220547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7624152102746673474352501 714764259632500638220547)
              ·
                refine ⟨1072146389448750957330821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714764259632500638220547 1072146389448750957330821)
                ·
                  refine ⟨201027448021640804499529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072146389448750957330821 201027448021640804499529)
                  ·
                    rfl

theorem cell21_880874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_880874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880874 prefixEnd_880874 := by exact prefixLift 880874
  have htrace : WordTrace (prefixWord ++ tailWord_880874) baseStart_880874 baseEnd_880874 := by
    simpa [prefixWord, tailWord_880874, baseEnd_880874] using wordTrace_append hprefix tailTrace_880874
  have hstable : (prefixWord ++ tailWord_880874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880874).length < 2 ^ (prefixWord ++ tailWord_880874).sum := by decide
  have hdescent : baseEnd_880874 < baseStart_880874 := by decide
  rcases family_descends (prefixWord ++ tailWord_880874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880919 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_880919 : Nat := 118140960795 + 880919 * 2 ^ 59
def prefixEnd_880919 : Nat := 4983230072969 + 3 ^ 40 * 880919 * 2
def baseEnd_880919 : Nat := 201037717634730726249437

theorem tailTrace_880919 : CollatzResearch.WordTrace tailWord_880919 prefixEnd_880919 201037717634730726249437 := by
  unfold tailWord_880919
  simp only [CollatzResearch.WordTrace]
  refine ⟨32129755495588386832453811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21419836997058924554969207 32129755495588386832453811)
  ·
    refine ⟨48194633243382580248680717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32129755495588386832453811 48194633243382580248680717)
    ·
      refine ⟨18072987466268467593255269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48194633243382580248680717 18072987466268467593255269)
      ·
        refine ⟨3388685149925337673735363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18072987466268467593255269 3388685149925337673735363)
        ·
          refine ⟨5083027724888006510603045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388685149925337673735363 5083027724888006510603045)
          ·
            refine ⟨953067698416501220738071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5083027724888006510603045 953067698416501220738071)
            ·
              refine ⟨1429601547624751831107107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953067698416501220738071 1429601547624751831107107)
              ·
                refine ⟨2144402321437127746660661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429601547624751831107107 2144402321437127746660661)
                ·
                  refine ⟨201037717634730726249437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2144402321437127746660661 201037717634730726249437)
                  ·
                    rfl

theorem cell21_880919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_880919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880919 prefixEnd_880919 := by exact prefixLift 880919
  have htrace : WordTrace (prefixWord ++ tailWord_880919) baseStart_880919 baseEnd_880919 := by
    simpa [prefixWord, tailWord_880919, baseEnd_880919] using wordTrace_append hprefix tailTrace_880919
  have hstable : (prefixWord ++ tailWord_880919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880919).length < 2 ^ (prefixWord ++ tailWord_880919).sum := by decide
  have hdescent : baseEnd_880919 < baseStart_880919 := by decide
  rcases family_descends (prefixWord ++ tailWord_880919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880964 : List Nat := [2, 3, 4, 1, 2, 9]
def baseStart_880964 : Nat := 118140960795 + 880964 * 2 ^ 59
def prefixEnd_880964 : Nat := 4983230072969 + 3 ^ 40 * 880964 * 2
def baseEnd_880964 : Nat := 7446221749919283259235

theorem tailTrace_880964 : CollatzResearch.WordTrace tailWord_880964 prefixEnd_880964 7446221749919283259235 := by
  unfold tailWord_880964
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065698390212679758920973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21420931186950239678561297 16065698390212679758920973)
  ·
    refine ⟨6024636896329754909595365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16065698390212679758920973 6024636896329754909595365)
    ·
      refine ⟨1129619418061829045549131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6024636896329754909595365 1129619418061829045549131)
      ·
        refine ⟨1694429127092743568323697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129619418061829045549131 1694429127092743568323697)
        ·
          refine ⟨1270821845319557676242773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694429127092743568323697 1270821845319557676242773)
          ·
            refine ⟨7446221749919283259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1270821845319557676242773 7446221749919283259235)
            ·
              rfl

theorem cell21_880964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 9].length) (baseStart_880964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880964 prefixEnd_880964 := by exact prefixLift 880964
  have htrace : WordTrace (prefixWord ++ tailWord_880964) baseStart_880964 baseEnd_880964 := by
    simpa [prefixWord, tailWord_880964, baseEnd_880964] using wordTrace_append hprefix tailTrace_880964
  have hstable : (prefixWord ++ tailWord_880964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880964).length < 2 ^ (prefixWord ++ tailWord_880964).sum := by decide
  have hdescent : baseEnd_880964 < baseStart_880964 := by decide
  rcases family_descends (prefixWord ++ tailWord_880964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880981 : List Nat := [1, 3, 2, 2, 5, 1, 1, 6]
def baseStart_880981 : Nat := 118140960795 + 880981 * 2 ^ 59
def prefixEnd_880981 : Nat := 4983230072969 + 3 ^ 40 * 880981 * 2
def baseEnd_880981 : Nat := 67017288959810798738659

theorem tailTrace_880981 : CollatzResearch.WordTrace tailWord_880981 prefixEnd_880981 67017288959810798738659 := by
  unfold tailWord_880981
  simp only [CollatzResearch.WordTrace]
  refine ⟨32132016821363771421210797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21421344547575847614140531 32132016821363771421210797)
  ·
    refine ⟨12049506308011414282954049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32132016821363771421210797 12049506308011414282954049)
    ·
      refine ⟨9037129731008560712215537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12049506308011414282954049 9037129731008560712215537)
      ·
        refine ⟨6777847298256420534161653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9037129731008560712215537 6777847298256420534161653)
        ·
          refine ⟨635423184211539425077655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6777847298256420534161653 635423184211539425077655)
          ·
            refine ⟨953134776317309137616483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635423184211539425077655 953134776317309137616483)
            ·
              refine ⟨1429702164475963706424725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953134776317309137616483 1429702164475963706424725)
              ·
                refine ⟨67017288959810798738659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1429702164475963706424725 67017288959810798738659)
                ·
                  rfl

theorem cell21_880981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].length) (baseStart_880981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_880981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_880981 prefixEnd_880981 := by exact prefixLift 880981
  have htrace : WordTrace (prefixWord ++ tailWord_880981) baseStart_880981 baseEnd_880981 := by
    simpa [prefixWord, tailWord_880981, baseEnd_880981] using wordTrace_append hprefix tailTrace_880981
  have hstable : (prefixWord ++ tailWord_880981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880981).length < 2 ^ (prefixWord ++ tailWord_880981).sum := by decide
  have hdescent : baseEnd_880981 < baseStart_880981 := by decide
  rcases family_descends (prefixWord ++ tailWord_880981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881113 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_881113 : Nat := 118140960795 + 881113 * 2 ^ 59
def prefixEnd_881113 : Nat := 4983230072969 + 3 ^ 40 * 881113 * 2
def baseEnd_881113 : Nat := 201081991077829500015707

theorem tailTrace_881113 : CollatzResearch.WordTrace tailWord_881113 prefixEnd_881113 201081991077829500015707 := by
  unfold tailWord_881113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32136831256885557965015993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21424554171257038643343995 32136831256885557965015993)
  ·
    refine ⟨24102623442664168473761995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32136831256885557965015993 24102623442664168473761995)
    ·
      refine ⟨36153935163996252710642993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24102623442664168473761995 36153935163996252710642993)
      ·
        refine ⟨27115451372997189532982245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36153935163996252710642993 27115451372997189532982245)
        ·
          refine ⟨5084147132436973037434171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27115451372997189532982245 5084147132436973037434171)
          ·
            refine ⟨7626220698655459556151257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084147132436973037434171 7626220698655459556151257)
            ·
              refine ⟨5719665523991594667113443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626220698655459556151257 5719665523991594667113443)
              ·
                refine ⟨8579498285987392000670165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719665523991594667113443 8579498285987392000670165)
                ·
                  refine ⟨201081991077829500015707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8579498285987392000670165 201081991077829500015707)
                  ·
                    rfl

theorem cell21_881113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_881113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881113 prefixEnd_881113 := by exact prefixLift 881113
  have htrace : WordTrace (prefixWord ++ tailWord_881113) baseStart_881113 baseEnd_881113 := by
    simpa [prefixWord, tailWord_881113, baseEnd_881113] using wordTrace_append hprefix tailTrace_881113
  have hstable : (prefixWord ++ tailWord_881113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881113).length < 2 ^ (prefixWord ++ tailWord_881113).sum := by decide
  have hdescent : baseEnd_881113 < baseStart_881113 := by decide
  rcases family_descends (prefixWord ++ tailWord_881113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881279 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_881279 : Nat := 118140960795 + 881279 * 2 ^ 59
def prefixEnd_881279 : Nat := 4983230072969 + 3 ^ 40 * 881279 * 2
def baseEnd_881279 : Nat := 201119874539450100248701

theorem tailTrace_881279 : CollatzResearch.WordTrace tailWord_881279 prefixEnd_881279 201119874539450100248701 := by
  unfold tailWord_881279
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142885774284168315558891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428590516189445543705927 32142885774284168315558891)
  ·
    refine ⟨48214328661426252473338337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32142885774284168315558891 48214328661426252473338337)
    ·
      refine ⟨36160746496069689355003753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48214328661426252473338337 36160746496069689355003753)
      ·
        refine ⟨27120559872052267016252815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36160746496069689355003753 27120559872052267016252815)
        ·
          refine ⟨40680839808078400524379223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27120559872052267016252815 40680839808078400524379223)
          ·
            refine ⟨61021259712117600786568835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40680839808078400524379223 61021259712117600786568835)
            ·
              refine ⟨91531889568176401179853253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61021259712117600786568835 91531889568176401179853253)
              ·
                refine ⟨17162229294033075221222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91531889568176401179853253 17162229294033075221222485)
                ·
                  refine ⟨201119874539450100248701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17162229294033075221222485 201119874539450100248701)
                  ·
                    rfl

theorem cell21_881279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_881279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881279 prefixEnd_881279 := by exact prefixLift 881279
  have htrace : WordTrace (prefixWord ++ tailWord_881279) baseStart_881279 baseEnd_881279 := by
    simpa [prefixWord, tailWord_881279, baseEnd_881279] using wordTrace_append hprefix tailTrace_881279
  have hstable : (prefixWord ++ tailWord_881279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881279).length < 2 ^ (prefixWord ++ tailWord_881279).sum := by decide
  have hdescent : baseEnd_881279 < baseStart_881279 := by decide
  rcases family_descends (prefixWord ++ tailWord_881279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881327 : List Nat := [1, 1, 2, 1, 2, 7, 1, 6]
def baseStart_881327 : Nat := 118140960795 + 881327 * 2 ^ 59
def prefixEnd_881327 : Nat := 4983230072969 + 3 ^ 40 * 881327 * 2
def baseEnd_881327 : Nat := 67043609597804227816201

theorem tailTrace_881327 : CollatzResearch.WordTrace tailWord_881327 prefixEnd_881327 67043609597804227816201 := by
  unfold tailWord_881327
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144636478110272513306235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21429757652073515008870823 32144636478110272513306235)
  ·
    refine ⟨48216954717165408769959353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32144636478110272513306235 48216954717165408769959353)
    ·
      refine ⟨36162716037874056577469515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48216954717165408769959353 36162716037874056577469515)
      ·
        refine ⟨54244074056811084866204273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36162716037874056577469515 54244074056811084866204273)
        ·
          refine ⟨40683055542608313649653205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54244074056811084866204273 40683055542608313649653205)
          ·
            refine ⟨953509114279882351163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 40683055542608313649653205 953509114279882351163747)
            ·
              refine ⟨1430263671419823526745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953509114279882351163747 1430263671419823526745621)
              ·
                refine ⟨67043609597804227816201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1430263671419823526745621 67043609597804227816201)
                ·
                  rfl

theorem cell21_881327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_881327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881327 prefixEnd_881327 := by exact prefixLift 881327
  have htrace : WordTrace (prefixWord ++ tailWord_881327) baseStart_881327 baseEnd_881327 := by
    simpa [prefixWord, tailWord_881327, baseEnd_881327] using wordTrace_append hprefix tailTrace_881327
  have hstable : (prefixWord ++ tailWord_881327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881327).length < 2 ^ (prefixWord ++ tailWord_881327).sum := by decide
  have hdescent : baseEnd_881327 < baseStart_881327 := by decide
  rcases family_descends (prefixWord ++ tailWord_881327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881341 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_881341 : Nat := 118140960795 + 881341 * 2 ^ 59
def prefixEnd_881341 : Nat := 4983230072969 + 3 ^ 40 * 881341 * 2
def baseEnd_881341 : Nat := 201134023784151770215241

theorem tailTrace_881341 : CollatzResearch.WordTrace tailWord_881341 prefixEnd_881341 201134023784151770215241 := by
  unfold tailWord_881341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32145147100059552904315877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21430098066706368602877251 32145147100059552904315877)
  ·
    refine ⟨6027215081261166169559227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32145147100059552904315877 6027215081261166169559227)
    ·
      refine ⟨9040822621891749254338841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027215081261166169559227 9040822621891749254338841)
      ·
        refine ⟨6780616966418811940754131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9040822621891749254338841 6780616966418811940754131)
        ·
          refine ⟨10170925449628217911131197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780616966418811940754131 10170925449628217911131197)
          ·
            refine ⟨3814097043610581716674199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10170925449628217911131197 3814097043610581716674199)
            ·
              refine ⟨5721145565415872575011299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814097043610581716674199 5721145565415872575011299)
              ·
                refine ⟨8581718348123808862516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721145565415872575011299 8581718348123808862516949)
                ·
                  refine ⟨201134023784151770215241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8581718348123808862516949 201134023784151770215241)
                  ·
                    rfl

theorem cell21_881341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_881341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881341 prefixEnd_881341 := by exact prefixLift 881341
  have htrace : WordTrace (prefixWord ++ tailWord_881341) baseStart_881341 baseEnd_881341 := by
    simpa [prefixWord, tailWord_881341, baseEnd_881341] using wordTrace_append hprefix tailTrace_881341
  have hstable : (prefixWord ++ tailWord_881341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881341).length < 2 ^ (prefixWord ++ tailWord_881341).sum := by decide
  have hdescent : baseEnd_881341 < baseStart_881341 := by decide
  rcases family_descends (prefixWord ++ tailWord_881341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881350 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_881350 : Nat := 118140960795 + 881350 * 2 ^ 59
def prefixEnd_881350 : Nat := 4983230072969 + 3 ^ 40 * 881350 * 2
def baseEnd_881350 : Nat := 201136077706769754565223

theorem tailTrace_881350 : CollatzResearch.WordTrace tailWord_881350 prefixEnd_881350 201136077706769754565223 := by
  unfold tailWord_881350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004546104907092107543547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21430316904684631627595669 1004546104907092107543547)
  ·
    refine ⟨1506819157360638161315321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004546104907092107543547 1506819157360638161315321)
    ·
      refine ⟨1130114368020478620986491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1506819157360638161315321 1130114368020478620986491)
      ·
        refine ⟨1695171552030717931479737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130114368020478620986491 1695171552030717931479737)
        ·
          refine ⟨1271378664023038448609803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1695171552030717931479737 1271378664023038448609803)
          ·
            refine ⟨1907067996034557672914705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271378664023038448609803 1907067996034557672914705)
            ·
              refine ⟨1430300997025918254686029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907067996034557672914705 1430300997025918254686029)
              ·
                refine ⟨536362873884719345507261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1430300997025918254686029 536362873884719345507261)
                ·
                  refine ⟨201136077706769754565223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536362873884719345507261 201136077706769754565223)
                  ·
                    rfl

theorem cell21_881350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_881350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881350 prefixEnd_881350 := by exact prefixLift 881350
  have htrace : WordTrace (prefixWord ++ tailWord_881350) baseStart_881350 baseEnd_881350 := by
    simpa [prefixWord, tailWord_881350, baseEnd_881350] using wordTrace_append hprefix tailTrace_881350
  have hstable : (prefixWord ++ tailWord_881350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881350).length < 2 ^ (prefixWord ++ tailWord_881350).sum := by decide
  have hdescent : baseEnd_881350 < baseStart_881350 := by decide
  rcases family_descends (prefixWord ++ tailWord_881350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881386 : List Nat := [3, 1, 3, 1, 1, 1, 1, 10]
def baseStart_881386 : Nat := 118140960795 + 881386 * 2 ^ 59
def prefixEnd_881386 : Nat := 4983230072969 + 3 ^ 40 * 881386 * 2
def baseEnd_881386 : Nat := 67048097799080563988383

theorem tailTrace_881386 : CollatzResearch.WordTrace tailWord_881386 prefixEnd_881386 67048097799080563988383 := by
  unfold tailWord_881386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036697096224131397426003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21431192256597683726469341 8036697096224131397426003)
  ·
    refine ⟨12055045644336197096139005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8036697096224131397426003 12055045644336197096139005)
    ·
      refine ⟨4520642116626073911052127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12055045644336197096139005 4520642116626073911052127)
      ·
        refine ⟨6780963174939110866578191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520642116626073911052127 6780963174939110866578191)
        ·
          refine ⟨10171444762408666299867287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780963174939110866578191 10171444762408666299867287)
          ·
            refine ⟨15257167143612999449800931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171444762408666299867287 15257167143612999449800931)
            ·
              refine ⟨22885750715419499174701397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257167143612999449800931 22885750715419499174701397)
              ·
                refine ⟨67048097799080563988383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22885750715419499174701397 67048097799080563988383)
                ·
                  rfl

theorem cell21_881386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_881386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881386 prefixEnd_881386 := by exact prefixLift 881386
  have htrace : WordTrace (prefixWord ++ tailWord_881386) baseStart_881386 baseEnd_881386 := by
    simpa [prefixWord, tailWord_881386, baseEnd_881386] using wordTrace_append hprefix tailTrace_881386
  have hstable : (prefixWord ++ tailWord_881386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881386).length < 2 ^ (prefixWord ++ tailWord_881386).sum := by decide
  have hdescent : baseEnd_881386 < baseStart_881386 := by decide
  rcases family_descends (prefixWord ++ tailWord_881386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881493 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_881493 : Nat := 118140960795 + 881493 * 2 ^ 59
def prefixEnd_881493 : Nat := 4983230072969 + 3 ^ 40 * 881493 * 2
def baseEnd_881493 : Nat := 201168712255033283681597

theorem tailTrace_881493 : CollatzResearch.WordTrace tailWord_881493 prefixEnd_881493 201168712255033283681597 := by
  unfold tailWord_881493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32150690995508882863849133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21433793997005921909232755 32150690995508882863849133)
  ·
    refine ⟨12056509123315831073943425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32150690995508882863849133 12056509123315831073943425)
    ·
      refine ⟨9042381842486873305457569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12056509123315831073943425 9042381842486873305457569)
      ·
        refine ⟨6781786381865154979093177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042381842486873305457569 6781786381865154979093177)
        ·
          refine ⟨5086339786398866234319883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781786381865154979093177 5086339786398866234319883)
          ·
            refine ⟨7629509679598299351479825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086339786398866234319883 7629509679598299351479825)
            ·
              refine ⟨5722132259698724513609869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7629509679598299351479825 5722132259698724513609869)
              ·
                refine ⟨2145799597387021692603701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5722132259698724513609869 2145799597387021692603701)
                ·
                  refine ⟨201168712255033283681597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2145799597387021692603701 201168712255033283681597)
                  ·
                    rfl

theorem cell21_881493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_881493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881493 prefixEnd_881493 := by exact prefixLift 881493
  have htrace : WordTrace (prefixWord ++ tailWord_881493) baseStart_881493 baseEnd_881493 := by
    simpa [prefixWord, tailWord_881493, baseEnd_881493] using wordTrace_append hprefix tailTrace_881493
  have hstable : (prefixWord ++ tailWord_881493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881493).length < 2 ^ (prefixWord ++ tailWord_881493).sum := by decide
  have hdescent : baseEnd_881493 < baseStart_881493 := by decide
  rcases family_descends (prefixWord ++ tailWord_881493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881541 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_881541 : Nat := 118140960795 + 881541 * 2 ^ 59
def prefixEnd_881541 : Nat := 4983230072969 + 3 ^ 40 * 881541 * 2
def baseEnd_881541 : Nat := 201179666508995866881499

theorem tailTrace_881541 : CollatzResearch.WordTrace tailWord_881541 prefixEnd_881541 201179666508995866881499 := by
  unfold tailWord_881541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32152441699334987061596477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21434961132889991374397651 32152441699334987061596477)
  ·
    refine ⟨12057165637250620148098679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32152441699334987061596477 12057165637250620148098679)
    ·
      refine ⟨18085748455875930222148019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12057165637250620148098679 18085748455875930222148019)
      ·
        refine ⟨27128622683813895333222029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085748455875930222148019 27128622683813895333222029)
        ·
          refine ⟨10173233506430210749958261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27128622683813895333222029 10173233506430210749958261)
          ·
            refine ⟨953740641227832257808587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10173233506430210749958261 953740641227832257808587)
            ·
              refine ⟨1430610961841748386712881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953740641227832257808587 1430610961841748386712881)
              ·
                refine ⟨1072958221381311290034661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430610961841748386712881 1072958221381311290034661)
                ·
                  refine ⟨201179666508995866881499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072958221381311290034661 201179666508995866881499)
                  ·
                    rfl

theorem cell21_881541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_881541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881541 prefixEnd_881541 := by exact prefixLift 881541
  have htrace : WordTrace (prefixWord ++ tailWord_881541) baseStart_881541 baseEnd_881541 := by
    simpa [prefixWord, tailWord_881541, baseEnd_881541] using wordTrace_append hprefix tailTrace_881541
  have hstable : (prefixWord ++ tailWord_881541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881541).length < 2 ^ (prefixWord ++ tailWord_881541).sum := by decide
  have hdescent : baseEnd_881541 < baseStart_881541 := by decide
  rcases family_descends (prefixWord ++ tailWord_881541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881614 : List Nat := [4, 1, 1, 1, 2, 3, 1, 8]
def baseStart_881614 : Nat := 118140960795 + 881614 * 2 ^ 59
def prefixEnd_881614 : Nat := 4983230072969 + 3 ^ 40 * 881614 * 2
def baseEnd_881614 : Nat := 67065442034521320721561

theorem tailTrace_881614 : CollatzResearch.WordTrace tailWord_881614 prefixEnd_881614 67065442034521320721561 := by
  unfold tailWord_881614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019388028508815066125487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21436736152047013686002597 4019388028508815066125487)
  ·
    refine ⟨6029082042763222599188231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019388028508815066125487 6029082042763222599188231)
    ·
      refine ⟨9043623064144833898782347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029082042763222599188231 9043623064144833898782347)
      ·
        refine ⟨13565434596217250848173521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043623064144833898782347 13565434596217250848173521)
        ·
          refine ⟨10174075947162938136130141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13565434596217250848173521 10174075947162938136130141)
          ·
            refine ⟨3815278480186101801048803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10174075947162938136130141 3815278480186101801048803)
            ·
              refine ⟨5722917720279152701573205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815278480186101801048803 5722917720279152701573205)
              ·
                refine ⟨67065442034521320721561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5722917720279152701573205 67065442034521320721561)
                ·
                  rfl

theorem cell21_881614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_881614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881614 prefixEnd_881614 := by exact prefixLift 881614
  have htrace : WordTrace (prefixWord ++ tailWord_881614) baseStart_881614 baseEnd_881614 := by
    simpa [prefixWord, tailWord_881614, baseEnd_881614] using wordTrace_append hprefix tailTrace_881614
  have hstable : (prefixWord ++ tailWord_881614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881614).length < 2 ^ (prefixWord ++ tailWord_881614).sum := by decide
  have hdescent : baseEnd_881614 < baseStart_881614 := by decide
  rcases family_descends (prefixWord ++ tailWord_881614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881676 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_881676 : Nat := 118140960795 + 881676 * 2 ^ 59
def prefixEnd_881676 : Nat := 4983230072969 + 3 ^ 40 * 881676 * 2
def baseEnd_881676 : Nat := 201210475348265632131223

theorem tailTrace_881676 : CollatzResearch.WordTrace tailWord_881676 prefixEnd_881676 201210475348265632131223 := by
  unfold tailWord_881676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078682776922952558880441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21438243702563936745173921 16078682776922952558880441)
  ·
    refine ⟨12059012082692214419160331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16078682776922952558880441 12059012082692214419160331)
    ·
      refine ⟨18088518124038321628740497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12059012082692214419160331 18088518124038321628740497)
      ·
        refine ⟨13566388593028741221555373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18088518124038321628740497 13566388593028741221555373)
        ·
          refine ⟨5087395722385777958083265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13566388593028741221555373 5087395722385777958083265)
          ·
            refine ⟨3815546791789333468562449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5087395722385777958083265 3815546791789333468562449)
            ·
              refine ⟨2861660093842000101421837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815546791789333468562449 2861660093842000101421837)
              ·
                refine ⟨1073122535190750038033189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2861660093842000101421837 1073122535190750038033189)
                ·
                  refine ⟨201210475348265632131223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073122535190750038033189 201210475348265632131223)
                  ·
                    rfl

theorem cell21_881676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_881676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881676 prefixEnd_881676 := by exact prefixLift 881676
  have htrace : WordTrace (prefixWord ++ tailWord_881676) baseStart_881676 baseEnd_881676 := by
    simpa [prefixWord, tailWord_881676, baseEnd_881676] using wordTrace_append hprefix tailTrace_881676
  have hstable : (prefixWord ++ tailWord_881676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881676).length < 2 ^ (prefixWord ++ tailWord_881676).sum := by decide
  have hdescent : baseEnd_881676 < baseStart_881676 := by decide
  rcases family_descends (prefixWord ++ tailWord_881676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881682 : List Nat := [3, 2, 5, 1, 1, 1, 3, 5]
def baseStart_881682 : Nat := 118140960795 + 881682 * 2 ^ 59
def prefixEnd_881682 : Nat := 4983230072969 + 3 ^ 40 * 881682 * 2
def baseEnd_881682 : Nat := 67070614876670318343737

theorem tailTrace_881682 : CollatzResearch.WordTrace tailWord_881682 prefixEnd_881682 67070614876670318343737 := by
  unfold tailWord_881682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039396097956042035619825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21438389594549445428319533 8039396097956042035619825)
  ·
    refine ⟨6029547073467031526714869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8039396097956042035619825 6029547073467031526714869)
    ·
      refine ⟨565270038137534205629519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6029547073467031526714869 565270038137534205629519)
      ·
        refine ⟨847905057206301308444279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565270038137534205629519 847905057206301308444279)
        ·
          refine ⟨1271857585809451962666419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847905057206301308444279 1271857585809451962666419)
          ·
            refine ⟨1907786378714177943999629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271857585809451962666419 1907786378714177943999629)
            ·
              refine ⟨715419892017816728999861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907786378714177943999629 715419892017816728999861)
              ·
                refine ⟨67070614876670318343737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 715419892017816728999861 67070614876670318343737)
                ·
                  rfl

theorem cell21_881682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_881682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881682 prefixEnd_881682 := by exact prefixLift 881682
  have htrace : WordTrace (prefixWord ++ tailWord_881682) baseStart_881682 baseEnd_881682 := by
    simpa [prefixWord, tailWord_881682, baseEnd_881682] using wordTrace_append hprefix tailTrace_881682
  have hstable : (prefixWord ++ tailWord_881682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881682).length < 2 ^ (prefixWord ++ tailWord_881682).sum := by decide
  have hdescent : baseEnd_881682 < baseStart_881682 := by decide
  rcases family_descends (prefixWord ++ tailWord_881682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881696 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_881696 : Nat := 118140960795 + 881696 * 2 ^ 59
def prefixEnd_881696 : Nat := 4983230072969 + 3 ^ 40 * 881696 * 2
def baseEnd_881696 : Nat := 201215039620750041797849

theorem tailTrace_881696 : CollatzResearch.WordTrace tailWord_881696 prefixEnd_881696 201215039620750041797849 := by
  unfold tailWord_881696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079047506886724266744471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21438730009182299022325961 16079047506886724266744471)
  ·
    refine ⟨24118571260330086400116707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079047506886724266744471 24118571260330086400116707)
    ·
      refine ⟨36177856890495129600175061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24118571260330086400116707 36177856890495129600175061)
      ·
        refine ⟨847918520870979600004103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36177856890495129600175061 847918520870979600004103)
        ·
          refine ⟨1271877781306469400006155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847918520870979600004103 1271877781306469400006155)
          ·
            refine ⟨1907816671959704100009233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271877781306469400006155 1907816671959704100009233)
            ·
              refine ⟨1430862503969778075006925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907816671959704100009233 1430862503969778075006925)
              ·
                refine ⟨536573438988666778127597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1430862503969778075006925 536573438988666778127597)
                ·
                  refine ⟨201215039620750041797849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536573438988666778127597 201215039620750041797849)
                  ·
                    rfl

theorem cell21_881696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_881696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881696 prefixEnd_881696 := by exact prefixLift 881696
  have htrace : WordTrace (prefixWord ++ tailWord_881696) baseStart_881696 baseEnd_881696 := by
    simpa [prefixWord, tailWord_881696, baseEnd_881696] using wordTrace_append hprefix tailTrace_881696
  have hstable : (prefixWord ++ tailWord_881696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881696).length < 2 ^ (prefixWord ++ tailWord_881696).sum := by decide
  have hdescent : baseEnd_881696 < baseStart_881696 := by decide
  rcases family_descends (prefixWord ++ tailWord_881696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881721 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_881721 : Nat := 118140960795 + 881721 * 2 ^ 59
def prefixEnd_881721 : Nat := 4983230072969 + 3 ^ 40 * 881721 * 2
def baseEnd_881721 : Nat := 201220744961355553881131

theorem tailTrace_881721 : CollatzResearch.WordTrace tailWord_881721 prefixEnd_881721 201220744961355553881131 := by
  unfold tailWord_881721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159006838682877803149017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21439337892455251868766011 32159006838682877803149017)
  ·
    refine ⟨24119255129012158352361763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32159006838682877803149017 24119255129012158352361763)
    ·
      refine ⟨36178882693518237528542645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24119255129012158352361763 36178882693518237528542645)
      ·
        refine ⟨3391770252517334768300873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36178882693518237528542645 3391770252517334768300873)
        ·
          refine ⟨2543827689388001076225655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391770252517334768300873 2543827689388001076225655)
          ·
            refine ⟨3815741534082001614338483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543827689388001076225655 3815741534082001614338483)
            ·
              refine ⟨5723612301123002421507725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815741534082001614338483 5723612301123002421507725)
              ·
                refine ⟨2146354612921125908065397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723612301123002421507725 2146354612921125908065397)
                ·
                  refine ⟨201220744961355553881131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2146354612921125908065397 201220744961355553881131)
                  ·
                    rfl

theorem cell21_881721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_881721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881721 prefixEnd_881721 := by exact prefixLift 881721
  have htrace : WordTrace (prefixWord ++ tailWord_881721) baseStart_881721 baseEnd_881721 := by
    simpa [prefixWord, tailWord_881721, baseEnd_881721] using wordTrace_append hprefix tailTrace_881721
  have hstable : (prefixWord ++ tailWord_881721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881721).length < 2 ^ (prefixWord ++ tailWord_881721).sum := by decide
  have hdescent : baseEnd_881721 < baseStart_881721 := by decide
  rcases family_descends (prefixWord ++ tailWord_881721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881828 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_881828 : Nat := 118140960795 + 881828 * 2 ^ 59
def prefixEnd_881828 : Nat := 4983230072969 + 3 ^ 40 * 881828 * 2
def baseEnd_881828 : Nat := 201245163819147145597579

theorem tailTrace_881828 : CollatzResearch.WordTrace tailWord_881828 prefixEnd_881828 201245163819147145597579 := by
  unfold tailWord_881828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16081454724647617538647069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21441939632863490051529425 16081454724647617538647069)
  ·
    refine ⟨6030545521742856576992651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16081454724647617538647069 6030545521742856576992651)
    ·
      refine ⟨9045818282614284865488977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030545521742856576992651 9045818282614284865488977)
      ·
        refine ⟨6784363711960713649116733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9045818282614284865488977 6784363711960713649116733)
        ·
          refine ⟨2544136391985267618418775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6784363711960713649116733 2544136391985267618418775)
          ·
            refine ⟨3816204587977901427628163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544136391985267618418775 3816204587977901427628163)
            ·
              refine ⟨5724306881966852141442245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816204587977901427628163 5724306881966852141442245)
              ·
                refine ⟨1073307540368784776520421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5724306881966852141442245 1073307540368784776520421)
                ·
                  refine ⟨201245163819147145597579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073307540368784776520421 201245163819147145597579)
                  ·
                    rfl

theorem cell21_881828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_881828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881828 prefixEnd_881828 := by exact prefixLift 881828
  have htrace : WordTrace (prefixWord ++ tailWord_881828) baseStart_881828 baseEnd_881828 := by
    simpa [prefixWord, tailWord_881828, baseEnd_881828] using wordTrace_append hprefix tailTrace_881828
  have hstable : (prefixWord ++ tailWord_881828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881828).length < 2 ^ (prefixWord ++ tailWord_881828).sum := by decide
  have hdescent : baseEnd_881828 < baseStart_881828 := by decide
  rcases family_descends (prefixWord ++ tailWord_881828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881831 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 3]
def baseStart_881831 : Nat := 118140960795 + 881831 * 2 ^ 59
def prefixEnd_881831 : Nat := 4983230072969 + 3 ^ 40 * 881831 * 2
def baseEnd_881831 : Nat := 201245848460019807047573

theorem tailTrace_881831 : CollatzResearch.WordTrace tailWord_881831 prefixEnd_881831 201245848460019807047573 := by
  unfold tailWord_881831
  simp only [CollatzResearch.WordTrace]
  refine ⟨32163018868284366589653347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21442012578856244393102231 32163018868284366589653347)
  ·
    refine ⟨48244528302426549884480021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32163018868284366589653347 48244528302426549884480021)
    ·
      refine ⟨2261462264176244525835001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48244528302426549884480021 2261462264176244525835001)
      ·
        refine ⟨1696096698132183394376251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261462264176244525835001 1696096698132183394376251)
        ·
          refine ⟨2544145047198275091564377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696096698132183394376251 2544145047198275091564377)
          ·
            refine ⟨1908108785398706318673283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544145047198275091564377 1908108785398706318673283)
            ·
              refine ⟨2862163178098059478009925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908108785398706318673283 2862163178098059478009925)
              ·
                refine ⟨536655595893386152126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2862163178098059478009925 536655595893386152126861)
                ·
                  refine ⟨201245848460019807047573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536655595893386152126861 201245848460019807047573)
                  ·
                    rfl

theorem cell21_881831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].length) (baseStart_881831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881831 prefixEnd_881831 := by exact prefixLift 881831
  have htrace : WordTrace (prefixWord ++ tailWord_881831) baseStart_881831 baseEnd_881831 := by
    simpa [prefixWord, tailWord_881831, baseEnd_881831] using wordTrace_append hprefix tailTrace_881831
  have hstable : (prefixWord ++ tailWord_881831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881831).length < 2 ^ (prefixWord ++ tailWord_881831).sum := by decide
  have hdescent : baseEnd_881831 < baseStart_881831 := by decide
  rcases family_descends (prefixWord ++ tailWord_881831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881842 : List Nat := [3, 2, 1, 1, 1, 4, 3, 6]
def baseStart_881842 : Nat := 118140960795 + 881842 * 2 ^ 59
def prefixEnd_881842 : Nat := 4983230072969 + 3 ^ 40 * 881842 * 2
def baseEnd_881842 : Nat := 67082786269962077454739

theorem tailTrace_881842 : CollatzResearch.WordTrace tailWord_881842 prefixEnd_881842 67082786269962077454739 := by
  unfold tailWord_881842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040855017811128867075945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21442280047496343645535853 8040855017811128867075945)
  ·
    refine ⟨6030641263358346650306959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8040855017811128867075945 6030641263358346650306959)
    ·
      refine ⟨9045961895037519975460439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030641263358346650306959 9045961895037519975460439)
      ·
        refine ⟨13568942842556279963190659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045961895037519975460439 13568942842556279963190659)
        ·
          refine ⟨20353414263834419944785989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568942842556279963190659 20353414263834419944785989)
          ·
            refine ⟨3816265174468953739647373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20353414263834419944785989 3816265174468953739647373)
            ·
              refine ⟨1431099440425857652367765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3816265174468953739647373 1431099440425857652367765)
              ·
                refine ⟨67082786269962077454739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1431099440425857652367765 67082786269962077454739)
                ·
                  rfl

theorem cell21_881842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_881842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_881842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_881842 prefixEnd_881842 := by exact prefixLift 881842
  have htrace : WordTrace (prefixWord ++ tailWord_881842) baseStart_881842 baseEnd_881842 := by
    simpa [prefixWord, tailWord_881842, baseEnd_881842] using wordTrace_append hprefix tailTrace_881842
  have hstable : (prefixWord ++ tailWord_881842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881842).length < 2 ^ (prefixWord ++ tailWord_881842).sum := by decide
  have hdescent : baseEnd_881842 < baseStart_881842 := by decide
  rcases family_descends (prefixWord ++ tailWord_881842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882008 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_882008 : Nat := 118140960795 + 882008 * 2 ^ 59
def prefixEnd_882008 : Nat := 4983230072969 + 3 ^ 40 * 882008 * 2
def baseEnd_882008 : Nat := 201286242271506832597211

theorem tailTrace_882008 : CollatzResearch.WordTrace tailWord_882008 prefixEnd_882008 201286242271506832597211 := by
  unfold tailWord_882008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084737294321562909423339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21446316392428750545897785 16084737294321562909423339)
  ·
    refine ⟨24127105941482344364135009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16084737294321562909423339 24127105941482344364135009)
    ·
      refine ⟨18095329456111758273101257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24127105941482344364135009 18095329456111758273101257)
      ·
        refine ⟨13571497092083818704825943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18095329456111758273101257 13571497092083818704825943)
        ·
          refine ⟨20357245638125728057238915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571497092083818704825943 20357245638125728057238915)
          ·
            refine ⟨30535868457188592085858373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357245638125728057238915 30535868457188592085858373)
            ·
              refine ⟨5725475335722861016098445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30535868457188592085858373 5725475335722861016098445)
              ·
                refine ⟨2147053250896072881036917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5725475335722861016098445 2147053250896072881036917)
                ·
                  refine ⟨201286242271506832597211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2147053250896072881036917 201286242271506832597211)
                  ·
                    rfl

theorem cell21_882008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_882008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882008 prefixEnd_882008 := by exact prefixLift 882008
  have htrace : WordTrace (prefixWord ++ tailWord_882008) baseStart_882008 baseEnd_882008 := by
    simpa [prefixWord, tailWord_882008, baseEnd_882008] using wordTrace_append hprefix tailTrace_882008
  have hstable : (prefixWord ++ tailWord_882008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882008).length < 2 ^ (prefixWord ++ tailWord_882008).sum := by decide
  have hdescent : baseEnd_882008 < baseStart_882008 := by decide
  rcases family_descends (prefixWord ++ tailWord_882008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882056 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_882056 : Nat := 118140960795 + 882056 * 2 ^ 59
def prefixEnd_882056 : Nat := 4983230072969 + 3 ^ 40 * 882056 * 2
def baseEnd_882056 : Nat := 201297196525469415797113

theorem tailTrace_882056 : CollatzResearch.WordTrace tailWord_882056 prefixEnd_882056 201297196525469415797113 := by
  unfold tailWord_882056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085612646234615008297011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21447483528312820011062681 16085612646234615008297011)
  ·
    refine ⟨24128418969351922512445517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085612646234615008297011 24128418969351922512445517)
    ·
      refine ⟨9048157113506970942167069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24128418969351922512445517 9048157113506970942167069)
      ·
        refine ⟨3393058917565114103312651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9048157113506970942167069 3393058917565114103312651)
        ·
          refine ⟨5089588376347671154968977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393058917565114103312651 5089588376347671154968977)
          ·
            refine ⟨3817191282260753366226733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089588376347671154968977 3817191282260753366226733)
            ·
              refine ⟨1431446730847782512335025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3817191282260753366226733 1431446730847782512335025)
              ·
                refine ⟨1073585048135836884251269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431446730847782512335025 1073585048135836884251269)
                ·
                  refine ⟨201297196525469415797113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073585048135836884251269 201297196525469415797113)
                  ·
                    rfl

theorem cell21_882056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_882056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882056 prefixEnd_882056 := by exact prefixLift 882056
  have htrace : WordTrace (prefixWord ++ tailWord_882056) baseStart_882056 baseEnd_882056 := by
    simpa [prefixWord, tailWord_882056, baseEnd_882056] using wordTrace_append hprefix tailTrace_882056
  have hstable : (prefixWord ++ tailWord_882056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882056).length < 2 ^ (prefixWord ++ tailWord_882056).sum := by decide
  have hdescent : baseEnd_882056 < baseStart_882056 := by decide
  rcases family_descends (prefixWord ++ tailWord_882056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882180 : List Nat := [2, 3, 2, 3, 3, 1, 1, 6]
def baseStart_882180 : Nat := 118140960795 + 882180 * 2 ^ 59
def prefixEnd_882180 : Nat := 4983230072969 + 3 ^ 40 * 882180 * 2
def baseEnd_882180 : Nat := 67108498338290918576731

theorem tailTrace_882180 : CollatzResearch.WordTrace tailWord_882180 prefixEnd_882180 67108498338290918576731 := by
  unfold tailWord_882180
  simp only [CollatzResearch.WordTrace]
  refine ⟨16087873972009999597053997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21450498629346666129405329 16087873972009999597053997)
  ·
    refine ⟨6032952739503749848895249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16087873972009999597053997 6032952739503749848895249)
    ·
      refine ⟨4524714554627812386671437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6032952739503749848895249 4524714554627812386671437)
      ·
        refine ⟨1696767957985429645001789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4524714554627812386671437 1696767957985429645001789)
        ·
          refine ⟨636287984244536116875671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696767957985429645001789 636287984244536116875671)
          ·
            refine ⟨954431976366804175313507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636287984244536116875671 954431976366804175313507)
            ·
              refine ⟨1431647964550206262970261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954431976366804175313507 1431647964550206262970261)
              ·
                refine ⟨67108498338290918576731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1431647964550206262970261 67108498338290918576731)
                ·
                  rfl

theorem cell21_882180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_882180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882180 prefixEnd_882180 := by exact prefixLift 882180
  have htrace : WordTrace (prefixWord ++ tailWord_882180) baseStart_882180 baseEnd_882180 := by
    simpa [prefixWord, tailWord_882180, baseEnd_882180] using wordTrace_append hprefix tailTrace_882180
  have hstable : (prefixWord ++ tailWord_882180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882180).length < 2 ^ (prefixWord ++ tailWord_882180).sum := by decide
  have hdescent : baseEnd_882180 < baseStart_882180 := by decide
  rcases family_descends (prefixWord ++ tailWord_882180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882222 : List Nat := [4, 1, 3, 1, 2, 2, 8]
def baseStart_882222 : Nat := 118140960795 + 882222 * 2 ^ 59
def prefixEnd_882222 : Nat := 4983230072969 + 3 ^ 40 * 882222 * 2
def baseEnd_882222 : Nat := 22370564443010001781123

theorem tailTrace_882222 : CollatzResearch.WordTrace tailWord_882222 prefixEnd_882222 22370564443010001781123 := by
  unfold tailWord_882222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022159976233480045892115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21451519873245226911424613 4022159976233480045892115)
  ·
    refine ⟨6033239964350220068838173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022159976233480045892115 6033239964350220068838173)
    ·
      refine ⟨2262464986631332525814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6033239964350220068838173 2262464986631332525814315)
      ·
        refine ⟨3393697479946998788721473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262464986631332525814315 3393697479946998788721473)
        ·
          refine ⟨2545273109960249091541105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3393697479946998788721473 2545273109960249091541105)
          ·
            refine ⟨1908954832470186818655829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545273109960249091541105 1908954832470186818655829)
            ·
              refine ⟨22370564443010001781123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1908954832470186818655829 22370564443010001781123)
              ·
                rfl

theorem cell21_882222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 8].length) (baseStart_882222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882222 prefixEnd_882222 := by exact prefixLift 882222
  have htrace : WordTrace (prefixWord ++ tailWord_882222) baseStart_882222 baseEnd_882222 := by
    simpa [prefixWord, tailWord_882222, baseEnd_882222] using wordTrace_append hprefix tailTrace_882222
  have hstable : (prefixWord ++ tailWord_882222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882222).length < 2 ^ (prefixWord ++ tailWord_882222).sum := by decide
  have hdescent : baseEnd_882222 < baseStart_882222 := by decide
  rcases family_descends (prefixWord ++ tailWord_882222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882262 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_882262 : Nat := 118140960795 + 882262 * 2 ^ 59
def prefixEnd_882262 : Nat := 4983230072969 + 3 ^ 40 * 882262 * 2
def baseEnd_882262 : Nat := 201344208532058835363359

theorem tailTrace_882262 : CollatzResearch.WordTrace tailWord_882262 prefixEnd_882262 201344208532058835363359 := by
  unfold tailWord_882262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011171170607682949912065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21452492486481951465728693 2011171170607682949912065)
  ·
    refine ⟨1508378377955762212434049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011171170607682949912065 1508378377955762212434049)
    ·
      refine ⟨1131283783466821659325537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508378377955762212434049 1131283783466821659325537)
      ·
        refine ⟨848462837600116244494153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131283783466821659325537 848462837600116244494153)
        ·
          refine ⟨636347128200087183370615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848462837600116244494153 636347128200087183370615)
          ·
            refine ⟨954520692300130775055923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636347128200087183370615 954520692300130775055923)
            ·
              refine ⟨1431781038450196162583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954520692300130775055923 1431781038450196162583885)
              ·
                refine ⟨536917889418823560968957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431781038450196162583885 536917889418823560968957)
                ·
                  refine ⟨201344208532058835363359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536917889418823560968957 201344208532058835363359)
                  ·
                    rfl

theorem cell21_882262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_882262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882262 prefixEnd_882262 := by exact prefixLift 882262
  have htrace : WordTrace (prefixWord ++ tailWord_882262) baseStart_882262 baseEnd_882262 := by
    simpa [prefixWord, tailWord_882262, baseEnd_882262] using wordTrace_append hprefix tailTrace_882262
  have hstable : (prefixWord ++ tailWord_882262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882262).length < 2 ^ (prefixWord ++ tailWord_882262).sum := by decide
  have hdescent : baseEnd_882262 < baseStart_882262 := by decide
  rcases family_descends (prefixWord ++ tailWord_882262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882301 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 4]
def baseStart_882301 : Nat := 118140960795 + 882301 * 2 ^ 59
def prefixEnd_882301 : Nat := 4983230072969 + 3 ^ 40 * 882301 * 2
def baseEnd_882301 : Nat := 201353108863403434213279

theorem tailTrace_882301 : CollatzResearch.WordTrace tailWord_882301 prefixEnd_882301 201353108863403434213279 := by
  unfold tailWord_882301
  simp only [CollatzResearch.WordTrace]
  refine ⟨32180161176581636859262757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21453440784387757906175171 32180161176581636859262757)
  ·
    refine ⟨6033780220609056911111767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32180161176581636859262757 6033780220609056911111767)
    ·
      refine ⟨9050670330913585366667651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033780220609056911111767 9050670330913585366667651)
      ·
        refine ⟨13576005496370378050001477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050670330913585366667651 13576005496370378050001477)
        ·
          refine ⟨2545501030569445884375277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13576005496370378050001477 2545501030569445884375277)
          ·
            refine ⟨954562886463542206640729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2545501030569445884375277 954562886463542206640729)
            ·
              refine ⟨715922164847656654980547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954562886463542206640729 715922164847656654980547)
              ·
                refine ⟨1073883247271484982470821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715922164847656654980547 1073883247271484982470821)
                ·
                  refine ⟨201353108863403434213279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073883247271484982470821 201353108863403434213279)
                  ·
                    rfl

theorem cell21_882301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_882301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882301 prefixEnd_882301 := by exact prefixLift 882301
  have htrace : WordTrace (prefixWord ++ tailWord_882301) baseStart_882301 baseEnd_882301 := by
    simpa [prefixWord, tailWord_882301, baseEnd_882301] using wordTrace_append hprefix tailTrace_882301
  have hstable : (prefixWord ++ tailWord_882301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882301).length < 2 ^ (prefixWord ++ tailWord_882301).sum := by decide
  have hdescent : baseEnd_882301 < baseStart_882301 := by decide
  rcases family_descends (prefixWord ++ tailWord_882301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882405 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 3]
def baseStart_882405 : Nat := 118140960795 + 882405 * 2 ^ 59
def prefixEnd_882405 : Nat := 4983230072969 + 3 ^ 40 * 882405 * 2
def baseEnd_882405 : Nat := 201376843080322364479733

theorem tailTrace_882405 : CollatzResearch.WordTrace tailWord_882405 prefixEnd_882405 201376843080322364479733 := by
  unfold tailWord_882405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183954368204862621048669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21455969578803241747365779 32183954368204862621048669)
  ·
    refine ⟨12068982888076823482893251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32183954368204862621048669 12068982888076823482893251)
    ·
      refine ⟨18103474332115235224339877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068982888076823482893251 18103474332115235224339877)
      ·
        refine ⟨3394401437271606604563727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18103474332115235224339877 3394401437271606604563727)
        ·
          refine ⟨5091602155907409906845591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394401437271606604563727 5091602155907409906845591)
          ·
            refine ⟨7637403233861114860268387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091602155907409906845591 7637403233861114860268387)
            ·
              refine ⟨11456104850791672290402581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637403233861114860268387 11456104850791672290402581)
              ·
                refine ⟨537004914880859638612621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11456104850791672290402581 537004914880859638612621)
                ·
                  refine ⟨201376843080322364479733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537004914880859638612621 201376843080322364479733)
                  ·
                    rfl

theorem cell21_882405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_882405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882405 prefixEnd_882405 := by exact prefixLift 882405
  have htrace : WordTrace (prefixWord ++ tailWord_882405) baseStart_882405 baseEnd_882405 := by
    simpa [prefixWord, tailWord_882405, baseEnd_882405] using wordTrace_append hprefix tailTrace_882405
  have hstable : (prefixWord ++ tailWord_882405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882405).length < 2 ^ (prefixWord ++ tailWord_882405).sum := by decide
  have hdescent : baseEnd_882405 < baseStart_882405 := by decide
  rcases family_descends (prefixWord ++ tailWord_882405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882439 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 3]
def baseStart_882439 : Nat := 118140960795 + 882439 * 2 ^ 59
def prefixEnd_882439 : Nat := 4983230072969 + 3 ^ 40 * 882439 * 2
def baseEnd_882439 : Nat := 201384602343545860912997

theorem tailTrace_882439 : CollatzResearch.WordTrace tailWord_882439 prefixEnd_882439 201384602343545860912997 := by
  unfold tailWord_882439
  simp only [CollatzResearch.WordTrace]
  refine ⟨32185194450081686427786371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21456796300054457618524247 32185194450081686427786371)
  ·
    refine ⟨48277791675122529641679557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32185194450081686427786371 48277791675122529641679557)
    ·
      refine ⟨9052085939085474307814917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48277791675122529641679557 9052085939085474307814917)
      ·
        refine ⟨1697266113578526432715297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9052085939085474307814917 1697266113578526432715297)
        ·
          refine ⟨1272949585183894824536473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697266113578526432715297 1272949585183894824536473)
          ·
            refine ⟨954712188887921118402355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272949585183894824536473 954712188887921118402355)
            ·
              refine ⟨1432068283331881677603533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954712188887921118402355 1432068283331881677603533)
              ·
                refine ⟨537025606249455629101325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432068283331881677603533 537025606249455629101325)
                ·
                  refine ⟨201384602343545860912997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537025606249455629101325 201384602343545860912997)
                  ·
                    rfl

theorem cell21_882439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].length) (baseStart_882439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882439 prefixEnd_882439 := by exact prefixLift 882439
  have htrace : WordTrace (prefixWord ++ tailWord_882439) baseStart_882439 baseEnd_882439 := by
    simpa [prefixWord, tailWord_882439, baseEnd_882439] using wordTrace_append hprefix tailTrace_882439
  have hstable : (prefixWord ++ tailWord_882439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882439).length < 2 ^ (prefixWord ++ tailWord_882439).sum := by decide
  have hdescent : baseEnd_882439 < baseStart_882439 := by decide
  rcases family_descends (prefixWord ++ tailWord_882439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882450 : List Nat := [3, 2, 4, 1, 1, 1, 9]
def baseStart_882450 : Nat := 118140960795 + 882450 * 2 ^ 59
def prefixEnd_882450 : Nat := 4983230072969 + 3 ^ 40 * 882450 * 2
def baseEnd_882450 : Nat := 22376345854823587358849

theorem tailTrace_882450 : CollatzResearch.WordTrace tailWord_882450 prefixEnd_882450 22376345854823587358849 := by
  unfold tailWord_882450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046398913260458826609201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21457063768694556870957869 8046398913260458826609201)
  ·
    refine ⟨6034799184945344119956901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8046398913260458826609201 6034799184945344119956901)
    ·
      refine ⟨1131524847177252022491919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6034799184945344119956901 1131524847177252022491919)
      ·
        refine ⟨1697287270765878033737879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131524847177252022491919 1697287270765878033737879)
        ·
          refine ⟨2545930906148817050606819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697287270765878033737879 2545930906148817050606819)
          ·
            refine ⟨3818896359223225575910229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545930906148817050606819 3818896359223225575910229)
            ·
              refine ⟨22376345854823587358849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3818896359223225575910229 22376345854823587358849)
              ·
                rfl

theorem cell21_882450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 9].length) (baseStart_882450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882450 prefixEnd_882450 := by exact prefixLift 882450
  have htrace : WordTrace (prefixWord ++ tailWord_882450) baseStart_882450 baseEnd_882450 := by
    simpa [prefixWord, tailWord_882450, baseEnd_882450] using wordTrace_append hprefix tailTrace_882450
  have hstable : (prefixWord ++ tailWord_882450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882450).length < 2 ^ (prefixWord ++ tailWord_882450).sum := by decide
  have hdescent : baseEnd_882450 < baseStart_882450 := by decide
  rcases family_descends (prefixWord ++ tailWord_882450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882540 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_882540 : Nat := 118140960795 + 882540 * 2 ^ 59
def prefixEnd_882540 : Nat := 4983230072969 + 3 ^ 40 * 882540 * 2
def baseEnd_882540 : Nat := 201407651919592129729457

theorem tailTrace_882540 : CollatzResearch.WordTrace tailWord_882540 prefixEnd_882540 201407651919592129729457 := by
  unfold tailWord_882540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094439111357890338606537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21459252148477187118142049 16094439111357890338606537)
  ·
    refine ⟨12070829333518417753954903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16094439111357890338606537 12070829333518417753954903)
    ·
      refine ⟨18106244000277626630932355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12070829333518417753954903 18106244000277626630932355)
      ·
        refine ⟨27159366000416439946398533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18106244000277626630932355 27159366000416439946398533)
        ·
          refine ⟨5092381125078082489949725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27159366000416439946398533 5092381125078082489949725)
          ·
            refine ⟨1909642921904280933731147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5092381125078082489949725 1909642921904280933731147)
            ·
              refine ⟨2864464382856421400596721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909642921904280933731147 2864464382856421400596721)
              ·
                refine ⟨2148348287142316050447541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864464382856421400596721 2148348287142316050447541)
                ·
                  refine ⟨201407651919592129729457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148348287142316050447541 201407651919592129729457)
                  ·
                    rfl

theorem cell21_882540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_882540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882540 prefixEnd_882540 := by exact prefixLift 882540
  have htrace : WordTrace (prefixWord ++ tailWord_882540) baseStart_882540 baseEnd_882540 := by
    simpa [prefixWord, tailWord_882540, baseEnd_882540] using wordTrace_append hprefix tailTrace_882540
  have hstable : (prefixWord ++ tailWord_882540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882540).length < 2 ^ (prefixWord ++ tailWord_882540).sum := by decide
  have hdescent : baseEnd_882540 < baseStart_882540 := by decide
  rcases family_descends (prefixWord ++ tailWord_882540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882574 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_882574 : Nat := 118140960795 + 882574 * 2 ^ 59
def prefixEnd_882574 : Nat := 4983230072969 + 3 ^ 40 * 882574 * 2
def baseEnd_882574 : Nat := 201415411182815626162721

theorem tailTrace_882574 : CollatzResearch.WordTrace tailWord_882574 prefixEnd_882574 201415411182815626162721 := by
  unfold tailWord_882574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023764788074075560493847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21460078869728402989300517 4023764788074075560493847)
  ·
    refine ⟨6035647182111113340740771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023764788074075560493847 6035647182111113340740771)
    ·
      refine ⟨9053470773166670011111157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035647182111113340740771 9053470773166670011111157)
      ·
        refine ⟨848762884984375313541671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9053470773166670011111157 848762884984375313541671)
        ·
          refine ⟨1273144327476562970312507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848762884984375313541671 1273144327476562970312507)
          ·
            refine ⟨1909716491214844455468761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273144327476562970312507 1909716491214844455468761)
            ·
              refine ⟨1432287368411133341601571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909716491214844455468761 1432287368411133341601571)
              ·
                refine ⟨2148431052616700012402357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432287368411133341601571 2148431052616700012402357)
                ·
                  refine ⟨201415411182815626162721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148431052616700012402357 201415411182815626162721)
                  ·
                    rfl

theorem cell21_882574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_882574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882574 prefixEnd_882574 := by exact prefixLift 882574
  have htrace : WordTrace (prefixWord ++ tailWord_882574) baseStart_882574 baseEnd_882574 := by
    simpa [prefixWord, tailWord_882574, baseEnd_882574] using wordTrace_append hprefix tailTrace_882574
  have hstable : (prefixWord ++ tailWord_882574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882574).length < 2 ^ (prefixWord ++ tailWord_882574).sum := by decide
  have hdescent : baseEnd_882574 < baseStart_882574 := by decide
  rcases family_descends (prefixWord ++ tailWord_882574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882678 : List Nat := [5, 1, 1, 1, 5, 8]
def baseStart_882678 : Nat := 118140960795 + 882678 * 2 ^ 59
def prefixEnd_882678 : Nat := 4983230072969 + 3 ^ 40 * 882678 * 2
def baseEnd_882678 : Nat := 7460709088879057645525

theorem tailTrace_882678 : CollatzResearch.WordTrace tailWord_882678 prefixEnd_882678 7460709088879057645525 := by
  unfold tailWord_882678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012119468513489390358543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21462607664143886830491125 2012119468513489390358543)
  ·
    refine ⟨3018179202770234085537815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012119468513489390358543 3018179202770234085537815)
    ·
      refine ⟨4527268804155351128306723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3018179202770234085537815 4527268804155351128306723)
      ·
        refine ⟨6790903206233026692460085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527268804155351128306723 6790903206233026692460085)
        ·
          refine ⟨636647175584346252418133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6790903206233026692460085 636647175584346252418133)
          ·
            refine ⟨7460709088879057645525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 636647175584346252418133 7460709088879057645525)
            ·
              rfl

theorem cell21_882678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 8].length) (baseStart_882678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882678 prefixEnd_882678 := by exact prefixLift 882678
  have htrace : WordTrace (prefixWord ++ tailWord_882678) baseStart_882678 baseEnd_882678 := by
    simpa [prefixWord, tailWord_882678, baseEnd_882678] using wordTrace_append hprefix tailTrace_882678
  have hstable : (prefixWord ++ tailWord_882678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882678).length < 2 ^ (prefixWord ++ tailWord_882678).sum := by decide
  have hdescent : baseEnd_882678 < baseStart_882678 := by decide
  rcases family_descends (prefixWord ++ tailWord_882678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882740 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_882740 : Nat := 118140960795 + 882740 * 2 ^ 59
def prefixEnd_882740 : Nat := 4983230072969 + 3 ^ 40 * 882740 * 2
def baseEnd_882740 : Nat := 201453294644436226395715

theorem tailTrace_882740 : CollatzResearch.WordTrace tailWord_882740 prefixEnd_882740 201453294644436226395715 := by
  unfold tailWord_882740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098086410995607417246837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21464115214660809889662449 16098086410995607417246837)
  ·
    refine ⟨1509195601030838195366891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16098086410995607417246837 1509195601030838195366891)
    ·
      refine ⟨2263793401546257293050337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509195601030838195366891 2263793401546257293050337)
      ·
        refine ⟨1697845051159692969787753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263793401546257293050337 1697845051159692969787753)
        ·
          refine ⟨1273383788369769727340815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697845051159692969787753 1273383788369769727340815)
          ·
            refine ⟨1910075682554654591011223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273383788369769727340815 1910075682554654591011223)
            ·
              refine ⟨2865113523831981886516835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910075682554654591011223 2865113523831981886516835)
              ·
                refine ⟨4297670285747972829775253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865113523831981886516835 4297670285747972829775253)
                ·
                  refine ⟨201453294644436226395715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4297670285747972829775253 201453294644436226395715)
                  ·
                    rfl

theorem cell21_882740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_882740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882740 prefixEnd_882740 := by exact prefixLift 882740
  have htrace : WordTrace (prefixWord ++ tailWord_882740) baseStart_882740 baseEnd_882740 := by
    simpa [prefixWord, tailWord_882740, baseEnd_882740] using wordTrace_append hprefix tailTrace_882740
  have hstable : (prefixWord ++ tailWord_882740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882740).length < 2 ^ (prefixWord ++ tailWord_882740).sum := by decide
  have hdescent : baseEnd_882740 < baseStart_882740 := by decide
  rcases family_descends (prefixWord ++ tailWord_882740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882751 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_882751 : Nat := 118140960795 + 882751 * 2 ^ 59
def prefixEnd_882751 : Nat := 4983230072969 + 3 ^ 40 * 882751 * 2
def baseEnd_882751 : Nat := 201455804994302651712359

theorem tailTrace_882751 : CollatzResearch.WordTrace tailWord_882751 prefixEnd_882751 201455804994302651712359 := by
  unfold tailWord_882751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196574024951363713144107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464382683300909142096071 32196574024951363713144107)
  ·
    refine ⟨48294861037427045569716161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196574024951363713144107 48294861037427045569716161)
    ·
      refine ⟨36221145778070284177287121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48294861037427045569716161 36221145778070284177287121)
      ·
        refine ⟨27165859333552713132965341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36221145778070284177287121 27165859333552713132965341)
        ·
          refine ⟨10187197250082267424862003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27165859333552713132965341 10187197250082267424862003)
          ·
            refine ⟨15280795875123401137293005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187197250082267424862003 15280795875123401137293005)
            ·
              refine ⟨5730298453171275426484877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15280795875123401137293005 5730298453171275426484877)
              ·
                refine ⟨2148861919939228284931829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730298453171275426484877 2148861919939228284931829)
                ·
                  refine ⟨201455804994302651712359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148861919939228284931829 201455804994302651712359)
                  ·
                    rfl

theorem cell21_882751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_882751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882751 prefixEnd_882751 := by exact prefixLift 882751
  have htrace : WordTrace (prefixWord ++ tailWord_882751) baseStart_882751 baseEnd_882751 := by
    simpa [prefixWord, tailWord_882751, baseEnd_882751] using wordTrace_append hprefix tailTrace_882751
  have hstable : (prefixWord ++ tailWord_882751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882751).length < 2 ^ (prefixWord ++ tailWord_882751).sum := by decide
  have hdescent : baseEnd_882751 < baseStart_882751 := by decide
  rcases family_descends (prefixWord ++ tailWord_882751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882796 : List Nat := [2, 2, 1, 1, 3, 3, 9]
def baseStart_882796 : Nat := 118140960795 + 882796 * 2 ^ 59
def prefixEnd_882796 : Nat := 4983230072969 + 3 ^ 40 * 882796 * 2
def baseEnd_882796 : Nat := 22385119400821397051363

theorem tailTrace_882796 : CollatzResearch.WordTrace tailWord_882796 prefixEnd_882796 22385119400821397051363 := by
  unfold tailWord_882796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099107654894168199266121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21465476873192224265688161 16099107654894168199266121)
  ·
    refine ⟨12074330741170626149449591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16099107654894168199266121 12074330741170626149449591)
    ·
      refine ⟨18111496111755939224174387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074330741170626149449591 18111496111755939224174387)
      ·
        refine ⟨27167244167633908836261581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111496111755939224174387 27167244167633908836261581)
        ·
          refine ⟨10187716562862715813598093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27167244167633908836261581 10187716562862715813598093)
          ·
            refine ⟨3820393711073518430099285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10187716562862715813598093 3820393711073518430099285)
            ·
              refine ⟨22385119400821397051363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3820393711073518430099285 22385119400821397051363)
              ·
                rfl

theorem cell21_882796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 9].length) (baseStart_882796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882796 prefixEnd_882796 := by exact prefixLift 882796
  have htrace : WordTrace (prefixWord ++ tailWord_882796) baseStart_882796 baseEnd_882796 := by
    simpa [prefixWord, tailWord_882796, baseEnd_882796] using wordTrace_append hprefix tailTrace_882796
  have hstable : (prefixWord ++ tailWord_882796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882796).length < 2 ^ (prefixWord ++ tailWord_882796).sum := by decide
  have hdescent : baseEnd_882796 < baseStart_882796 := by decide
  rcases family_descends (prefixWord ++ tailWord_882796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882802 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_882802 : Nat := 118140960795 + 882802 * 2 ^ 59
def prefixEnd_882802 : Nat := 4983230072969 + 3 ^ 40 * 882802 * 2
def baseEnd_882802 : Nat := 201467443889137896362255

theorem tailTrace_882802 : CollatzResearch.WordTrace tailWord_882802 prefixEnd_882802 201467443889137896362255 := by
  unfold tailWord_882802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049608536941649855812665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21465622765177732948833773 8049608536941649855812665)
  ·
    refine ⟨6037206402706237391859499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8049608536941649855812665 6037206402706237391859499)
    ·
      refine ⟨9055809604059356087789249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037206402706237391859499 9055809604059356087789249)
      ·
        refine ⟨6791857203044517065841937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9055809604059356087789249 6791857203044517065841937)
        ·
          refine ⟨5093892902283387799381453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791857203044517065841937 5093892902283387799381453)
          ·
            refine ⟨1910209838356270424768045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5093892902283387799381453 1910209838356270424768045)
            ·
              refine ⟨716328689383601409288017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1910209838356270424768045 716328689383601409288017)
              ·
                refine ⟨537246517037701056966013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716328689383601409288017 537246517037701056966013)
                ·
                  refine ⟨201467443889137896362255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537246517037701056966013 201467443889137896362255)
                  ·
                    rfl

theorem cell21_882802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_882802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882802 prefixEnd_882802 := by exact prefixLift 882802
  have htrace : WordTrace (prefixWord ++ tailWord_882802) baseStart_882802 baseEnd_882802 := by
    simpa [prefixWord, tailWord_882802, baseEnd_882802] using wordTrace_append hprefix tailTrace_882802
  have hstable : (prefixWord ++ tailWord_882802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882802).length < 2 ^ (prefixWord ++ tailWord_882802).sum := by decide
  have hdescent : baseEnd_882802 < baseStart_882802 := by decide
  rcases family_descends (prefixWord ++ tailWord_882802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882813 : List Nat := [1, 4, 1, 1, 3, 3, 2, 6]
def baseStart_882813 : Nat := 118140960795 + 882813 * 2 ^ 59
def prefixEnd_882813 : Nat := 4983230072969 + 3 ^ 40 * 882813 * 2
def baseEnd_882813 : Nat := 67156651413001440559633

theorem tailTrace_882813 : CollatzResearch.WordTrace tailWord_882813 prefixEnd_882813 67156651413001440559633 := by
  unfold tailWord_882813
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198835350726748301901093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465890233817832201267395 32198835350726748301901093)
  ·
    refine ⟨6037281628261265306606455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32198835350726748301901093 6037281628261265306606455)
    ·
      refine ⟨9055922442391897959909683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037281628261265306606455 9055922442391897959909683)
      ·
        refine ⟨13583883663587846939864525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055922442391897959909683 13583883663587846939864525)
        ·
          refine ⟨5093956373845442602449197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13583883663587846939864525 5093956373845442602449197)
          ·
            refine ⟨1910233640192040975918449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5093956373845442602449197 1910233640192040975918449)
            ·
              refine ⟨1432675230144030731938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910233640192040975918449 1432675230144030731938837)
              ·
                refine ⟨67156651413001440559633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1432675230144030731938837 67156651413001440559633)
                ·
                  rfl

theorem cell21_882813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_882813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882813 prefixEnd_882813 := by exact prefixLift 882813
  have htrace : WordTrace (prefixWord ++ tailWord_882813) baseStart_882813 baseEnd_882813 := by
    simpa [prefixWord, tailWord_882813, baseEnd_882813] using wordTrace_append hprefix tailTrace_882813
  have hstable : (prefixWord ++ tailWord_882813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882813).length < 2 ^ (prefixWord ++ tailWord_882813).sum := by decide
  have hdescent : baseEnd_882813 < baseStart_882813 := by decide
  rcases family_descends (prefixWord ++ tailWord_882813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882841 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_882841 : Nat := 118140960795 + 882841 * 2 ^ 59
def prefixEnd_882841 : Nat := 4983230072969 + 3 ^ 40 * 882841 * 2
def baseEnd_882841 : Nat := 201476344220482495212175

theorem tailTrace_882841 : CollatzResearch.WordTrace tailWord_882841 prefixEnd_882841 201476344220482495212175 := by
  unfold tailWord_882841
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199856594625309083920377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21466571063083539389280251 32199856594625309083920377)
  ·
    refine ⟨24149892445968981812940283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32199856594625309083920377 24149892445968981812940283)
    ·
      refine ⟨36224838668953472719410425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24149892445968981812940283 36224838668953472719410425)
      ·
        refine ⟨27168629001715104539557819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36224838668953472719410425 27168629001715104539557819)
        ·
          refine ⟨40752943502572656809336729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27168629001715104539557819 40752943502572656809336729)
          ·
            refine ⟨30564707626929492607002547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40752943502572656809336729 30564707626929492607002547)
            ·
              refine ⟨45847061440394238910503821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30564707626929492607002547 45847061440394238910503821)
              ·
                refine ⟨17192648040147839591438933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45847061440394238910503821 17192648040147839591438933)
                ·
                  refine ⟨201476344220482495212175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17192648040147839591438933 201476344220482495212175)
                  ·
                    rfl

theorem cell21_882841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_882841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882841 prefixEnd_882841 := by exact prefixLift 882841
  have htrace : WordTrace (prefixWord ++ tailWord_882841) baseStart_882841 baseEnd_882841 := by
    simpa [prefixWord, tailWord_882841, baseEnd_882841] using wordTrace_append hprefix tailTrace_882841
  have hstable : (prefixWord ++ tailWord_882841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882841).length < 2 ^ (prefixWord ++ tailWord_882841).sum := by decide
  have hdescent : baseEnd_882841 < baseStart_882841 := by decide
  rcases family_descends (prefixWord ++ tailWord_882841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882920 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_882920 : Nat := 118140960795 + 882920 * 2 ^ 59
def prefixEnd_882920 : Nat := 4983230072969 + 3 ^ 40 * 882920 * 2
def baseEnd_882920 : Nat := 201494373096795913395347

theorem tailTrace_882920 : CollatzResearch.WordTrace tailWord_882920 prefixEnd_882920 201494373096795913395347 := by
  unfold tailWord_882920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101368980669552788023107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21468491974226070384030809 16101368980669552788023107)
  ·
    refine ⟨24152053471004329182034661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16101368980669552788023107 24152053471004329182034661)
    ·
      refine ⟨4528510025813311721631499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24152053471004329182034661 4528510025813311721631499)
      ·
        refine ⟨6792765038719967582447249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528510025813311721631499 6792765038719967582447249)
        ·
          refine ⟨5094573779039975686835437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6792765038719967582447249 5094573779039975686835437)
          ·
            refine ⟨1910465167139990882563289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5094573779039975686835437 1910465167139990882563289)
            ·
              refine ⟨1432848875354993161922467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910465167139990882563289 1432848875354993161922467)
              ·
                refine ⟨2149273313032489742883701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432848875354993161922467 2149273313032489742883701)
                ·
                  refine ⟨201494373096795913395347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2149273313032489742883701 201494373096795913395347)
                  ·
                    rfl

theorem cell21_882920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_882920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_882920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_882920 prefixEnd_882920 := by exact prefixLift 882920
  have htrace : WordTrace (prefixWord ++ tailWord_882920) baseStart_882920 baseEnd_882920 := by
    simpa [prefixWord, tailWord_882920, baseEnd_882920] using wordTrace_append hprefix tailTrace_882920
  have hstable : (prefixWord ++ tailWord_882920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882920).length < 2 ^ (prefixWord ++ tailWord_882920).sum := by decide
  have hdescent : baseEnd_882920 < baseStart_882920 := by decide
  rcases family_descends (prefixWord ++ tailWord_882920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883103 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 4]
def baseStart_883103 : Nat := 118140960795 + 883103 * 2 ^ 59
def prefixEnd_883103 : Nat := 4983230072969 + 3 ^ 40 * 883103 * 2
def baseEnd_883103 : Nat := 201536136190028261844973

theorem tailTrace_883103 : CollatzResearch.WordTrace tailWord_883103 prefixEnd_883103 201536136190028261844973 := by
  unfold tailWord_883103
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209412519676127829957963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21472941679784085219971975 32209412519676127829957963)
  ·
    refine ⟨48314118779514191744936945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32209412519676127829957963 48314118779514191744936945)
    ·
      refine ⟨36235589084635643808702709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48314118779514191744936945 36235589084635643808702709)
      ·
        refine ⟨3397086476684591607065879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36235589084635643808702709 3397086476684591607065879)
        ·
          refine ⟨5095629715026887410598819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397086476684591607065879 5095629715026887410598819)
          ·
            refine ⟨7643444572540331115898229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095629715026887410598819 7643444572540331115898229)
            ·
              refine ⟨716572928675656042115459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7643444572540331115898229 716572928675656042115459)
              ·
                refine ⟨1074859393013484063173189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716572928675656042115459 1074859393013484063173189)
                ·
                  refine ⟨201536136190028261844973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074859393013484063173189 201536136190028261844973)
                  ·
                    rfl

theorem cell21_883103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_883103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883103 prefixEnd_883103 := by exact prefixLift 883103
  have htrace : WordTrace (prefixWord ++ tailWord_883103) baseStart_883103 baseEnd_883103 := by
    simpa [prefixWord, tailWord_883103, baseEnd_883103] using wordTrace_append hprefix tailTrace_883103
  have hstable : (prefixWord ++ tailWord_883103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883103).length < 2 ^ (prefixWord ++ tailWord_883103).sum := by decide
  have hdescent : baseEnd_883103 < baseStart_883103 := by decide
  rcases family_descends (prefixWord ++ tailWord_883103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883145 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_883145 : Nat := 118140960795 + 883145 * 2 ^ 59
def prefixEnd_883145 : Nat := 4983230072969 + 3 ^ 40 * 883145 * 2
def baseEnd_883145 : Nat := 201545721162245522144887

theorem tailTrace_883145 : CollatzResearch.WordTrace tailWord_883145 prefixEnd_883145 201545721162245522144887 := by
  unfold tailWord_883145
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210944385523969002986889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21473962923682646001991259 32210944385523969002986889)
  ·
    refine ⟨24158208289142976752240167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32210944385523969002986889 24158208289142976752240167)
    ·
      refine ⟨36237312433714465128360251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24158208289142976752240167 36237312433714465128360251)
      ·
        refine ⟨54355968650571697692540377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36237312433714465128360251 54355968650571697692540377)
        ·
          refine ⟨40766976487928773269405283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54355968650571697692540377 40766976487928773269405283)
          ·
            refine ⟨61150464731893159904107925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40766976487928773269405283 61150464731893159904107925)
            ·
              refine ⟨2866428034307491870505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61150464731893159904107925 2866428034307491870505059)
              ·
                refine ⟨4299642051461237805757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866428034307491870505059 4299642051461237805757589)
                ·
                  refine ⟨201545721162245522144887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4299642051461237805757589 201545721162245522144887)
                  ·
                    rfl

theorem cell21_883145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_883145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883145 prefixEnd_883145 := by exact prefixLift 883145
  have htrace : WordTrace (prefixWord ++ tailWord_883145) baseStart_883145 baseEnd_883145 := by
    simpa [prefixWord, tailWord_883145, baseEnd_883145] using wordTrace_append hprefix tailTrace_883145
  have hstable : (prefixWord ++ tailWord_883145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883145).length < 2 ^ (prefixWord ++ tailWord_883145).sum := by decide
  have hdescent : baseEnd_883145 < baseStart_883145 := by decide
  rcases family_descends (prefixWord ++ tailWord_883145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883154 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_883154 : Nat := 118140960795 + 883154 * 2 ^ 59
def prefixEnd_883154 : Nat := 4983230072969 + 3 ^ 40 * 883154 * 2
def baseEnd_883154 : Nat := 201547775084863506494869

theorem tailTrace_883154 : CollatzResearch.WordTrace tailWord_883154 prefixEnd_883154 201547775084863506494869 := by
  unfold tailWord_883154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052818160622840885016129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21474181761660909026709677 8052818160622840885016129)
  ·
    refine ⟨6039613620467130663762097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8052818160622840885016129 6039613620467130663762097)
    ·
      refine ⟨4529710215350347997821573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6039613620467130663762097 4529710215350347997821573)
      ·
        refine ⟨849320665378190249591545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4529710215350347997821573 849320665378190249591545)
        ·
          refine ⟨636990499033642687193659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849320665378190249591545 636990499033642687193659)
          ·
            refine ⟨955485748550464030790489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636990499033642687193659 955485748550464030790489)
            ·
              refine ⟨716614311412848023092867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955485748550464030790489 716614311412848023092867)
              ·
                refine ⟨1074921467119272034639301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716614311412848023092867 1074921467119272034639301)
                ·
                  refine ⟨201547775084863506494869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074921467119272034639301 201547775084863506494869)
                  ·
                    rfl

theorem cell21_883154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_883154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883154 prefixEnd_883154 := by exact prefixLift 883154
  have htrace : WordTrace (prefixWord ++ tailWord_883154) baseStart_883154 baseEnd_883154 := by
    simpa [prefixWord, tailWord_883154, baseEnd_883154] using wordTrace_append hprefix tailTrace_883154
  have hstable : (prefixWord ++ tailWord_883154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883154).length < 2 ^ (prefixWord ++ tailWord_883154).sum := by decide
  have hdescent : baseEnd_883154 < baseStart_883154 := by decide
  rcases family_descends (prefixWord ++ tailWord_883154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883162 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_883162 : Nat := 118140960795 + 883162 * 2 ^ 59
def prefixEnd_883162 : Nat := 4983230072969 + 3 ^ 40 * 883162 * 2
def baseEnd_883162 : Nat := 201549600793857270361519

theorem tailTrace_883162 : CollatzResearch.WordTrace tailWord_883162 prefixEnd_883162 201549600793857270361519 := by
  unfold tailWord_883162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052891106615595226588935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21474376284308253937570493 8052891106615595226588935)
  ·
    refine ⟨12079336659923392839883403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8052891106615595226588935 12079336659923392839883403)
    ·
      refine ⟨18119004989885089259825105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12079336659923392839883403 18119004989885089259825105)
      ·
        refine ⟨13589253742413816944868829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18119004989885089259825105 13589253742413816944868829)
        ·
          refine ⟨5095970153405181354325811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13589253742413816944868829 5095970153405181354325811)
          ·
            refine ⟨7643955230107772031488717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095970153405181354325811 7643955230107772031488717)
            ·
              refine ⟨2866483211290414511808269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7643955230107772031488717 2866483211290414511808269)
              ·
                refine ⟨1074931204233905441928101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866483211290414511808269 1074931204233905441928101)
                ·
                  refine ⟨201549600793857270361519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074931204233905441928101 201549600793857270361519)
                  ·
                    rfl

theorem cell21_883162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_883162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883162 prefixEnd_883162 := by exact prefixLift 883162
  have htrace : WordTrace (prefixWord ++ tailWord_883162) baseStart_883162 baseEnd_883162 := by
    simpa [prefixWord, tailWord_883162, baseEnd_883162] using wordTrace_append hprefix tailTrace_883162
  have hstable : (prefixWord ++ tailWord_883162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883162).length < 2 ^ (prefixWord ++ tailWord_883162).sum := by decide
  have hdescent : baseEnd_883162 < baseStart_883162 := by decide
  rcases family_descends (prefixWord ++ tailWord_883162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883176 : List Nat := [2, 1, 4, 1, 1, 3, 2, 7]
def baseStart_883176 : Nat := 118140960795 + 883176 * 2 ^ 59
def prefixEnd_883176 : Nat := 4983230072969 + 3 ^ 40 * 883176 * 2
def baseEnd_883176 : Nat := 67184265261532119042719

theorem tailTrace_883176 : CollatzResearch.WordTrace tailWord_883176 prefixEnd_883176 67184265261532119042719 := by
  unfold tailWord_883176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106037524205830648682691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21474716698941107531576921 16106037524205830648682691)
  ·
    refine ⟨24159056286308745973024037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16106037524205830648682691 24159056286308745973024037)
    ·
      refine ⟨4529823053682889869942007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24159056286308745973024037 4529823053682889869942007)
      ·
        refine ⟨6794734580524334804913011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529823053682889869942007 6794734580524334804913011)
        ·
          refine ⟨10192101870786502207369517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794734580524334804913011 10192101870786502207369517)
          ·
            refine ⟨3822038201544938327763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10192101870786502207369517 3822038201544938327763569)
            ·
              refine ⟨2866528651158703745822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822038201544938327763569 2866528651158703745822677)
              ·
                refine ⟨67184265261532119042719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2866528651158703745822677 67184265261532119042719)
                ·
                  rfl

theorem cell21_883176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_883176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883176 prefixEnd_883176 := by exact prefixLift 883176
  have htrace : WordTrace (prefixWord ++ tailWord_883176) baseStart_883176 baseEnd_883176 := by
    simpa [prefixWord, tailWord_883176, baseEnd_883176] using wordTrace_append hprefix tailTrace_883176
  have hstable : (prefixWord ++ tailWord_883176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883176).length < 2 ^ (prefixWord ++ tailWord_883176).sum := by decide
  have hdescent : baseEnd_883176 < baseStart_883176 := by decide
  rcases family_descends (prefixWord ++ tailWord_883176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883297 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_883297 : Nat := 118140960795 + 883297 * 2 ^ 59
def prefixEnd_883297 : Nat := 4983230072969 + 3 ^ 40 * 883297 * 2
def baseEnd_883297 : Nat := 201580409633127035611243

theorem tailTrace_883297 : CollatzResearch.WordTrace tailWord_883297 prefixEnd_883297 201580409633127035611243 := by
  unfold tailWord_883297
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216488280973298962520145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21477658853982199308346763 32216488280973298962520145)
  ·
    refine ⟨24162366210729974221890109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32216488280973298962520145 24162366210729974221890109)
    ·
      refine ⟨9060887329023740333208791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24162366210729974221890109 9060887329023740333208791)
      ·
        refine ⟨13591330993535610499813187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060887329023740333208791 13591330993535610499813187)
        ·
          refine ⟨20386996490303415749719781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591330993535610499813187 20386996490303415749719781)
          ·
            refine ⟨3822561841931890453072459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20386996490303415749719781 3822561841931890453072459)
            ·
              refine ⟨5733842762897835679608689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822561841931890453072459 5733842762897835679608689)
              ·
                refine ⟨4300382072173376759706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733842762897835679608689 4300382072173376759706517)
                ·
                  refine ⟨201580409633127035611243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4300382072173376759706517 201580409633127035611243)
                  ·
                    rfl

theorem cell21_883297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_883297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883297 prefixEnd_883297 := by exact prefixLift 883297
  have htrace : WordTrace (prefixWord ++ tailWord_883297) baseStart_883297 baseEnd_883297 := by
    simpa [prefixWord, tailWord_883297, baseEnd_883297] using wordTrace_append hprefix tailTrace_883297
  have hstable : (prefixWord ++ tailWord_883297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883297).length < 2 ^ (prefixWord ++ tailWord_883297).sum := by decide
  have hdescent : baseEnd_883297 < baseStart_883297 := by decide
  rcases family_descends (prefixWord ++ tailWord_883297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883311 : List Nat := [1, 1, 2, 1, 3, 2, 11]
def baseStart_883311 : Nat := 118140960795 + 883311 * 2 ^ 59
def prefixEnd_883311 : Nat := 4983230072969 + 3 ^ 40 * 883311 * 2
def baseEnd_883311 : Nat := 22398178291540680264209

theorem tailTrace_883311 : CollatzResearch.WordTrace tailWord_883311 prefixEnd_883311 22398178291540680264209 := by
  unfold tailWord_883311
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216998902922579353529787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21477999268615052902353191 32216998902922579353529787)
  ·
    refine ⟨48325498354383869030294681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32216998902922579353529787 48325498354383869030294681)
    ·
      refine ⟨36244123765787901772721011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48325498354383869030294681 36244123765787901772721011)
      ·
        refine ⟨54366185648681852659081517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36244123765787901772721011 54366185648681852659081517)
        ·
          refine ⟨20387319618255694747155569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54366185648681852659081517 20387319618255694747155569)
          ·
            refine ⟨15290489713691771060366677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20387319618255694747155569 15290489713691771060366677)
            ·
              refine ⟨22398178291540680264209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15290489713691771060366677 22398178291540680264209)
              ·
                rfl

theorem cell21_883311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_883311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883311 prefixEnd_883311 := by exact prefixLift 883311
  have htrace : WordTrace (prefixWord ++ tailWord_883311) baseStart_883311 baseEnd_883311 := by
    simpa [prefixWord, tailWord_883311, baseEnd_883311] using wordTrace_append hprefix tailTrace_883311
  have hstable : (prefixWord ++ tailWord_883311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883311).length < 2 ^ (prefixWord ++ tailWord_883311).sum := by decide
  have hdescent : baseEnd_883311 < baseStart_883311 := by decide
  rcases family_descends (prefixWord ++ tailWord_883311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883317 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_883317 : Nat := 118140960795 + 883317 * 2 ^ 59
def prefixEnd_883317 : Nat := 4983230072969 + 3 ^ 40 * 883317 * 2
def baseEnd_883317 : Nat := 201584973905611445277869

theorem tailTrace_883317 : CollatzResearch.WordTrace tailWord_883317 prefixEnd_883317 201584973905611445277869 := by
  unfold tailWord_883317
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217217740900842378248205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21478145160600561585498803 32217217740900842378248205)
  ·
    refine ⟨12081456652837815891843077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32217217740900842378248205 12081456652837815891843077)
    ·
      refine ⟨2265273122407090479720577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12081456652837815891843077 2265273122407090479720577)
      ·
        refine ⟨1698954841805317859790433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2265273122407090479720577 1698954841805317859790433)
        ·
          refine ⟨1274216131353988394842825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698954841805317859790433 1274216131353988394842825)
          ·
            refine ⟨955662098515491296132119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274216131353988394842825 955662098515491296132119)
            ·
              refine ⟨1433493147773236944198179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955662098515491296132119 1433493147773236944198179)
              ·
                refine ⟨2150239721659855416297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433493147773236944198179 2150239721659855416297269)
                ·
                  refine ⟨201584973905611445277869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150239721659855416297269 201584973905611445277869)
                  ·
                    rfl

theorem cell21_883317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_883317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883317 prefixEnd_883317 := by exact prefixLift 883317
  have htrace : WordTrace (prefixWord ++ tailWord_883317) baseStart_883317 baseEnd_883317 := by
    simpa [prefixWord, tailWord_883317, baseEnd_883317] using wordTrace_append hprefix tailTrace_883317
  have hstable : (prefixWord ++ tailWord_883317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883317).length < 2 ^ (prefixWord ++ tailWord_883317).sum := by decide
  have hdescent : baseEnd_883317 < baseStart_883317 := by decide
  rcases family_descends (prefixWord ++ tailWord_883317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883328 : List Nat := [2, 1, 1, 2, 1, 6, 2, 6]
def baseStart_883328 : Nat := 118140960795 + 883328 * 2 ^ 59
def prefixEnd_883328 : Nat := 4983230072969 + 3 ^ 40 * 883328 * 2
def baseEnd_883328 : Nat := 67195828085159290198171

theorem tailTrace_883328 : CollatzResearch.WordTrace tailWord_883328 prefixEnd_883328 67195828085159290198171 := by
  unfold tailWord_883328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108809471930495628449319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21478412629240660837932425 16108809471930495628449319)
  ·
    refine ⟨24163214207895743442673979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16108809471930495628449319 24163214207895743442673979)
    ·
      refine ⟨36244821311843615164010969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24163214207895743442673979 36244821311843615164010969)
      ·
        refine ⟨27183615983882711373008227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36244821311843615164010969 27183615983882711373008227)
        ·
          refine ⟨40775423975824067059512341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27183615983882711373008227 40775423975824067059512341)
          ·
            refine ⟨1911347998866753143414641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40775423975824067059512341 1911347998866753143414641)
            ·
              refine ⟨1433510999150064857560981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911347998866753143414641 1433510999150064857560981)
              ·
                refine ⟨67195828085159290198171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1433510999150064857560981 67195828085159290198171)
                ·
                  rfl

theorem cell21_883328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_883328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883328 prefixEnd_883328 := by exact prefixLift 883328
  have htrace : WordTrace (prefixWord ++ tailWord_883328) baseStart_883328 baseEnd_883328 := by
    simpa [prefixWord, tailWord_883328, baseEnd_883328] using wordTrace_append hprefix tailTrace_883328
  have hstable : (prefixWord ++ tailWord_883328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883328).length < 2 ^ (prefixWord ++ tailWord_883328).sum := by decide
  have hdescent : baseEnd_883328 < baseStart_883328 := by decide
  rcases family_descends (prefixWord ++ tailWord_883328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883390 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_883390 : Nat := 118140960795 + 883390 * 2 ^ 59
def prefixEnd_883390 : Nat := 4983230072969 + 3 ^ 40 * 883390 * 2
def baseEnd_883390 : Nat := 201601633500179540561053

theorem tailTrace_883390 : CollatzResearch.WordTrace tailWord_883390 prefixEnd_883390 201601633500179540561053 := by
  unfold tailWord_883390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027485033704546980706953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21479920179757583897103749 4027485033704546980706953)
  ·
    refine ⟨3020613775278410235530215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4027485033704546980706953 3020613775278410235530215)
    ·
      refine ⟨4530920662917615353295323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020613775278410235530215 4530920662917615353295323)
      ·
        refine ⟨6796380994376423029942985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530920662917615353295323 6796380994376423029942985)
        ·
          refine ⟨5097285745782317272457239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796380994376423029942985 5097285745782317272457239)
          ·
            refine ⟨7645928618673475908685859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097285745782317272457239 7645928618673475908685859)
            ·
              refine ⟨11468892928010213863028789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645928618673475908685859 11468892928010213863028789)
              ·
                refine ⟨1075208712000957549658949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11468892928010213863028789 1075208712000957549658949)
                ·
                  refine ⟨201601633500179540561053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075208712000957549658949 201601633500179540561053)
                  ·
                    rfl

theorem cell21_883390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_883390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883390 prefixEnd_883390 := by exact prefixLift 883390
  have htrace : WordTrace (prefixWord ++ tailWord_883390) baseStart_883390 baseEnd_883390 := by
    simpa [prefixWord, tailWord_883390, baseEnd_883390] using wordTrace_append hprefix tailTrace_883390
  have hstable : (prefixWord ++ tailWord_883390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883390).length < 2 ^ (prefixWord ++ tailWord_883390).sum := by decide
  have hdescent : baseEnd_883390 < baseStart_883390 := by decide
  rcases family_descends (prefixWord ++ tailWord_883390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883393 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_883393 : Nat := 118140960795 + 883393 * 2 ^ 59
def prefixEnd_883393 : Nat := 4983230072969 + 3 ^ 40 * 883393 * 2
def baseEnd_883393 : Nat := 201602318141052202011047

theorem tailTrace_883393 : CollatzResearch.WordTrace tailWord_883393 prefixEnd_883393 201602318141052202011047 := by
  unfold tailWord_883393
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219989688625507358014833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21479993125750338238676555 32219989688625507358014833)
  ·
    refine ⟨24164992266469130518511125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32219989688625507358014833 24164992266469130518511125)
    ·
      refine ⟨1132734012490740493055209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24164992266469130518511125 1132734012490740493055209)
      ·
        refine ⟨849550509368055369791407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132734012490740493055209 849550509368055369791407)
        ·
          refine ⟨1274325764052083054687111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849550509368055369791407 1274325764052083054687111)
          ·
            refine ⟨1911488646078124582030667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274325764052083054687111 1911488646078124582030667)
            ·
              refine ⟨2867232969117186873046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911488646078124582030667 2867232969117186873046001)
              ·
                refine ⟨2150424726837890154784501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867232969117186873046001 2150424726837890154784501)
                ·
                  refine ⟨201602318141052202011047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150424726837890154784501 201602318141052202011047)
                  ·
                    rfl

theorem cell21_883393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_883393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883393 prefixEnd_883393 := by exact prefixLift 883393
  have htrace : WordTrace (prefixWord ++ tailWord_883393) baseStart_883393 baseEnd_883393 := by
    simpa [prefixWord, tailWord_883393, baseEnd_883393] using wordTrace_append hprefix tailTrace_883393
  have hstable : (prefixWord ++ tailWord_883393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883393).length < 2 ^ (prefixWord ++ tailWord_883393).sum := by decide
  have hdescent : baseEnd_883393 < baseStart_883393 := by decide
  rcases family_descends (prefixWord ++ tailWord_883393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883418 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_883418 : Nat := 118140960795 + 883418 * 2 ^ 59
def prefixEnd_883418 : Nat := 4983230072969 + 3 ^ 40 * 883418 * 2
def baseEnd_883418 : Nat := 201608023481657714094329

theorem tailTrace_883418 : CollatzResearch.WordTrace tailWord_883418 prefixEnd_883418 201608023481657714094329 := by
  unfold tailWord_883418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055225378383734156918727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21480601009023291085116605 8055225378383734156918727)
  ·
    refine ⟨12082838067575601235378091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055225378383734156918727 12082838067575601235378091)
    ·
      refine ⟨18124257101363401853067137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12082838067575601235378091 18124257101363401853067137)
      ·
        refine ⟨13593192826022551389800353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18124257101363401853067137 13593192826022551389800353)
        ·
          refine ⟨10194894619516913542350265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13593192826022551389800353 10194894619516913542350265)
          ·
            refine ⟨7646170964637685156762699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10194894619516913542350265 7646170964637685156762699)
            ·
              refine ⟨11469256446956527735144049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646170964637685156762699 11469256446956527735144049)
              ·
                refine ⟨8601942335217395801358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11469256446956527735144049 8601942335217395801358037)
                ·
                  refine ⟨201608023481657714094329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8601942335217395801358037 201608023481657714094329)
                  ·
                    rfl

theorem cell21_883418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_883418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883418 prefixEnd_883418 := by exact prefixLift 883418
  have htrace : WordTrace (prefixWord ++ tailWord_883418) baseStart_883418 baseEnd_883418 := by
    simpa [prefixWord, tailWord_883418, baseEnd_883418] using wordTrace_append hprefix tailTrace_883418
  have hstable : (prefixWord ++ tailWord_883418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883418).length < 2 ^ (prefixWord ++ tailWord_883418).sum := by decide
  have hdescent : baseEnd_883418 < baseStart_883418 := by decide
  rcases family_descends (prefixWord ++ tailWord_883418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883449 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_883449 : Nat := 118140960795 + 883449 * 2 ^ 59
def prefixEnd_883449 : Nat := 4983230072969 + 3 ^ 40 * 883449 * 2
def baseEnd_883449 : Nat := 201615098104008549077599

theorem tailTrace_883449 : CollatzResearch.WordTrace tailWord_883449 prefixEnd_883449 201615098104008549077599 := by
  unfold tailWord_883449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222032176422628922053401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21481354784281752614702267 32222032176422628922053401)
  ·
    refine ⟨24166524132316971691540051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32222032176422628922053401 24166524132316971691540051)
    ·
      refine ⟨36249786198475457537310077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24166524132316971691540051 36249786198475457537310077)
      ·
        refine ⟨13593669824428296576491279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36249786198475457537310077 13593669824428296576491279)
        ·
          refine ⟨20390504736642444864736919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593669824428296576491279 20390504736642444864736919)
          ·
            refine ⟨30585757104963667297105379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20390504736642444864736919 30585757104963667297105379)
            ·
              refine ⟨45878635657445500945658069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30585757104963667297105379 45878635657445500945658069)
              ·
                refine ⟨1075280523221378928413861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45878635657445500945658069 1075280523221378928413861)
                ·
                  refine ⟨201615098104008549077599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075280523221378928413861 201615098104008549077599)
                  ·
                    rfl

theorem cell21_883449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_883449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883449 prefixEnd_883449 := by exact prefixLift 883449
  have htrace : WordTrace (prefixWord ++ tailWord_883449) baseStart_883449 baseEnd_883449 := by
    simpa [prefixWord, tailWord_883449, baseEnd_883449] using wordTrace_append hprefix tailTrace_883449
  have hstable : (prefixWord ++ tailWord_883449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883449).length < 2 ^ (prefixWord ++ tailWord_883449).sum := by decide
  have hdescent : baseEnd_883449 < baseStart_883449 := by decide
  rcases family_descends (prefixWord ++ tailWord_883449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883545 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 3]
def baseStart_883545 : Nat := 118140960795 + 883545 * 2 ^ 59
def prefixEnd_883545 : Nat := 4983230072969 + 3 ^ 40 * 883545 * 2
def baseEnd_883545 : Nat := 201637006611933715477403

theorem tailTrace_883545 : CollatzResearch.WordTrace tailWord_883545 prefixEnd_883545 201637006611933715477403 := by
  unfold tailWord_883545
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225533584074837317548089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21483689056049891545032059 32225533584074837317548089)
  ·
    refine ⟨24169150188056127988161067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32225533584074837317548089 24169150188056127988161067)
    ·
      refine ⟨36253725282084191982241601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24169150188056127988161067 36253725282084191982241601)
      ·
        refine ⟨27190293961563143986681201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36253725282084191982241601 27190293961563143986681201)
        ·
          refine ⟨20392720471172357990010901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27190293961563143986681201 20392720471172357990010901)
          ·
            refine ⟨955908772086204280781761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20392720471172357990010901 955908772086204280781761)
            ·
              refine ⟨716931579064653210586321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955908772086204280781761 716931579064653210586321)
              ·
                refine ⟨537698684298489907939741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716931579064653210586321 537698684298489907939741)
                ·
                  refine ⟨201637006611933715477403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537698684298489907939741 201637006611933715477403)
                  ·
                    rfl

theorem cell21_883545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_883545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883545 prefixEnd_883545 := by exact prefixLift 883545
  have htrace : WordTrace (prefixWord ++ tailWord_883545) baseStart_883545 baseEnd_883545 := by
    simpa [prefixWord, tailWord_883545, baseEnd_883545] using wordTrace_append hprefix tailTrace_883545
  have hstable : (prefixWord ++ tailWord_883545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883545).length < 2 ^ (prefixWord ++ tailWord_883545).sum := by decide
  have hdescent : baseEnd_883545 < baseStart_883545 := by decide
  rcases family_descends (prefixWord ++ tailWord_883545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883556 : List Nat := [2, 3, 1, 1, 4, 1, 3, 6]
def baseStart_883556 : Nat := 118140960795 + 883556 * 2 ^ 59
def prefixEnd_883556 : Nat := 4983230072969 + 3 ^ 40 * 883556 * 2
def baseEnd_883556 : Nat := 67213172320600046931349

theorem tailTrace_883556 : CollatzResearch.WordTrace tailWord_883556 prefixEnd_883556 67213172320600046931349 := by
  unfold tailWord_883556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112967393517493098099261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21483956524689990797465681 16112967393517493098099261)
  ·
    refine ⟨6042362772569059911787223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16112967393517493098099261 6042362772569059911787223)
    ·
      refine ⟨9063544158853589867680835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042362772569059911787223 9063544158853589867680835)
      ·
        refine ⟨13595316238280384801521253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063544158853589867680835 13595316238280384801521253)
        ·
          refine ⟨2549121794677572150285235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13595316238280384801521253 2549121794677572150285235)
          ·
            refine ⟨3823682692016358225427853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549121794677572150285235 3823682692016358225427853)
            ·
              refine ⟨1433881009506134334535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3823682692016358225427853 1433881009506134334535445)
              ·
                refine ⟨67213172320600046931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1433881009506134334535445 67213172320600046931349)
                ·
                  rfl

theorem cell21_883556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_883556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883556 prefixEnd_883556 := by exact prefixLift 883556
  have htrace : WordTrace (prefixWord ++ tailWord_883556) baseStart_883556 baseEnd_883556 := by
    simpa [prefixWord, tailWord_883556, baseEnd_883556] using wordTrace_append hprefix tailTrace_883556
  have hstable : (prefixWord ++ tailWord_883556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883556).length < 2 ^ (prefixWord ++ tailWord_883556).sum := by decide
  have hdescent : baseEnd_883556 < baseStart_883556 := by decide
  rcases family_descends (prefixWord ++ tailWord_883556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883570 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_883570 : Nat := 118140960795 + 883570 * 2 ^ 59
def prefixEnd_883570 : Nat := 4983230072969 + 3 ^ 40 * 883570 * 2
def baseEnd_883570 : Nat := 201642711952539227560685

theorem tailTrace_883570 : CollatzResearch.WordTrace tailWord_883570 prefixEnd_883570 201642711952539227560685 := by
  unfold tailWord_883570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056611352246066646802041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21484296939322844391472109 8056611352246066646802041)
  ·
    refine ⟨6042458514184549985101531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8056611352246066646802041 6042458514184549985101531)
    ·
      refine ⟨9063687771276824977652297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042458514184549985101531 9063687771276824977652297)
      ·
        refine ⟨6797765828457618733239223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063687771276824977652297 6797765828457618733239223)
        ·
          refine ⟨10196648742686428099858835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797765828457618733239223 10196648742686428099858835)
          ·
            refine ⟨15294973114029642149788253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196648742686428099858835 15294973114029642149788253)
            ·
              refine ⟨5735614917761115806170595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15294973114029642149788253 5735614917761115806170595)
              ·
                refine ⟨8603422376641673709255893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735614917761115806170595 8603422376641673709255893)
                ·
                  refine ⟨201642711952539227560685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8603422376641673709255893 201642711952539227560685)
                  ·
                    rfl

theorem cell21_883570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_883570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883570 prefixEnd_883570 := by exact prefixLift 883570
  have htrace : WordTrace (prefixWord ++ tailWord_883570) baseStart_883570 baseEnd_883570 := by
    simpa [prefixWord, tailWord_883570, baseEnd_883570] using wordTrace_append hprefix tailTrace_883570
  have hstable : (prefixWord ++ tailWord_883570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883570).length < 2 ^ (prefixWord ++ tailWord_883570).sum := by decide
  have hdescent : baseEnd_883570 < baseStart_883570 := by decide
  rcases family_descends (prefixWord ++ tailWord_883570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883573 : List Nat := [1, 3, 4, 1, 1, 3, 3, 5]
def baseStart_883573 : Nat := 118140960795 + 883573 * 2 ^ 59
def prefixEnd_883573 : Nat := 4983230072969 + 3 ^ 40 * 883573 * 2
def baseEnd_883573 : Nat := 67214465531137296336893

theorem tailTrace_883573 : CollatzResearch.WordTrace tailWord_883573 prefixEnd_883573 67214465531137296336893 := by
  unfold tailWord_883573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226554827973398099567373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21484369885315598733044915 32226554827973398099567373)
  ·
    refine ⟨12084958060490024287337765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32226554827973398099567373 12084958060490024287337765)
    ·
      refine ⟨2265929636341879553875831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12084958060490024287337765 2265929636341879553875831)
      ·
        refine ⟨3398894454512819330813747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265929636341879553875831 3398894454512819330813747)
        ·
          refine ⟨5098341681769228996220621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398894454512819330813747 5098341681769228996220621)
          ·
            refine ⟨1911878130663460873582733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5098341681769228996220621 1911878130663460873582733)
            ·
              refine ⟨716954298998797827593525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911878130663460873582733 716954298998797827593525)
              ·
                refine ⟨67214465531137296336893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 716954298998797827593525 67214465531137296336893)
                ·
                  rfl

theorem cell21_883573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].length) (baseStart_883573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883573 prefixEnd_883573 := by exact prefixLift 883573
  have htrace : WordTrace (prefixWord ++ tailWord_883573) baseStart_883573 baseEnd_883573 := by
    simpa [prefixWord, tailWord_883573, baseEnd_883573] using wordTrace_append hprefix tailTrace_883573
  have hstable : (prefixWord ++ tailWord_883573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883573).length < 2 ^ (prefixWord ++ tailWord_883573).sum := by decide
  have hdescent : baseEnd_883573 < baseStart_883573 := by decide
  rcases family_descends (prefixWord ++ tailWord_883573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883604 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_883604 : Nat := 118140960795 + 883604 * 2 ^ 59
def prefixEnd_883604 : Nat := 4983230072969 + 3 ^ 40 * 883604 * 2
def baseEnd_883604 : Nat := 201650471215762723993949

theorem tailTrace_883604 : CollatzResearch.WordTrace tailWord_883604 prefixEnd_883604 201650471215762723993949 := by
  unfold tailWord_883604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113842745430545196972933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21485123660574060262630577 16113842745430545196972933)
  ·
    refine ⟨3021345514768227224432425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16113842745430545196972933 3021345514768227224432425)
    ·
      refine ⟨2266009136076170418324319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3021345514768227224432425 2266009136076170418324319)
      ·
        refine ⟨3399013704114255627486479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266009136076170418324319 3399013704114255627486479)
        ·
          refine ⟨5098520556171383441229719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399013704114255627486479 5098520556171383441229719)
          ·
            refine ⟨7647780834257075161844579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098520556171383441229719 7647780834257075161844579)
            ·
              refine ⟨11471671251385612742766869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647780834257075161844579 11471671251385612742766869)
              ·
                refine ⟨537734589908700597317197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11471671251385612742766869 537734589908700597317197)
                ·
                  refine ⟨201650471215762723993949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537734589908700597317197 201650471215762723993949)
                  ·
                    rfl

theorem cell21_883604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_883604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883604 prefixEnd_883604 := by exact prefixLift 883604
  have htrace : WordTrace (prefixWord ++ tailWord_883604) baseStart_883604 baseEnd_883604 := by
    simpa [prefixWord, tailWord_883604, baseEnd_883604] using wordTrace_append hprefix tailTrace_883604
  have hstable : (prefixWord ++ tailWord_883604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883604).length < 2 ^ (prefixWord ++ tailWord_883604).sum := by decide
  have hdescent : baseEnd_883604 < baseStart_883604 := by decide
  rcases family_descends (prefixWord ++ tailWord_883604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883663 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_883663 : Nat := 118140960795 + 883663 * 2 ^ 59
def prefixEnd_883663 : Nat := 4983230072969 + 3 ^ 40 * 883663 * 2
def baseEnd_883663 : Nat := 201663935819591732510495

theorem tailTrace_883663 : CollatzResearch.WordTrace tailWord_883663 prefixEnd_883663 201663935819591732510495 := by
  unfold tailWord_883663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32229837397647343470343643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21486558265098228980229095 32229837397647343470343643)
  ·
    refine ⟨48344756096471015205515465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32229837397647343470343643 48344756096471015205515465)
    ·
      refine ⟨36258567072353261404136599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48344756096471015205515465 36258567072353261404136599)
      ·
        refine ⟨54387850608529892106204899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36258567072353261404136599 54387850608529892106204899)
        ·
          refine ⟨81581775912794838159307349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54387850608529892106204899 81581775912794838159307349)
          ·
            refine ⟨956036436478064509679383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 81581775912794838159307349 956036436478064509679383)
            ·
              refine ⟨1434054654717096764519075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956036436478064509679383 1434054654717096764519075)
              ·
                refine ⟨2151081982075645146778613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434054654717096764519075 2151081982075645146778613)
                ·
                  refine ⟨201663935819591732510495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2151081982075645146778613 201663935819591732510495)
                  ·
                    rfl

theorem cell21_883663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_883663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883663 prefixEnd_883663 := by exact prefixLift 883663
  have htrace : WordTrace (prefixWord ++ tailWord_883663) baseStart_883663 baseEnd_883663 := by
    simpa [prefixWord, tailWord_883663, baseEnd_883663] using wordTrace_append hprefix tailTrace_883663
  have hstable : (prefixWord ++ tailWord_883663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883663).length < 2 ^ (prefixWord ++ tailWord_883663).sum := by decide
  have hdescent : baseEnd_883663 < baseStart_883663 := by decide
  rcases family_descends (prefixWord ++ tailWord_883663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883714 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_883714 : Nat := 118140960795 + 883714 * 2 ^ 59
def prefixEnd_883714 : Nat := 4983230072969 + 3 ^ 40 * 883714 * 2
def baseEnd_883714 : Nat := 201675574714426977160391

theorem tailTrace_883714 : CollatzResearch.WordTrace tailWord_883714 prefixEnd_883714 201675574714426977160391 := by
  unfold tailWord_883714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057924380115644795112549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21487798346975052786966797 8057924380115644795112549)
  ·
    refine ⟨1510860821271683399083603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8057924380115644795112549 1510860821271683399083603)
    ·
      refine ⟨2266291231907525098625405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510860821271683399083603 2266291231907525098625405)
      ·
        refine ⟨849859211965321911984527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2266291231907525098625405 849859211965321911984527)
        ·
          refine ⟨1274788817947982867976791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849859211965321911984527 1274788817947982867976791)
          ·
            refine ⟨1912183226921974301965187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274788817947982867976791 1912183226921974301965187)
            ·
              refine ⟨2868274840382961452947781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912183226921974301965187 2868274840382961452947781)
              ·
                refine ⟨537801532571805272427709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2868274840382961452947781 537801532571805272427709)
                ·
                  refine ⟨201675574714426977160391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537801532571805272427709 201675574714426977160391)
                  ·
                    rfl

theorem cell21_883714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_883714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883714 prefixEnd_883714 := by exact prefixLift 883714
  have htrace : WordTrace (prefixWord ++ tailWord_883714) baseStart_883714 baseEnd_883714 := by
    simpa [prefixWord, tailWord_883714, baseEnd_883714] using wordTrace_append hprefix tailTrace_883714
  have hstable : (prefixWord ++ tailWord_883714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883714).length < 2 ^ (prefixWord ++ tailWord_883714).sum := by decide
  have hdescent : baseEnd_883714 < baseStart_883714 := by decide
  rcases family_descends (prefixWord ++ tailWord_883714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883838 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_883838 : Nat := 118140960795 + 883838 * 2 ^ 59
def prefixEnd_883838 : Nat := 4983230072969 + 3 ^ 40 * 883838 * 2
def baseEnd_883838 : Nat := 201703873203830317093471

theorem tailTrace_883838 : CollatzResearch.WordTrace tailWord_883838 prefixEnd_883838 201703873203830317093471 := by
  unfold tailWord_883838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029527521501668544745521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21490813448008898905309445 4029527521501668544745521)
  ·
    refine ⟨3022145641126251408559141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4029527521501668544745521 3022145641126251408559141)
    ·
      refine ⟨566652307711172139104839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3022145641126251408559141 566652307711172139104839)
      ·
        refine ⟨849978461566758208657259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566652307711172139104839 849978461566758208657259)
        ·
          refine ⟨1274967692350137312985889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849978461566758208657259 1274967692350137312985889)
          ·
            refine ⟨956225769262602984739417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274967692350137312985889 956225769262602984739417)
            ·
              refine ⟨717169326946952238554563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956225769262602984739417 717169326946952238554563)
              ·
                refine ⟨1075753990420428357831845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717169326946952238554563 1075753990420428357831845)
                ·
                  refine ⟨201703873203830317093471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075753990420428357831845 201703873203830317093471)
                  ·
                    rfl

theorem cell21_883838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_883838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883838 prefixEnd_883838 := by exact prefixLift 883838
  have htrace : WordTrace (prefixWord ++ tailWord_883838) baseStart_883838 baseEnd_883838 := by
    simpa [prefixWord, tailWord_883838, baseEnd_883838] using wordTrace_append hprefix tailTrace_883838
  have hstable : (prefixWord ++ tailWord_883838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883838).length < 2 ^ (prefixWord ++ tailWord_883838).sum := by decide
  have hdescent : baseEnd_883838 < baseStart_883838 := by decide
  rcases family_descends (prefixWord ++ tailWord_883838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883843 : List Nat := [1, 1, 1, 3, 3, 2, 4, 6]
def baseStart_883843 : Nat := 118140960795 + 883843 * 2 ^ 59
def prefixEnd_883843 : Nat := 4983230072969 + 3 ^ 40 * 883843 * 2
def baseEnd_883843 : Nat := 67235004757317139836709

theorem tailTrace_883843 : CollatzResearch.WordTrace tailWord_883843 prefixEnd_883843 67235004757317139836709 := by
  unfold tailWord_883843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236402536995234211896183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21490935024663489474597455 32236402536995234211896183)
  ·
    refine ⟨48354603805492851317844275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32236402536995234211896183 48354603805492851317844275)
    ·
      refine ⟨72531905708239276976766413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48354603805492851317844275 72531905708239276976766413)
      ·
        refine ⟨27199464640589728866287405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72531905708239276976766413 27199464640589728866287405)
        ·
          refine ⟨10199799240221148324857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27199464640589728866287405 10199799240221148324857777)
          ·
            refine ⟨7649849430165861243643333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199799240221148324857777 7649849430165861243643333)
            ·
              refine ⟨1434346768156098983183125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7649849430165861243643333 1434346768156098983183125)
              ·
                refine ⟨67235004757317139836709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1434346768156098983183125 67235004757317139836709)
                ·
                  rfl

theorem cell21_883843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_883843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883843 prefixEnd_883843 := by exact prefixLift 883843
  have htrace : WordTrace (prefixWord ++ tailWord_883843) baseStart_883843 baseEnd_883843 := by
    simpa [prefixWord, tailWord_883843, baseEnd_883843] using wordTrace_append hprefix tailTrace_883843
  have hstable : (prefixWord ++ tailWord_883843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883843).length < 2 ^ (prefixWord ++ tailWord_883843).sum := by decide
  have hdescent : baseEnd_883843 < baseStart_883843 := by decide
  rcases family_descends (prefixWord ++ tailWord_883843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883950 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_883950 : Nat := 118140960795 + 883950 * 2 ^ 59
def prefixEnd_883950 : Nat := 4983230072969 + 3 ^ 40 * 883950 * 2
def baseEnd_883950 : Nat := 201729433129743011226575

theorem tailTrace_883950 : CollatzResearch.WordTrace tailWord_883950 prefixEnd_883950 201729433129743011226575 := by
  unfold tailWord_883950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030038143450948935755163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21493536765071727657360869 4030038143450948935755163)
  ·
    refine ⟨6045057215176423403632745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030038143450948935755163 6045057215176423403632745)
    ·
      refine ⟨4533792911382317552724559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6045057215176423403632745 4533792911382317552724559)
      ·
        refine ⟨6800689367073476329086839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533792911382317552724559 6800689367073476329086839)
        ·
          refine ⟨10201034050610214493630259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800689367073476329086839 10201034050610214493630259)
          ·
            refine ⟨15301551075915321740445389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201034050610214493630259 15301551075915321740445389)
            ·
              refine ⟨5738081653468245652667021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15301551075915321740445389 5738081653468245652667021)
              ·
                refine ⟨2151780620050592119750133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5738081653468245652667021 2151780620050592119750133)
                ·
                  refine ⟨201729433129743011226575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2151780620050592119750133 201729433129743011226575)
                  ·
                    rfl

theorem cell21_883950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_883950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883950 prefixEnd_883950 := by exact prefixLift 883950
  have htrace : WordTrace (prefixWord ++ tailWord_883950) baseStart_883950 baseEnd_883950 := by
    simpa [prefixWord, tailWord_883950, baseEnd_883950] using wordTrace_append hprefix tailTrace_883950
  have hstable : (prefixWord ++ tailWord_883950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883950).length < 2 ^ (prefixWord ++ tailWord_883950).sum := by decide
  have hdescent : baseEnd_883950 < baseStart_883950 := by decide
  rcases family_descends (prefixWord ++ tailWord_883950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883970 : List Nat := [3, 4, 1, 1, 3, 2, 2, 5]
def baseStart_883970 : Nat := 118140960795 + 883970 * 2 ^ 59
def prefixEnd_883970 : Nat := 4983230072969 + 3 ^ 40 * 883970 * 2
def baseEnd_883970 : Nat := 67244665800742473631067

theorem tailTrace_883970 : CollatzResearch.WordTrace tailWord_883970 prefixEnd_883970 67244665800742473631067 := by
  unfold tailWord_883970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060258651883783725442341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21494023071690089934512909 8060258651883783725442341)
  ·
    refine ⟨1511298497228209448520439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8060258651883783725442341 1511298497228209448520439)
    ·
      refine ⟨2266947745842314172780659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511298497228209448520439 2266947745842314172780659)
      ·
        refine ⟨3400421618763471259170989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266947745842314172780659 3400421618763471259170989)
        ·
          refine ⟨1275158107036301722189121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400421618763471259170989 1275158107036301722189121)
          ·
            refine ⟨956368580277226291641841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275158107036301722189121 956368580277226291641841)
            ·
              refine ⟨717276435207919718731381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956368580277226291641841 717276435207919718731381)
              ·
                refine ⟨67244665800742473631067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717276435207919718731381 67244665800742473631067)
                ·
                  rfl

theorem cell21_883970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_883970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_883970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_883970 prefixEnd_883970 := by exact prefixLift 883970
  have htrace : WordTrace (prefixWord ++ tailWord_883970) baseStart_883970 baseEnd_883970 := by
    simpa [prefixWord, tailWord_883970, baseEnd_883970] using wordTrace_append hprefix tailTrace_883970
  have hstable : (prefixWord ++ tailWord_883970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883970).length < 2 ^ (prefixWord ++ tailWord_883970).sum := by decide
  have hdescent : baseEnd_883970 < baseStart_883970 := by decide
  rcases family_descends (prefixWord ++ tailWord_883970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884094 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_884094 : Nat := 118140960795 + 884094 * 2 ^ 59
def prefixEnd_884094 : Nat := 4983230072969 + 3 ^ 40 * 884094 * 2
def baseEnd_884094 : Nat := 201762295891630760826281

theorem tailTrace_884094 : CollatzResearch.WordTrace tailWord_884094 prefixEnd_884094 201762295891630760826281 := by
  unfold tailWord_884094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030694657385738009910417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21497038172723936052855557 4030694657385738009910417)
  ·
    refine ⟨3023020993039303507432813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4030694657385738009910417 3023020993039303507432813)
    ·
      refine ⟨1133632872389738815287305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3023020993039303507432813 1133632872389738815287305)
      ·
        refine ⟨850224654292304111465479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133632872389738815287305 850224654292304111465479)
        ·
          refine ⟨1275336981438456167198219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850224654292304111465479 1275336981438456167198219)
          ·
            refine ⟨1913005472157684250797329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275336981438456167198219 1913005472157684250797329)
            ·
              refine ⟨1434754104118263188097997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913005472157684250797329 1434754104118263188097997)
              ·
                refine ⟨538032789044348695536749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434754104118263188097997 538032789044348695536749)
                ·
                  refine ⟨201762295891630760826281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538032789044348695536749 201762295891630760826281)
                  ·
                    rfl

theorem cell21_884094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_884094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884094 prefixEnd_884094 := by exact prefixLift 884094
  have htrace : WordTrace (prefixWord ++ tailWord_884094) baseStart_884094 baseEnd_884094 := by
    simpa [prefixWord, tailWord_884094, baseEnd_884094] using wordTrace_append hprefix tailTrace_884094
  have hstable : (prefixWord ++ tailWord_884094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884094).length < 2 ^ (prefixWord ++ tailWord_884094).sum := by decide
  have hdescent : baseEnd_884094 < baseStart_884094 := by decide
  rcases family_descends (prefixWord ++ tailWord_884094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884153 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 3]
def baseStart_884153 : Nat := 118140960795 + 884153 * 2 ^ 59
def prefixEnd_884153 : Nat := 4983230072969 + 3 ^ 40 * 884153 * 2
def baseEnd_884153 : Nat := 201775760495459769342827

theorem tailTrace_884153 : CollatzResearch.WordTrace tailWord_884153 prefixEnd_884153 201775760495459769342827 := by
  unfold tailWord_884153
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247709165872157155681113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21498472777248104770454075 32247709165872157155681113)
  ·
    refine ⟨24185781874404117866760835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32247709165872157155681113 24185781874404117866760835)
    ·
      refine ⟨36278672811606176800141253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24185781874404117866760835 36278672811606176800141253)
      ·
        refine ⟨6802251152176158150026485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36278672811606176800141253 6802251152176158150026485)
        ·
          refine ⟨637711045516514826564983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6802251152176158150026485 637711045516514826564983)
          ·
            refine ⟨956566568274772239847475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637711045516514826564983 956566568274772239847475)
            ·
              refine ⟨1434849852412158359771213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956566568274772239847475 1434849852412158359771213)
              ·
                refine ⟨538068694654559384914205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434849852412158359771213 538068694654559384914205)
                ·
                  refine ⟨201775760495459769342827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538068694654559384914205 201775760495459769342827)
                  ·
                    rfl

theorem cell21_884153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_884153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884153 prefixEnd_884153 := by exact prefixLift 884153
  have htrace : WordTrace (prefixWord ++ tailWord_884153) baseStart_884153 baseEnd_884153 := by
    simpa [prefixWord, tailWord_884153, baseEnd_884153] using wordTrace_append hprefix tailTrace_884153
  have hstable : (prefixWord ++ tailWord_884153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884153).length < 2 ^ (prefixWord ++ tailWord_884153).sum := by decide
  have hdescent : baseEnd_884153 < baseStart_884153 := by decide
  rcases family_descends (prefixWord ++ tailWord_884153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884164 : List Nat := [2, 3, 3, 2, 1, 3, 7]
def baseStart_884164 : Nat := 118140960795 + 884164 * 2 ^ 59
def prefixEnd_884164 : Nat := 4983230072969 + 3 ^ 40 * 884164 * 2
def baseEnd_884164 : Nat := 22419807871702910517719

theorem tailTrace_884164 : CollatzResearch.WordTrace tailWord_884164 prefixEnd_884164 22419807871702910517719 := by
  unfold tailWord_884164
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124055184416153017165773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21498740245888204022887697 16124055184416153017165773)
  ·
    refine ⟨6046520694156057381437165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16124055184416153017165773 6046520694156057381437165)
    ·
      refine ⟨2267445260308521518038937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6046520694156057381437165 2267445260308521518038937)
      ·
        refine ⟨1700583945231391138529203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267445260308521518038937 1700583945231391138529203)
        ·
          refine ⟨2550875917847086707793805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700583945231391138529203 2550875917847086707793805)
          ·
            refine ⟨956578469192657515422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2550875917847086707793805 956578469192657515422677)
            ·
              refine ⟨22419807871702910517719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 956578469192657515422677 22419807871702910517719)
              ·
                rfl

theorem cell21_884164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 7].length) (baseStart_884164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884164 prefixEnd_884164 := by exact prefixLift 884164
  have htrace : WordTrace (prefixWord ++ tailWord_884164) baseStart_884164 baseEnd_884164 := by
    simpa [prefixWord, tailWord_884164, baseEnd_884164] using wordTrace_append hprefix tailTrace_884164
  have hstable : (prefixWord ++ tailWord_884164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884164).length < 2 ^ (prefixWord ++ tailWord_884164).sum := by decide
  have hdescent : baseEnd_884164 < baseStart_884164 := by decide
  rcases family_descends (prefixWord ++ tailWord_884164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884226 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_884226 : Nat := 118140960795 + 884226 * 2 ^ 59
def prefixEnd_884226 : Nat := 4983230072969 + 3 ^ 40 * 884226 * 2
def baseEnd_884226 : Nat := 201792420090027864626011

theorem tailTrace_884226 : CollatzResearch.WordTrace tailWord_884226 prefixEnd_884226 201792420090027864626011 := by
  unfold tailWord_884226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062592923651922655772133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21500247796405127082059021 8062592923651922655772133)
  ·
    refine ⟨1511736173184735497957275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8062592923651922655772133 1511736173184735497957275)
    ·
      refine ⟨2267604259777103246935913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511736173184735497957275 2267604259777103246935913)
      ·
        refine ⟨1700703194832827435201935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267604259777103246935913 1700703194832827435201935)
        ·
          refine ⟨2551054792249241152802903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700703194832827435201935 2551054792249241152802903)
          ·
            refine ⟨3826582188373861729204355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551054792249241152802903 3826582188373861729204355)
            ·
              refine ⟨5739873282560792593806533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826582188373861729204355 5739873282560792593806533)
              ·
                refine ⟨1076226240480148611338725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5739873282560792593806533 1076226240480148611338725)
                ·
                  refine ⟨201792420090027864626011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076226240480148611338725 201792420090027864626011)
                  ·
                    rfl

theorem cell21_884226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_884226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884226 prefixEnd_884226 := by exact prefixLift 884226
  have htrace : WordTrace (prefixWord ++ tailWord_884226) baseStart_884226 baseEnd_884226 := by
    simpa [prefixWord, tailWord_884226, baseEnd_884226] using wordTrace_append hprefix tailTrace_884226
  have hstable : (prefixWord ++ tailWord_884226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884226).length < 2 ^ (prefixWord ++ tailWord_884226).sum := by decide
  have hdescent : baseEnd_884226 < baseStart_884226 := by decide
  rcases family_descends (prefixWord ++ tailWord_884226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884282 : List Nat := [3, 1, 1, 1, 3, 2, 10]
def baseStart_884282 : Nat := 118140960795 + 884282 * 2 ^ 59
def prefixEnd_884282 : Nat := 4983230072969 + 3 ^ 40 * 884282 * 2
def baseEnd_884282 : Nat := 22422800005887134632507

theorem tailTrace_884282 : CollatzResearch.WordTrace tailWord_884282 prefixEnd_884282 22422800005887134632507 := by
  unfold tailWord_884282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063103545601203046781775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21501609454936541458084733 8063103545601203046781775)
  ·
    refine ⟨12094655318401804570172663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8063103545601203046781775 12094655318401804570172663)
    ·
      refine ⟨18141982977602706855258995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094655318401804570172663 18141982977602706855258995)
      ·
        refine ⟨27212974466404060282888493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18141982977602706855258995 27212974466404060282888493)
        ·
          refine ⟨10204865424901522606083185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27212974466404060282888493 10204865424901522606083185)
          ·
            refine ⟨7653649068676141954562389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204865424901522606083185 7653649068676141954562389)
            ·
              refine ⟨22422800005887134632507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7653649068676141954562389 22422800005887134632507)
              ·
                rfl

theorem cell21_884282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 10].length) (baseStart_884282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884282 prefixEnd_884282 := by exact prefixLift 884282
  have htrace : WordTrace (prefixWord ++ tailWord_884282) baseStart_884282 baseEnd_884282 := by
    simpa [prefixWord, tailWord_884282, baseEnd_884282] using wordTrace_append hprefix tailTrace_884282
  have hstable : (prefixWord ++ tailWord_884282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884282).length < 2 ^ (prefixWord ++ tailWord_884282).sum := by decide
  have hdescent : baseEnd_884282 < baseStart_884282 := by decide
  rcases family_descends (prefixWord ++ tailWord_884282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884285 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_884285 : Nat := 118140960795 + 884285 * 2 ^ 59
def prefixEnd_884285 : Nat := 4983230072969 + 3 ^ 40 * 884285 * 2
def baseEnd_884285 : Nat := 201805884693856873142557

theorem tailTrace_884285 : CollatzResearch.WordTrace tailWord_884285 prefixEnd_884285 201805884693856873142557 := by
  unfold tailWord_884285
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252523601393943699486309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21501682400929295799657539 32252523601393943699486309)
  ·
    refine ⟨6047348175261364443653683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32252523601393943699486309 6047348175261364443653683)
    ·
      refine ⟨9071022262892046665480525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047348175261364443653683 9071022262892046665480525)
      ·
        refine ⟨3401633348584517499555197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9071022262892046665480525 3401633348584517499555197)
        ·
          refine ⟨1275612505719194062333199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3401633348584517499555197 1275612505719194062333199)
          ·
            refine ⟨1913418758578791093499799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275612505719194062333199 1913418758578791093499799)
            ·
              refine ⟨2870128137868186640249699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913418758578791093499799 2870128137868186640249699)
              ·
                refine ⟨4305192206802279960374549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870128137868186640249699 4305192206802279960374549)
                ·
                  refine ⟨201805884693856873142557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4305192206802279960374549 201805884693856873142557)
                  ·
                    rfl

theorem cell21_884285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_884285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884285 prefixEnd_884285 := by exact prefixLift 884285
  have htrace : WordTrace (prefixWord ++ tailWord_884285) baseStart_884285 baseEnd_884285 := by
    simpa [prefixWord, tailWord_884285, baseEnd_884285] using wordTrace_append hprefix tailTrace_884285
  have hstable : (prefixWord ++ tailWord_884285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884285).length < 2 ^ (prefixWord ++ tailWord_884285).sum := by decide
  have hdescent : baseEnd_884285 < baseStart_884285 := by decide
  rcases family_descends (prefixWord ++ tailWord_884285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884316 : List Nat := [2, 2, 4, 1, 2, 1, 4, 5]
def baseStart_884316 : Nat := 118140960795 + 884316 * 2 ^ 59
def prefixEnd_884316 : Nat := 4983230072969 + 3 ^ 40 * 884316 * 2
def baseEnd_884316 : Nat := 67270986438735902708609

theorem tailTrace_884316 : CollatzResearch.WordTrace tailWord_884316 prefixEnd_884316 67270986438735902708609 := by
  unfold tailWord_884316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126827132140817996932401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21502436176187757329243201 16126827132140817996932401)
  ·
    refine ⟨12095120349105613497699301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16126827132140817996932401 12095120349105613497699301)
    ·
      refine ⟨2267835065457302530818619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12095120349105613497699301 2267835065457302530818619)
      ·
        refine ⟨3401752598185953796227929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267835065457302530818619 3401752598185953796227929)
        ·
          refine ⟨2551314448639465347170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401752598185953796227929 2551314448639465347170947)
          ·
            refine ⟨3826971672959198020756421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551314448639465347170947 3826971672959198020756421)
            ·
              refine ⟨717557188679849628891829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3826971672959198020756421 717557188679849628891829)
              ·
                refine ⟨67270986438735902708609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717557188679849628891829 67270986438735902708609)
                ·
                  rfl

theorem cell21_884316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_884316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884316 prefixEnd_884316 := by exact prefixLift 884316
  have htrace : WordTrace (prefixWord ++ tailWord_884316) baseStart_884316 baseEnd_884316 := by
    simpa [prefixWord, tailWord_884316, baseEnd_884316] using wordTrace_append hprefix tailTrace_884316
  have hstable : (prefixWord ++ tailWord_884316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884316).length < 2 ^ (prefixWord ++ tailWord_884316).sum := by decide
  have hdescent : baseEnd_884316 < baseStart_884316 := by decide
  rcases family_descends (prefixWord ++ tailWord_884316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884347 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 3]
def baseStart_884347 : Nat := 118140960795 + 884347 * 2 ^ 59
def prefixEnd_884347 : Nat := 4983230072969 + 3 ^ 40 * 884347 * 2
def baseEnd_884347 : Nat := 201820033938558543109097

theorem tailTrace_884347 : CollatzResearch.WordTrace tailWord_884347 prefixEnd_884347 201820033938558543109097 := by
  unfold tailWord_884347
  simp only [CollatzResearch.WordTrace]
  refine ⟨32254784927169328288243295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21503189951446218858828863 32254784927169328288243295)
  ·
    refine ⟨48382177390753992432364943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32254784927169328288243295 48382177390753992432364943)
    ·
      refine ⟨72573266086130988648547415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48382177390753992432364943 72573266086130988648547415)
      ·
        refine ⟨108859899129196482972821123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72573266086130988648547415 108859899129196482972821123)
        ·
          refine ⟨163289848693794724459231685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108859899129196482972821123 163289848693794724459231685)
          ·
            refine ⟨30616846630086510836105941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163289848693794724459231685 30616846630086510836105941)
            ·
              refine ⟨717582342892652597721233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30616846630086510836105941 717582342892652597721233)
              ·
                refine ⟨538186757169489448290925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717582342892652597721233 538186757169489448290925)
                ·
                  refine ⟨201820033938558543109097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538186757169489448290925 201820033938558543109097)
                  ·
                    rfl

theorem cell21_884347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].length) (baseStart_884347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884347 prefixEnd_884347 := by exact prefixLift 884347
  have htrace : WordTrace (prefixWord ++ tailWord_884347) baseStart_884347 baseEnd_884347 := by
    simpa [prefixWord, tailWord_884347, baseEnd_884347] using wordTrace_append hprefix tailTrace_884347
  have hstable : (prefixWord ++ tailWord_884347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884347).length < 2 ^ (prefixWord ++ tailWord_884347).sum := by decide
  have hdescent : baseEnd_884347 < baseStart_884347 := by decide
  rcases family_descends (prefixWord ++ tailWord_884347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884361 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 4]
def baseStart_884361 : Nat := 118140960795 + 884361 * 2 ^ 59
def prefixEnd_884361 : Nat := 4983230072969 + 3 ^ 40 * 884361 * 2
def baseEnd_884361 : Nat := 201823228929297629875735

theorem tailTrace_884361 : CollatzResearch.WordTrace tailWord_884361 prefixEnd_884361 201823228929297629875735 := by
  unfold tailWord_884361
  simp only [CollatzResearch.WordTrace]
  refine ⟨32255295549118608679252937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21503530366079072452835291 32255295549118608679252937)
  ·
    refine ⟨24191471661838956509439703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32255295549118608679252937 24191471661838956509439703)
    ·
      refine ⟨36287207492758434764159555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24191471661838956509439703 36287207492758434764159555)
      ·
        refine ⟨54430811239137652146239333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36287207492758434764159555 54430811239137652146239333)
        ·
          refine ⟨10205777107338309777419875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54430811239137652146239333 10205777107338309777419875)
          ·
            refine ⟨15308665661007464666129813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10205777107338309777419875 15308665661007464666129813)
            ·
              refine ⟨717593702859724906224835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15308665661007464666129813 717593702859724906224835)
              ·
                refine ⟨1076390554289587359337253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717593702859724906224835 1076390554289587359337253)
                ·
                  refine ⟨201823228929297629875735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076390554289587359337253 201823228929297629875735)
                  ·
                    rfl

theorem cell21_884361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_884361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884361 prefixEnd_884361 := by exact prefixLift 884361
  have htrace : WordTrace (prefixWord ++ tailWord_884361) baseStart_884361 baseEnd_884361 := by
    simpa [prefixWord, tailWord_884361, baseEnd_884361] using wordTrace_append hprefix tailTrace_884361
  have hstable : (prefixWord ++ tailWord_884361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884361).length < 2 ^ (prefixWord ++ tailWord_884361).sum := by decide
  have hdescent : baseEnd_884361 < baseStart_884361 := by decide
  rcases family_descends (prefixWord ++ tailWord_884361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884392 : List Nat := [2, 1, 7, 1, 10]
def baseStart_884392 : Nat := 118140960795 + 884392 * 2 ^ 59
def prefixEnd_884392 : Nat := 4983230072969 + 3 ^ 40 * 884392 * 2
def baseEnd_884392 : Nat := 2491732142612944010605

theorem tailTrace_884392 : CollatzResearch.WordTrace tailWord_884392 prefixEnd_884392 2491732142612944010605 := by
  unfold tailWord_884392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128213106003150486815715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21504284141337533982420953 16128213106003150486815715)
  ·
    refine ⟨24192319659004725730223573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128213106003150486815715 24192319659004725730223573)
    ·
      refine ⟨567007492007923259302115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24192319659004725730223573 567007492007923259302115)
      ·
        refine ⟨850511238011884888953173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567007492007923259302115 850511238011884888953173)
        ·
          refine ⟨2491732142612944010605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 850511238011884888953173 2491732142612944010605)
          ·
            rfl

theorem cell21_884392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 10].length) (baseStart_884392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884392 prefixEnd_884392 := by exact prefixLift 884392
  have htrace : WordTrace (prefixWord ++ tailWord_884392) baseStart_884392 baseEnd_884392 := by
    simpa [prefixWord, tailWord_884392, baseEnd_884392] using wordTrace_append hprefix tailTrace_884392
  have hstable : (prefixWord ++ tailWord_884392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884392).length < 2 ^ (prefixWord ++ tailWord_884392).sum := by decide
  have hdescent : baseEnd_884392 < baseStart_884392 := by decide
  rcases family_descends (prefixWord ++ tailWord_884392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884398 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_884398 : Nat := 118140960795 + 884398 * 2 ^ 59
def prefixEnd_884398 : Nat := 4983230072969 + 3 ^ 40 * 884398 * 2
def baseEnd_884398 : Nat := 201831672833393787758993

theorem tailTrace_884398 : CollatzResearch.WordTrace tailWord_884398 prefixEnd_884398 201831672833393787758993 := by
  unfold tailWord_884398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032080631248070499793731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21504430033323042665566565 4032080631248070499793731)
  ·
    refine ⟨6048120946872105749690597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032080631248070499793731 6048120946872105749690597)
    ·
      refine ⟨1134022677538519828066987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6048120946872105749690597 1134022677538519828066987)
      ·
        refine ⟨1701034016307779742100481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134022677538519828066987 1701034016307779742100481)
        ·
          refine ⟨1275775512230834806575361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701034016307779742100481 1275775512230834806575361)
          ·
            refine ⟨956831634173126104931521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275775512230834806575361 956831634173126104931521)
            ·
              refine ⟨717623725629844578698641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956831634173126104931521 717623725629844578698641)
              ·
                refine ⟨538217794222383434023981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717623725629844578698641 538217794222383434023981)
                ·
                  refine ⟨201831672833393787758993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538217794222383434023981 201831672833393787758993)
                  ·
                    rfl

theorem cell21_884398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_884398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884398 prefixEnd_884398 := by exact prefixLift 884398
  have htrace : WordTrace (prefixWord ++ tailWord_884398) baseStart_884398 baseEnd_884398 := by
    simpa [prefixWord, tailWord_884398, baseEnd_884398] using wordTrace_append hprefix tailTrace_884398
  have hstable : (prefixWord ++ tailWord_884398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884398).length < 2 ^ (prefixWord ++ tailWord_884398).sum := by decide
  have hdescent : baseEnd_884398 < baseStart_884398 := by decide
  rcases family_descends (prefixWord ++ tailWord_884398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884451 : List Nat := [1, 1, 1, 7, 2, 1, 8]
def baseStart_884451 : Nat := 118140960795 + 884451 * 2 ^ 59
def prefixEnd_884451 : Nat := 4983230072969 + 3 ^ 40 * 884451 * 2
def baseEnd_884451 : Nat := 22427085350608608152839

theorem tailTrace_884451 : CollatzResearch.WordTrace tailWord_884451 prefixEnd_884451 22427085350608608152839 := by
  unfold tailWord_884451
  simp only [CollatzResearch.WordTrace]
  refine ⟨32258578118792554050029207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21505718745861702700019471 32258578118792554050029207)
  ·
    refine ⟨48387867178188831075043811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32258578118792554050029207 48387867178188831075043811)
    ·
      refine ⟨72581800767283246612565717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48387867178188831075043811 72581800767283246612565717)
      ·
        refine ⟨1701135955483201092482009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72581800767283246612565717 1701135955483201092482009)
        ·
          refine ⟨1275851966612400819361507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701135955483201092482009 1275851966612400819361507)
          ·
            refine ⟨1913777949918601229042261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275851966612400819361507 1913777949918601229042261)
            ·
              refine ⟨22427085350608608152839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1913777949918601229042261 22427085350608608152839)
              ·
                rfl

theorem cell21_884451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_884451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884451 prefixEnd_884451 := by exact prefixLift 884451
  have htrace : WordTrace (prefixWord ++ tailWord_884451) baseStart_884451 baseEnd_884451 := by
    simpa [prefixWord, tailWord_884451, baseEnd_884451] using wordTrace_append hprefix tailTrace_884451
  have hstable : (prefixWord ++ tailWord_884451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884451).length < 2 ^ (prefixWord ++ tailWord_884451).sum := by decide
  have hdescent : baseEnd_884451 < baseStart_884451 := by decide
  rcases family_descends (prefixWord ++ tailWord_884451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884465 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_884465 : Nat := 118140960795 + 884465 * 2 ^ 59
def prefixEnd_884465 : Nat := 4983230072969 + 3 ^ 40 * 884465 * 2
def baseEnd_884465 : Nat := 201846963146216560142189

theorem tailTrace_884465 : CollatzResearch.WordTrace tailWord_884465 prefixEnd_884465 201846963146216560142189 := by
  unfold tailWord_884465
  simp only [CollatzResearch.WordTrace]
  refine ⟨32259088740741834441038849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21506059160494556294025899 32259088740741834441038849)
  ·
    refine ⟨24194316555556375830779137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32259088740741834441038849 24194316555556375830779137)
    ·
      refine ⟨18145737416667281873084353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24194316555556375830779137 18145737416667281873084353)
      ·
        refine ⟨13609303062500461404813265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18145737416667281873084353 13609303062500461404813265)
        ·
          refine ⟨10206977296875346053609949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13609303062500461404813265 10206977296875346053609949)
          ·
            refine ⟨3827616486328254770103731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10206977296875346053609949 3827616486328254770103731)
            ·
              refine ⟨5741424729492382155155597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827616486328254770103731 5741424729492382155155597)
              ·
                refine ⟨2153034273559643308183349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741424729492382155155597 2153034273559643308183349)
                ·
                  refine ⟨201846963146216560142189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153034273559643308183349 201846963146216560142189)
                  ·
                    rfl

theorem cell21_884465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_884465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884465 prefixEnd_884465 := by exact prefixLift 884465
  have htrace : WordTrace (prefixWord ++ tailWord_884465) baseStart_884465 baseEnd_884465 := by
    simpa [prefixWord, tailWord_884465, baseEnd_884465] using wordTrace_append hprefix tailTrace_884465
  have hstable : (prefixWord ++ tailWord_884465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884465).length < 2 ^ (prefixWord ++ tailWord_884465).sum := by decide
  have hdescent : baseEnd_884465 < baseStart_884465 := by decide
  rcases family_descends (prefixWord ++ tailWord_884465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884482 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_884482 : Nat := 118140960795 + 884482 * 2 ^ 59
def prefixEnd_884482 : Nat := 4983230072969 + 3 ^ 40 * 884482 * 2
def baseEnd_884482 : Nat := 201850842777828308358821

theorem tailTrace_884482 : CollatzResearch.WordTrace tailWord_884482 prefixEnd_884482 201850842777828308358821 := by
  unfold tailWord_884482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064927195420061586101925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21506472521120164229605133 8064927195420061586101925)
  ·
    refine ⟨1512173849141261547394111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8064927195420061586101925 1512173849141261547394111)
    ·
      refine ⟨2268260773711892321091167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512173849141261547394111 2268260773711892321091167)
      ·
        refine ⟨3402391160567838481636751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268260773711892321091167 3402391160567838481636751)
        ·
          refine ⟨5103586740851757722455127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402391160567838481636751 5103586740851757722455127)
          ·
            refine ⟨7655380111277636583682691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103586740851757722455127 7655380111277636583682691)
            ·
              refine ⟨11483070166916454875524037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655380111277636583682691 11483070166916454875524037)
              ·
                refine ⟨2153075656296835289160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11483070166916454875524037 2153075656296835289160757)
                ·
                  refine ⟨201850842777828308358821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153075656296835289160757 201850842777828308358821)
                  ·
                    rfl

theorem cell21_884482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_884482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884482 prefixEnd_884482 := by exact prefixLift 884482
  have htrace : WordTrace (prefixWord ++ tailWord_884482) baseStart_884482 baseEnd_884482 := by
    simpa [prefixWord, tailWord_884482, baseEnd_884482] using wordTrace_append hprefix tailTrace_884482
  have hstable : (prefixWord ++ tailWord_884482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884482).length < 2 ^ (prefixWord ++ tailWord_884482).sum := by decide
  have hdescent : baseEnd_884482 < baseStart_884482 := by decide
  rcases family_descends (prefixWord ++ tailWord_884482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884516 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_884516 : Nat := 118140960795 + 884516 * 2 ^ 59
def prefixEnd_884516 : Nat := 4983230072969 + 3 ^ 40 * 884516 * 2
def baseEnd_884516 : Nat := 201858602041051804792085

theorem tailTrace_884516 : CollatzResearch.WordTrace tailWord_884516 prefixEnd_884516 201858602041051804792085 := by
  unfold tailWord_884516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130474431778535075572701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21507299242371380100763601 16130474431778535075572701)
  ·
    refine ⟨6048927911916950653339763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16130474431778535075572701 6048927911916950653339763)
    ·
      refine ⟨9073391867875425980009645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6048927911916950653339763 9073391867875425980009645)
      ·
        refine ⟨3402521950453284742503617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9073391867875425980009645 3402521950453284742503617)
        ·
          refine ⟨2551891462839963556877713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402521950453284742503617 2551891462839963556877713)
          ·
            refine ⟨1913918597129972667658285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551891462839963556877713 1913918597129972667658285)
            ·
              refine ⟨717719473923739750371857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913918597129972667658285 717719473923739750371857)
              ·
                refine ⟨538289605442804812778893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717719473923739750371857 538289605442804812778893)
                ·
                  refine ⟨201858602041051804792085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538289605442804812778893 201858602041051804792085)
                  ·
                    rfl

theorem cell21_884516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_884516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884516 prefixEnd_884516 := by exact prefixLift 884516
  have htrace : WordTrace (prefixWord ++ tailWord_884516) baseStart_884516 baseEnd_884516 := by
    simpa [prefixWord, tailWord_884516, baseEnd_884516] using wordTrace_append hprefix tailTrace_884516
  have hstable : (prefixWord ++ tailWord_884516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884516).length < 2 ^ (prefixWord ++ tailWord_884516).sum := by decide
  have hdescent : baseEnd_884516 < baseStart_884516 := by decide
  rcases family_descends (prefixWord ++ tailWord_884516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884530 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_884530 : Nat := 118140960795 + 884530 * 2 ^ 59
def prefixEnd_884530 : Nat := 4983230072969 + 3 ^ 40 * 884530 * 2
def baseEnd_884530 : Nat := 201861797031790891558723

theorem tailTrace_884530 : CollatzResearch.WordTrace tailWord_884530 prefixEnd_884530 201861797031790891558723 := by
  unfold tailWord_884530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8065364871376587635538761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21507639657004233694770029 8065364871376587635538761)
  ·
    refine ⟨6049023653532440726654071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8065364871376587635538761 6049023653532440726654071)
    ·
      refine ⟨9073535480298661089981107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049023653532440726654071 9073535480298661089981107)
      ·
        refine ⟨13610303220447991634971661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073535480298661089981107 13610303220447991634971661)
        ·
          refine ⟨5103863707667996863114373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13610303220447991634971661 5103863707667996863114373)
          ·
            refine ⟨956974445187749411833945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5103863707667996863114373 956974445187749411833945)
            ·
              refine ⟨717730833890812058875459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956974445187749411833945 717730833890812058875459)
              ·
                refine ⟨1076596250836218088313189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717730833890812058875459 1076596250836218088313189)
                ·
                  refine ⟨201861797031790891558723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076596250836218088313189 201861797031790891558723)
                  ·
                    rfl

theorem cell21_884530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_884530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884530 prefixEnd_884530 := by exact prefixLift 884530
  have htrace : WordTrace (prefixWord ++ tailWord_884530) baseStart_884530 baseEnd_884530 := by
    simpa [prefixWord, tailWord_884530, baseEnd_884530] using wordTrace_append hprefix tailTrace_884530
  have hstable : (prefixWord ++ tailWord_884530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884530).length < 2 ^ (prefixWord ++ tailWord_884530).sum := by decide
  have hdescent : baseEnd_884530 < baseStart_884530 := by decide
  rcases family_descends (prefixWord ++ tailWord_884530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
