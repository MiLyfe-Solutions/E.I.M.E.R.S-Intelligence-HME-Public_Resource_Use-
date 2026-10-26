import V185TrunkScan23Chunk1121

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6645895 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_6645895 : Nat := 118140960795 + 6645895 * 2 ^ 59
def prefixEnd_6645895 : Nat := 4983230072969 + 3 ^ 40 * 6645895 * 2
def baseEnd_6645895 : Nat := 3412538514312380638948591

theorem tailTrace_6645895 : CollatzResearch.WordTrace tailWord_6645895 prefixEnd_6645895 3412538514312380638948591 := by
  unfold tailWord_6645895
  simp only [CollatzResearch.WordTrace]
  refine ⟨242395704258064918346875139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161597136172043278897916759 242395704258064918346875139)
  ·
    refine ⟨363593556387097377520312709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242395704258064918346875139 363593556387097377520312709)
    ·
      refine ⟨68173791822580758285058633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363593556387097377520312709 68173791822580758285058633)
      ·
        refine ⟨51130343866935568713793975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68173791822580758285058633 51130343866935568713793975)
        ·
          refine ⟨76695515800403353070690963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51130343866935568713793975 76695515800403353070690963)
          ·
            refine ⟨115043273700605029606036445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76695515800403353070690963 115043273700605029606036445)
            ·
              refine ⟨43141227637726886102263667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115043273700605029606036445 43141227637726886102263667)
              ·
                refine ⟨64711841456590329153395501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43141227637726886102263667 64711841456590329153395501)
                ·
                  refine ⟨24266940546221373432523313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64711841456590329153395501 24266940546221373432523313)
                  ·
                    refine ⟨18200205409666030074392485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24266940546221373432523313 18200205409666030074392485)
                    ·
                      refine ⟨3412538514312380638948591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18200205409666030074392485 3412538514312380638948591)
                      ·
                        rfl

theorem cell23_6645895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_6645895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645895 prefixEnd_6645895 := by exact prefixLift 6645895
  have htrace : WordTrace (prefixWord ++ tailWord_6645895) baseStart_6645895 baseEnd_6645895 := by
    simpa [prefixWord, tailWord_6645895, baseEnd_6645895] using wordTrace_append hprefix tailTrace_6645895
  have hstable : (prefixWord ++ tailWord_6645895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645895).length < 2 ^ (prefixWord ++ tailWord_6645895).sum := by decide
  have hdescent : baseEnd_6645895 < baseStart_6645895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645915 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3]
def baseStart_6645915 : Nat := 118140960795 + 6645915 * 2 ^ 59
def prefixEnd_6645915 : Nat := 4983230072969 + 3 ^ 40 * 6645915 * 2
def baseEnd_6645915 : Nat := 3412548783925470560698499

theorem tailTrace_6645915 : CollatzResearch.WordTrace tailWord_6645915 prefixEnd_6645915 3412548783925470560698499 := by
  unfold tailWord_6645915
  simp only [CollatzResearch.WordTrace]
  refine ⟨242396433717992461762603199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161597622478661641175068799 242396433717992461762603199)
  ·
    refine ⟨363594650576988692643904799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242396433717992461762603199 363594650576988692643904799)
    ·
      refine ⟨545391975865483038965857199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363594650576988692643904799 545391975865483038965857199)
      ·
        refine ⟨818087963798224558448785799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545391975865483038965857199 818087963798224558448785799)
        ·
          refine ⟨1227131945697336837673178699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818087963798224558448785799 1227131945697336837673178699)
          ·
            refine ⟨1840697918546005256509768049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227131945697336837673178699 1840697918546005256509768049)
            ·
              refine ⟨1380523438909503942382326037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840697918546005256509768049 1380523438909503942382326037)
              ·
                refine ⟨64712036198882997299171533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1380523438909503942382326037 64712036198882997299171533)
                ·
                  refine ⟨24267013574581123987189325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64712036198882997299171533 24267013574581123987189325)
                  ·
                    refine ⟨9100130090467921495195997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24267013574581123987189325 9100130090467921495195997)
                    ·
                      refine ⟨3412548783925470560698499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100130090467921495195997 3412548783925470560698499)
                      ·
                        rfl

theorem cell23_6645915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].length) (baseStart_6645915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645915 prefixEnd_6645915 := by exact prefixLift 6645915
  have htrace : WordTrace (prefixWord ++ tailWord_6645915) baseStart_6645915 baseEnd_6645915 := by
    simpa [prefixWord, tailWord_6645915, baseEnd_6645915] using wordTrace_append hprefix tailTrace_6645915
  have hstable : (prefixWord ++ tailWord_6645915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645915).length < 2 ^ (prefixWord ++ tailWord_6645915).sum := by decide
  have hdescent : baseEnd_6645915 < baseStart_6645915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645922 : List Nat := [3, 3, 1, 3, 1, 1, 3, 8]
def baseStart_6645922 : Nat := 118140960795 + 6645922 * 2 ^ 59
def prefixEnd_6645922 : Nat := 4983230072969 + 3 ^ 40 * 6645922 * 2
def baseEnd_6645922 : Nat := 126390828825557482715221

theorem tailTrace_6645922 : CollatzResearch.WordTrace tailWord_6645922 prefixEnd_6645922 126390828825557482715221 := by
  unfold tailWord_6645922
  simp only [CollatzResearch.WordTrace]
  refine ⟨60599172257241775489527005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161597792685978067972072013 60599172257241775489527005)
  ·
    refine ⟨22724689596465665808572627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60599172257241775489527005 22724689596465665808572627)
    ·
      refine ⟨34087034394698498712858941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22724689596465665808572627 34087034394698498712858941)
      ·
        refine ⟨12782637898011937017322103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34087034394698498712858941 12782637898011937017322103)
        ·
          refine ⟨19173956847017905525983155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782637898011937017322103 19173956847017905525983155)
          ·
            refine ⟨28760935270526858288974733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19173956847017905525983155 28760935270526858288974733)
            ·
              refine ⟨10785350726447571858365525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28760935270526858288974733 10785350726447571858365525)
              ·
                refine ⟨126390828825557482715221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10785350726447571858365525 126390828825557482715221)
                ·
                  rfl

theorem cell23_6645922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_6645922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645922 prefixEnd_6645922 := by exact prefixLift 6645922
  have htrace : WordTrace (prefixWord ++ tailWord_6645922) baseStart_6645922 baseEnd_6645922 := by
    simpa [prefixWord, tailWord_6645922, baseEnd_6645922] using wordTrace_append hprefix tailTrace_6645922
  have hstable : (prefixWord ++ tailWord_6645922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645922).length < 2 ^ (prefixWord ++ tailWord_6645922).sum := by decide
  have hdescent : baseEnd_6645922 < baseStart_6645922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645945 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6645945 : Nat := 118140960795 + 6645945 * 2 ^ 59
def prefixEnd_6645945 : Nat := 4983230072969 + 3 ^ 40 * 6645945 * 2
def baseEnd_6645945 : Nat := 3412564188345105443323361

theorem tailTrace_6645945 : CollatzResearch.WordTrace tailWord_6645945 prefixEnd_6645945 3412564188345105443323361 := by
  unfold tailWord_6645945
  simp only [CollatzResearch.WordTrace]
  refine ⟨242397527907883776886195289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161598351938589184590796859 242397527907883776886195289)
  ·
    refine ⟨181798145930912832664646467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242397527907883776886195289 181798145930912832664646467)
    ·
      refine ⟨272697218896369248996969701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181798145930912832664646467 272697218896369248996969701)
      ·
        refine ⟨51130728543069234186931819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272697218896369248996969701 51130728543069234186931819)
        ·
          refine ⟨76696092814603851280397729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51130728543069234186931819 76696092814603851280397729)
          ·
            refine ⟨57522069610952888460298297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76696092814603851280397729 57522069610952888460298297)
            ·
              refine ⟨43141552208214666345223723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57522069610952888460298297 43141552208214666345223723)
              ·
                refine ⟨64712328312321999517835585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43141552208214666345223723 64712328312321999517835585)
                ·
                  refine ⟨48534246234241499638376689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64712328312321999517835585 48534246234241499638376689)
                  ·
                    refine ⟨36400684675681124728782517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48534246234241499638376689 36400684675681124728782517)
                    ·
                      refine ⟨3412564188345105443323361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36400684675681124728782517 3412564188345105443323361)
                      ·
                        rfl

theorem cell23_6645945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6645945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645945 prefixEnd_6645945 := by exact prefixLift 6645945
  have htrace : WordTrace (prefixWord ++ tailWord_6645945) baseStart_6645945 baseEnd_6645945 := by
    simpa [prefixWord, tailWord_6645945, baseEnd_6645945] using wordTrace_append hprefix tailTrace_6645945
  have hstable : (prefixWord ++ tailWord_6645945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645945).length < 2 ^ (prefixWord ++ tailWord_6645945).sum := by decide
  have hdescent : baseEnd_6645945 < baseStart_6645945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645950 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_6645950 : Nat := 118140960795 + 6645950 * 2 ^ 59
def prefixEnd_6645950 : Nat := 4983230072969 + 3 ^ 40 * 6645950 * 2
def baseEnd_6645950 : Nat := 3412566755748377923760839

theorem tailTrace_6645950 : CollatzResearch.WordTrace tailWord_6645950 prefixEnd_6645950 3412566755748377923760839 := by
  unfold tailWord_6645950
  simp only [CollatzResearch.WordTrace]
  refine ⟨30299713784108207842515913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161598473515243775160084869 30299713784108207842515913)
  ·
    refine ⟨22724785338081155881886935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30299713784108207842515913 22724785338081155881886935)
    ·
      refine ⟨34087178007121733822830403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22724785338081155881886935 34087178007121733822830403)
      ·
        refine ⟨51130767010682600734245605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34087178007121733822830403 51130767010682600734245605)
        ·
          refine ⟨9587018814502987637671051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51130767010682600734245605 9587018814502987637671051)
          ·
            refine ⟨14380528221754481456506577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587018814502987637671051 14380528221754481456506577)
            ·
              refine ⟨10785396166315861092379933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14380528221754481456506577 10785396166315861092379933)
              ·
                refine ⟨4044523562368447909642475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10785396166315861092379933 4044523562368447909642475)
                ·
                  refine ⟨6066785343552671864463713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044523562368447909642475 6066785343552671864463713)
                  ·
                    refine ⟨4550089007664503898347785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066785343552671864463713 4550089007664503898347785)
                    ·
                      refine ⟨3412566755748377923760839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550089007664503898347785 3412566755748377923760839)
                      ·
                        rfl

theorem cell23_6645950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_6645950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645950 prefixEnd_6645950 := by exact prefixLift 6645950
  have htrace : WordTrace (prefixWord ++ tailWord_6645950) baseStart_6645950 baseEnd_6645950 := by
    simpa [prefixWord, tailWord_6645950, baseEnd_6645950] using wordTrace_append hprefix tailTrace_6645950
  have hstable : (prefixWord ++ tailWord_6645950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645950).length < 2 ^ (prefixWord ++ tailWord_6645950).sum := by decide
  have hdescent : baseEnd_6645950 < baseStart_6645950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645966 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_6645966 : Nat := 118140960795 + 6645966 * 2 ^ 59
def prefixEnd_6645966 : Nat := 4983230072969 + 3 ^ 40 * 6645966 * 2
def baseEnd_6645966 : Nat := 3412574971438849861160765

theorem tailTrace_6645966 : CollatzResearch.WordTrace tailWord_6645966 prefixEnd_6645966 3412574971438849861160765 := by
  unfold tailWord_6645966
  simp only [CollatzResearch.WordTrace]
  refine ⟨30299786730100962184088719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161598862560538464981806501 30299786730100962184088719)
  ·
    refine ⟨45449680095151443276133079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30299786730100962184088719 45449680095151443276133079)
    ·
      refine ⟨68174520142727164914199619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45449680095151443276133079 68174520142727164914199619)
      ·
        refine ⟨102261780214090747371299429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68174520142727164914199619 102261780214090747371299429)
        ·
          refine ⟨19174083790142015132118643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102261780214090747371299429 19174083790142015132118643)
          ·
            refine ⟨28761125685213022698177965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19174083790142015132118643 28761125685213022698177965)
            ·
              refine ⟨10785422131954883511816737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28761125685213022698177965 10785422131954883511816737)
              ·
                refine ⟨8089066598966162633862553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10785422131954883511816737 8089066598966162633862553)
                ·
                  refine ⟨6066799949224621975396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8089066598966162633862553 6066799949224621975396915)
                  ·
                    refine ⟨9100199923836932963095373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6066799949224621975396915 9100199923836932963095373)
                    ·
                      refine ⟨3412574971438849861160765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100199923836932963095373 3412574971438849861160765)
                      ·
                        rfl

theorem cell23_6645966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_6645966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645966 prefixEnd_6645966 := by exact prefixLift 6645966
  have htrace : WordTrace (prefixWord ++ tailWord_6645966) baseStart_6645966 baseEnd_6645966 := by
    simpa [prefixWord, tailWord_6645966, baseEnd_6645966] using wordTrace_append hprefix tailTrace_6645966
  have hstable : (prefixWord ++ tailWord_6645966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645966).length < 2 ^ (prefixWord ++ tailWord_6645966).sum := by decide
  have hdescent : baseEnd_6645966 < baseStart_6645966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645975 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_6645975 : Nat := 118140960795 + 6645975 * 2 ^ 59
def prefixEnd_6645975 : Nat := 4983230072969 + 3 ^ 40 * 6645975 * 2
def baseEnd_6645975 : Nat := 3412579592764740325948223

theorem tailTrace_6645975 : CollatzResearch.WordTrace tailWord_6645975 prefixEnd_6645975 3412579592764740325948223 := by
  unfold tailWord_6645975
  simp only [CollatzResearch.WordTrace]
  refine ⟨242398622097775092009787379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161599081398516728006524919 242398622097775092009787379)
  ·
    refine ⟨363597933146662638014681069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242398622097775092009787379 363597933146662638014681069)
    ·
      refine ⟨136349224929998489255505401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363597933146662638014681069 136349224929998489255505401)
      ·
        refine ⟨102261918697498866941629051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136349224929998489255505401 102261918697498866941629051)
        ·
          refine ⟨153392878046248300412443577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102261918697498866941629051 153392878046248300412443577)
          ·
            refine ⟨115044658534686225309332683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153392878046248300412443577 115044658534686225309332683)
            ·
              refine ⟨172566987802029337963999025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115044658534686225309332683 172566987802029337963999025)
              ·
                refine ⟨129425240851522003472999269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172566987802029337963999025 129425240851522003472999269)
                ·
                  refine ⟨24267232659660375651187363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129425240851522003472999269 24267232659660375651187363)
                  ·
                    refine ⟨36400848989490563476781045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24267232659660375651187363 36400848989490563476781045)
                    ·
                      refine ⟨3412579592764740325948223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36400848989490563476781045 3412579592764740325948223)
                      ·
                        rfl

theorem cell23_6645975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_6645975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645975 prefixEnd_6645975 := by exact prefixLift 6645975
  have htrace : WordTrace (prefixWord ++ tailWord_6645975) baseStart_6645975 baseEnd_6645975 := by
    simpa [prefixWord, tailWord_6645975, baseEnd_6645975] using wordTrace_append hprefix tailTrace_6645975
  have hstable : (prefixWord ++ tailWord_6645975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645975).length < 2 ^ (prefixWord ++ tailWord_6645975).sum := by decide
  have hdescent : baseEnd_6645975 < baseStart_6645975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645995 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 7]
def baseStart_6645995 : Nat := 118140960795 + 6645995 * 2 ^ 59
def prefixEnd_6645995 : Nat := 4983230072969 + 3 ^ 40 * 6645995 * 2
def baseEnd_6645995 : Nat := 379176651375314471966459

theorem tailTrace_6645995 : CollatzResearch.WordTrace tailWord_6645995 prefixEnd_6645995 379176651375314471966459 := by
  unfold tailWord_6645995
  simp only [CollatzResearch.WordTrace]
  refine ⟨242399351557702635425515439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161599567705135090283676959 242399351557702635425515439)
  ·
    refine ⟨363599027336553953138273159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242399351557702635425515439 363599027336553953138273159)
    ·
      refine ⟨545398541004830929707409739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363599027336553953138273159 545398541004830929707409739)
      ·
        refine ⟨818097811507246394561114609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545398541004830929707409739 818097811507246394561114609)
        ·
          refine ⟨613573358630434795920835957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818097811507246394561114609 613573358630434795920835957)
          ·
            refine ⟨57522502371603262117578371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613573358630434795920835957 57522502371603262117578371)
            ·
              refine ⟨86283753557404893176367557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57522502371603262117578371 86283753557404893176367557)
              ·
                refine ⟨16178203792013417470568917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86283753557404893176367557 16178203792013417470568917)
                ·
                  refine ⟨379176651375314471966459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16178203792013417470568917 379176651375314471966459)
                  ·
                    rfl

theorem cell23_6645995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 7].length) (baseStart_6645995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645995 prefixEnd_6645995 := by exact prefixLift 6645995
  have htrace : WordTrace (prefixWord ++ tailWord_6645995) baseStart_6645995 baseEnd_6645995 := by
    simpa [prefixWord, tailWord_6645995, baseEnd_6645995] using wordTrace_append hprefix tailTrace_6645995
  have hstable : (prefixWord ++ tailWord_6645995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645995).length < 2 ^ (prefixWord ++ tailWord_6645995).sum := by decide
  have hdescent : baseEnd_6645995 < baseStart_6645995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646006 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6646006 : Nat := 118140960795 + 6646006 * 2 ^ 59
def prefixEnd_6646006 : Nat := 4983230072969 + 3 ^ 40 * 6646006 * 2
def baseEnd_6646006 : Nat := 3412595510665029704660581

theorem tailTrace_6646006 : CollatzResearch.WordTrace tailWord_6646006 prefixEnd_6646006 3412595510665029704660581 := by
  unfold tailWord_6646006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149984547541424019010367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161599835173775189536110581 15149984547541424019010367)
  ·
    refine ⟨22724976821312136028515551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15149984547541424019010367 22724976821312136028515551)
    ·
      refine ⟨34087465231968204042773327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22724976821312136028515551 34087465231968204042773327)
      ·
        refine ⟨51131197847952306064159991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34087465231968204042773327 51131197847952306064159991)
        ·
          refine ⟨76696796771928459096239987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51131197847952306064159991 76696796771928459096239987)
          ·
            refine ⟨115045195157892688644359981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76696796771928459096239987 115045195157892688644359981)
            ·
              refine ⟨43141948184209758241634993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115045195157892688644359981 43141948184209758241634993)
              ·
                refine ⟨32356461138157318681226245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43141948184209758241634993 32356461138157318681226245)
                ·
                  refine ⟨6066836463404497252729921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32356461138157318681226245 6066836463404497252729921)
                  ·
                    refine ⟨4550127347553372939547441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066836463404497252729921 4550127347553372939547441)
                    ·
                      refine ⟨3412595510665029704660581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550127347553372939547441 3412595510665029704660581)
                      ·
                        rfl

theorem cell23_6646006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6646006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646006 prefixEnd_6646006 := by exact prefixLift 6646006
  have htrace : WordTrace (prefixWord ++ tailWord_6646006) baseStart_6646006 baseEnd_6646006 := by
    simpa [prefixWord, tailWord_6646006, baseEnd_6646006] using wordTrace_append hprefix tailTrace_6646006
  have hstable : (prefixWord ++ tailWord_6646006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646006).length < 2 ^ (prefixWord ++ tailWord_6646006).sum := by decide
  have hdescent : baseEnd_6646006 < baseStart_6646006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646079 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 4, 2]
def baseStart_6646079 : Nat := 118140960795 + 6646079 * 2 ^ 59
def prefixEnd_6646079 : Nat := 4983230072969 + 3 ^ 40 * 6646079 * 2
def baseEnd_6646079 : Nat := 3412632994752807919047745

theorem tailTrace_6646079 : CollatzResearch.WordTrace tailWord_6646079 prefixEnd_6646079 3412632994752807919047745 := by
  unfold tailWord_6646079
  simp only [CollatzResearch.WordTrace]
  refine ⟨242402415289398317771573291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161601610192932211847715527 242402415289398317771573291)
  ·
    refine ⟨363603622934097476657359937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242402415289398317771573291 363603622934097476657359937)
    ·
      refine ⟨272702717200573107493019953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363603622934097476657359937 272702717200573107493019953)
      ·
        refine ⟨204527037900429830619764965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272702717200573107493019953 204527037900429830619764965)
        ·
          refine ⟨38348819606330593241205931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204527037900429830619764965 38348819606330593241205931)
          ·
            refine ⟨57523229409495889861808897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38348819606330593241205931 57523229409495889861808897)
            ·
              refine ⟨43142422057121917396356673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57523229409495889861808897 43142422057121917396356673)
              ·
                refine ⟨32356816542841438047267505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43142422057121917396356673 32356816542841438047267505)
                ·
                  refine ⟨24267612407131078535450629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32356816542841438047267505 24267612407131078535450629)
                  ·
                    refine ⟨4550177326337077225396993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24267612407131078535450629 4550177326337077225396993)
                    ·
                      refine ⟨3412632994752807919047745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550177326337077225396993 3412632994752807919047745)
                      ·
                        rfl

theorem cell23_6646079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_6646079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646079 prefixEnd_6646079 := by exact prefixLift 6646079
  have htrace : WordTrace (prefixWord ++ tailWord_6646079) baseStart_6646079 baseEnd_6646079 := by
    simpa [prefixWord, tailWord_6646079, baseEnd_6646079] using wordTrace_append hprefix tailTrace_6646079
  have hstable : (prefixWord ++ tailWord_6646079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646079).length < 2 ^ (prefixWord ++ tailWord_6646079).sum := by decide
  have hdescent : baseEnd_6646079 < baseStart_6646079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646110 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6646110 : Nat := 118140960795 + 6646110 * 2 ^ 59
def prefixEnd_6646110 : Nat := 4983230072969 + 3 ^ 40 * 6646110 * 2
def baseEnd_6646110 : Nat := 1137549637551032432586701

theorem tailTrace_6646110 : CollatzResearch.WordTrace tailWord_6646110 prefixEnd_6646110 1137549637551032432586701 := by
  unfold tailWord_6646110
  simp only [CollatzResearch.WordTrace]
  refine ⟨30300443244035751258243973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161602363968190673377301189 30300443244035751258243973)
  ·
    refine ⟨5681333108256703360920745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30300443244035751258243973 5681333108256703360920745)
    ·
      refine ⟨4260999831192527520690559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681333108256703360920745 4260999831192527520690559)
      ·
        refine ⟨6391499746788791281035839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260999831192527520690559 6391499746788791281035839)
        ·
          refine ⟨9587249620183186921553759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391499746788791281035839 9587249620183186921553759)
          ·
            refine ⟨14380874430274780382330639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587249620183186921553759 14380874430274780382330639)
            ·
              refine ⟨21571311645412170573495959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14380874430274780382330639 21571311645412170573495959)
              ·
                refine ⟨32356967468118255860243939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21571311645412170573495959 32356967468118255860243939)
                ·
                  refine ⟨48535451202177383790365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32356967468118255860243939 48535451202177383790365909)
                  ·
                    refine ⟨1137549637551032432586701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48535451202177383790365909 1137549637551032432586701)
                    ·
                      rfl

theorem cell23_6646110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6646110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646110 prefixEnd_6646110 := by exact prefixLift 6646110
  have htrace : WordTrace (prefixWord ++ tailWord_6646110) baseStart_6646110 baseEnd_6646110 := by
    simpa [prefixWord, tailWord_6646110, baseEnd_6646110] using wordTrace_append hprefix tailTrace_6646110
  have hstable : (prefixWord ++ tailWord_6646110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646110).length < 2 ^ (prefixWord ++ tailWord_6646110).sum := by decide
  have hdescent : baseEnd_6646110 < baseStart_6646110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646129 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_6646129 : Nat := 118140960795 + 6646129 * 2 ^ 59
def prefixEnd_6646129 : Nat := 4983230072969 + 3 ^ 40 * 6646129 * 2
def baseEnd_6646129 : Nat := 3412658668785532723422515

theorem tailTrace_6646129 : CollatzResearch.WordTrace tailWord_6646129 prefixEnd_6646129 3412658668785532723422515 := by
  unfold tailWord_6646129
  simp only [CollatzResearch.WordTrace]
  refine ⟨242404238939217176310893441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161602825959478117540595627 242404238939217176310893441)
  ·
    refine ⟨181803179204412882233170081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242404238939217176310893441 181803179204412882233170081)
    ·
      refine ⟨136352384403309661674877561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181803179204412882233170081 136352384403309661674877561)
      ·
        refine ⟨102264288302482246256158171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136352384403309661674877561 102264288302482246256158171)
        ·
          refine ⟨153396432453723369384237257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102264288302482246256158171 153396432453723369384237257)
          ·
            refine ⟨115047324340292527038177943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153396432453723369384237257 115047324340292527038177943)
            ·
              refine ⟨172570986510438790557266915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115047324340292527038177943 172570986510438790557266915)
              ·
                refine ⟨258856479765658185835900373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172570986510438790557266915 258856479765658185835900373)
                ·
                  refine ⟨6066948744507613730528915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 258856479765658185835900373 6066948744507613730528915)
                  ·
                    refine ⟨9100423116761420595793373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6066948744507613730528915 9100423116761420595793373)
                    ·
                      refine ⟨3412658668785532723422515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100423116761420595793373 3412658668785532723422515)
                      ·
                        rfl

theorem cell23_6646129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_6646129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646129 prefixEnd_6646129 := by exact prefixLift 6646129
  have htrace : WordTrace (prefixWord ++ tailWord_6646129) baseStart_6646129 baseEnd_6646129 := by
    simpa [prefixWord, tailWord_6646129, baseEnd_6646129] using wordTrace_append hprefix tailTrace_6646129
  have hstable : (prefixWord ++ tailWord_6646129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646129).length < 2 ^ (prefixWord ++ tailWord_6646129).sum := by decide
  have hdescent : baseEnd_6646129 < baseStart_6646129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646169 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 6, 2]
def baseStart_6646169 : Nat := 118140960795 + 6646169 * 2 ^ 59
def prefixEnd_6646169 : Nat := 4983230072969 + 3 ^ 40 * 6646169 * 2
def baseEnd_6646169 : Nat := 3412679208011712566922331

theorem tailTrace_6646169 : CollatzResearch.WordTrace tailWord_6646169 prefixEnd_6646169 3412679208011712566922331 := by
  unfold tailWord_6646169
  simp only [CollatzResearch.WordTrace]
  refine ⟨242405697859072263142349561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161603798572714842094899707 242405697859072263142349561)
  ·
    refine ⟨181804273394304197356762171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242405697859072263142349561 181804273394304197356762171)
    ·
      refine ⟨272706410091456296035143257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181804273394304197356762171 272706410091456296035143257)
      ·
        refine ⟨204529807568592222026357443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272706410091456296035143257 204529807568592222026357443)
        ·
          refine ⟨306794711352888333039536165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204529807568592222026357443 306794711352888333039536165)
          ·
            refine ⟨57524008378666562444913031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306794711352888333039536165 57524008378666562444913031)
            ·
              refine ⟨86286012567999843667369547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57524008378666562444913031 86286012567999843667369547)
              ·
                refine ⟨129429018851999765501054321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86286012567999843667369547 129429018851999765501054321)
                ·
                  refine ⟨97071764138999824125790741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129429018851999765501054321 97071764138999824125790741)
                  ·
                    refine ⟨4550238944015616755896441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97071764138999824125790741 4550238944015616755896441)
                    ·
                      refine ⟨3412679208011712566922331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550238944015616755896441 3412679208011712566922331)
                      ·
                        rfl

theorem cell23_6646169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_6646169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646169 prefixEnd_6646169 := by exact prefixLift 6646169
  have htrace : WordTrace (prefixWord ++ tailWord_6646169) baseStart_6646169 baseEnd_6646169 := by
    simpa [prefixWord, tailWord_6646169, baseEnd_6646169] using wordTrace_append hprefix tailTrace_6646169
  have hstable : (prefixWord ++ tailWord_6646169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646169).length < 2 ^ (prefixWord ++ tailWord_6646169).sum := by decide
  have hdescent : baseEnd_6646169 < baseStart_6646169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646179 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 4, 4]
def baseStart_6646179 : Nat := 118140960795 + 6646179 * 2 ^ 59
def prefixEnd_6646179 : Nat := 4983230072969 + 3 ^ 40 * 6646179 * 2
def baseEnd_6646179 : Nat := 1137561447606085842599095

theorem tailTrace_6646179 : CollatzResearch.WordTrace tailWord_6646179 prefixEnd_6646179 1137561447606085842599095 := by
  unfold tailWord_6646179
  simp only [CollatzResearch.WordTrace]
  refine ⟨242406062589036034850213591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161604041726024023233475727 242406062589036034850213591)
  ·
    refine ⟨363609093883554052275320387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242406062589036034850213591 363609093883554052275320387)
    ·
      refine ⟨545413640825331078412980581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363609093883554052275320387 545413640825331078412980581)
      ·
        refine ⟨102265057654749577202433859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545413640825331078412980581 102265057654749577202433859)
        ·
          refine ⟨153397586482124365803650789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102265057654749577202433859 153397586482124365803650789)
          ·
            refine ⟨28762047465398318588184523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153397586482124365803650789 28762047465398318588184523)
            ·
              refine ⟨43143071198097477882276785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28762047465398318588184523 43143071198097477882276785)
              ·
                refine ⟨32357303398573108411707589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43143071198097477882276785 32357303398573108411707589)
                ·
                  refine ⟨6066994387232457827195173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32357303398573108411707589 6066994387232457827195173)
                  ·
                    refine ⟨1137561447606085842599095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066994387232457827195173 1137561447606085842599095)
                    ·
                      rfl

theorem cell23_6646179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 4].length) (baseStart_6646179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646179 prefixEnd_6646179 := by exact prefixLift 6646179
  have htrace : WordTrace (prefixWord ++ tailWord_6646179) baseStart_6646179 baseEnd_6646179 := by
    simpa [prefixWord, tailWord_6646179, baseEnd_6646179] using wordTrace_append hprefix tailTrace_6646179
  have hstable : (prefixWord ++ tailWord_6646179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646179).length < 2 ^ (prefixWord ++ tailWord_6646179).sum := by decide
  have hdescent : baseEnd_6646179 < baseStart_6646179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646197 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6646197 : Nat := 118140960795 + 6646197 * 2 ^ 59
def prefixEnd_6646197 : Nat := 4983230072969 + 3 ^ 40 * 6646197 * 2
def baseEnd_6646197 : Nat := 3412693585470038457372203

theorem tailTrace_6646197 : CollatzResearch.WordTrace tailWord_6646197 prefixEnd_6646197 3412693585470038457372203 := by
  unfold tailWord_6646197
  simp only [CollatzResearch.WordTrace]
  refine ⟨242406719102970823924368845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161604479401980549282912563 242406719102970823924368845)
  ·
    refine ⟨90902519663614058971638317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242406719102970823924368845 90902519663614058971638317)
    ·
      refine ⟨34088444873855272114364369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90902519663614058971638317 34088444873855272114364369)
      ·
        refine ⟨25566333655391454085773277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34088444873855272114364369 25566333655391454085773277)
        ·
          refine ⟨9587375120771795282164979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25566333655391454085773277 9587375120771795282164979)
          ·
            refine ⟨14381062681157692923247469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587375120771795282164979 14381062681157692923247469)
            ·
              refine ⟨5392898505434134846217801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14381062681157692923247469 5392898505434134846217801)
              ·
                refine ⟨4044673879075601134663351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392898505434134846217801 4044673879075601134663351)
                ·
                  refine ⟨6067010818613401701995027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044673879075601134663351 6067010818613401701995027)
                  ·
                    refine ⟨9100516227920102552992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067010818613401701995027 9100516227920102552992541)
                    ·
                      refine ⟨3412693585470038457372203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100516227920102552992541 3412693585470038457372203)
                      ·
                        rfl

theorem cell23_6646197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6646197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646197 prefixEnd_6646197 := by exact prefixLift 6646197
  have htrace : WordTrace (prefixWord ++ tailWord_6646197) baseStart_6646197 baseEnd_6646197 := by
    simpa [prefixWord, tailWord_6646197, baseEnd_6646197] using wordTrace_append hprefix tailTrace_6646197
  have hstable : (prefixWord ++ tailWord_6646197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646197).length < 2 ^ (prefixWord ++ tailWord_6646197).sum := by decide
  have hdescent : baseEnd_6646197 < baseStart_6646197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646219 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3]
def baseStart_6646219 : Nat := 118140960795 + 6646219 * 2 ^ 59
def prefixEnd_6646219 : Nat := 4983230072969 + 3 ^ 40 * 6646219 * 2
def baseEnd_6646219 : Nat := 3412704882044437371297101

theorem tailTrace_6646219 : CollatzResearch.WordTrace tailWord_6646219 prefixEnd_6646219 3412704882044437371297101 := by
  unfold tailWord_6646219
  simp only [CollatzResearch.WordTrace]
  refine ⟨242407521508891121681669711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161605014339260747787779807 242407521508891121681669711)
  ·
    refine ⟨363611282263336682522504567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242407521508891121681669711 363611282263336682522504567)
    ·
      refine ⟨545416923395005023783756851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363611282263336682522504567 545416923395005023783756851)
      ·
        refine ⟨818125385092507535675635277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545416923395005023783756851 818125385092507535675635277)
        ·
          refine ⟨306797019409690325878363229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 818125385092507535675635277 306797019409690325878363229)
          ·
            refine ⟨115048882278633872204386211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306797019409690325878363229 115048882278633872204386211)
            ·
              refine ⟨172573323417950808306579317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115048882278633872204386211 172573323417950808306579317)
              ·
                refine ⟨16178749070432888278741811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172573323417950808306579317 16178749070432888278741811)
                ·
                  refine ⟨24268123605649332418112717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16178749070432888278741811 24268123605649332418112717)
                  ·
                    refine ⟨9100546352118499656792269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24268123605649332418112717 9100546352118499656792269)
                    ·
                      refine ⟨3412704882044437371297101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100546352118499656792269 3412704882044437371297101)
                      ·
                        rfl

theorem cell23_6646219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].length) (baseStart_6646219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646219 prefixEnd_6646219 := by exact prefixLift 6646219
  have htrace : WordTrace (prefixWord ++ tailWord_6646219) baseStart_6646219 baseEnd_6646219 := by
    simpa [prefixWord, tailWord_6646219, baseEnd_6646219] using wordTrace_append hprefix tailTrace_6646219
  have hstable : (prefixWord ++ tailWord_6646219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646219).length < 2 ^ (prefixWord ++ tailWord_6646219).sum := by decide
  have hdescent : baseEnd_6646219 < baseStart_6646219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646220 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6646220 : Nat := 118140960795 + 6646220 * 2 ^ 59
def prefixEnd_6646220 : Nat := 4983230072969 + 3 ^ 40 * 6646220 * 2
def baseEnd_6646220 : Nat := 3412705395525091867384597

theorem tailTrace_6646220 : CollatzResearch.WordTrace tailWord_6646220 prefixEnd_6646220 3412705395525091867384597 := by
  unfold tailWord_6646220
  simp only [CollatzResearch.WordTrace]
  refine ⟨121203778990943749426228057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161605038654591665901637409 121203778990943749426228057)
  ·
    refine ⟨90902834243207812069671043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121203778990943749426228057 90902834243207812069671043)
    ·
      refine ⟨136354251364811718104506565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90902834243207812069671043 136354251364811718104506565)
      ·
        refine ⟨25566422130902197144594981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136354251364811718104506565 25566422130902197144594981)
        ·
          refine ⟨4793704149544161964611559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25566422130902197144594981 4793704149544161964611559)
          ·
            refine ⟨7190556224316242946917339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793704149544161964611559 7190556224316242946917339)
            ·
              refine ⟨10785834336474364420376009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190556224316242946917339 10785834336474364420376009)
              ·
                refine ⟨8089375752355773315282007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10785834336474364420376009 8089375752355773315282007)
                ·
                  refine ⟨12134063628533659972923011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8089375752355773315282007 12134063628533659972923011)
                  ·
                    refine ⟨18201095442800489959384517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12134063628533659972923011 18201095442800489959384517)
                    ·
                      refine ⟨3412705395525091867384597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18201095442800489959384517 3412705395525091867384597)
                      ·
                        rfl

theorem cell23_6646220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6646220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646220 prefixEnd_6646220 := by exact prefixLift 6646220
  have htrace : WordTrace (prefixWord ++ tailWord_6646220) baseStart_6646220 baseEnd_6646220 := by
    simpa [prefixWord, tailWord_6646220, baseEnd_6646220] using wordTrace_append hprefix tailTrace_6646220
  have hstable : (prefixWord ++ tailWord_6646220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646220).length < 2 ^ (prefixWord ++ tailWord_6646220).sum := by decide
  have hdescent : baseEnd_6646220 < baseStart_6646220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646254 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_6646254 : Nat := 118140960795 + 6646254 * 2 ^ 59
def prefixEnd_6646254 : Nat := 4983230072969 + 3 ^ 40 * 6646254 * 2
def baseEnd_6646254 : Nat := 3412722853867344734359441

theorem tailTrace_6646254 : CollatzResearch.WordTrace tailWord_6646254 prefixEnd_6646254 3412722853867344734359441 := by
  unfold tailWord_6646254
  simp only [CollatzResearch.WordTrace]
  refine ⟨30301099757970540332399227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161605865375842881772795877 30301099757970540332399227)
  ·
    refine ⟨45451649636955810498598841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30301099757970540332399227 45451649636955810498598841)
    ·
      refine ⟨34088737227716857873949131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45451649636955810498598841 34088737227716857873949131)
      ·
        refine ⟨51133105841575286810923697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34088737227716857873949131 51133105841575286810923697)
        ·
          refine ⟨38349829381181465108192773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51133105841575286810923697 38349829381181465108192773)
          ·
            refine ⟨7190593008971524707786145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38349829381181465108192773 7190593008971524707786145)
            ·
              refine ⟨5392944756728643530839609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190593008971524707786145 5392944756728643530839609)
              ·
                refine ⟨4044708567546482648129707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392944756728643530839609 4044708567546482648129707)
                ·
                  refine ⟨6067062851319723972194561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044708567546482648129707 6067062851319723972194561)
                  ·
                    refine ⟨4550297138489792979145921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067062851319723972194561 4550297138489792979145921)
                    ·
                      refine ⟨3412722853867344734359441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550297138489792979145921 3412722853867344734359441)
                      ·
                        rfl

theorem cell23_6646254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_6646254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646254 prefixEnd_6646254 := by exact prefixLift 6646254
  have htrace : WordTrace (prefixWord ++ tailWord_6646254) baseStart_6646254 baseEnd_6646254 := by
    simpa [prefixWord, tailWord_6646254, baseEnd_6646254] using wordTrace_append hprefix tailTrace_6646254
  have hstable : (prefixWord ++ tailWord_6646254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646254).length < 2 ^ (prefixWord ++ tailWord_6646254).sum := by decide
  have hdescent : baseEnd_6646254 < baseStart_6646254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646269 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_6646269 : Nat := 118140960795 + 6646269 * 2 ^ 59
def prefixEnd_6646269 : Nat := 4983230072969 + 3 ^ 40 * 6646269 * 2
def baseEnd_6646269 : Nat := 1137576852025720725223957

theorem tailTrace_6646269 : CollatzResearch.WordTrace tailWord_6646269 prefixEnd_6646269 1137576852025720725223957 := by
  unfold tailWord_6646269
  simp only [CollatzResearch.WordTrace]
  refine ⟨242409345158709980220989861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161606230105806653480659907 242409345158709980220989861)
  ·
    refine ⟨45451752217258121291435599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242409345158709980220989861 45451752217258121291435599)
    ·
      refine ⟨68177628325887181937153399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45451752217258121291435599 68177628325887181937153399)
      ·
        refine ⟨102266442488830772905730099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68177628325887181937153399 102266442488830772905730099)
        ·
          refine ⟨153399663733246159358595149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102266442488830772905730099 153399663733246159358595149)
          ·
            refine ⟨57524873899967309759473181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153399663733246159358595149 57524873899967309759473181)
            ·
              refine ⟨21571827712487741159802443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57524873899967309759473181 21571827712487741159802443)
              ·
                refine ⟨32357741568731611739703665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21571827712487741159802443 32357741568731611739703665)
                ·
                  refine ⟨24268306176548708804777749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32357741568731611739703665 24268306176548708804777749)
                  ·
                    refine ⟨1137576852025720725223957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24268306176548708804777749 1137576852025720725223957)
                    ·
                      rfl

theorem cell23_6646269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_6646269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646269 prefixEnd_6646269 := by exact prefixLift 6646269
  have htrace : WordTrace (prefixWord ++ tailWord_6646269) baseStart_6646269 baseEnd_6646269 := by
    simpa [prefixWord, tailWord_6646269, baseEnd_6646269] using wordTrace_append hprefix tailTrace_6646269
  have hstable : (prefixWord ++ tailWord_6646269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646269).length < 2 ^ (prefixWord ++ tailWord_6646269).sum := by decide
  have hdescent : baseEnd_6646269 < baseStart_6646269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646293 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_6646293 : Nat := 118140960795 + 6646293 * 2 ^ 59
def prefixEnd_6646293 : Nat := 4983230072969 + 3 ^ 40 * 6646293 * 2
def baseEnd_6646293 : Nat := 3412742879612870081771761

theorem tailTrace_6646293 : CollatzResearch.WordTrace tailWord_6646293 prefixEnd_6646293 3412742879612870081771761 := by
  unfold tailWord_6646293
  simp only [CollatzResearch.WordTrace]
  refine ⟨242410220510623032319863533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161606813673748688213242355 242410220510623032319863533)
  ·
    refine ⟨90903832691483637119948825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242410220510623032319863533 90903832691483637119948825)
    ·
      refine ⟨68177874518612727839961619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90903832691483637119948825 68177874518612727839961619)
      ·
        refine ⟨102266811777919091759942429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68177874518612727839961619 102266811777919091759942429)
        ·
          refine ⟨38350054416719659409978411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102266811777919091759942429 38350054416719659409978411)
          ·
            refine ⟨57525081625079489114967617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38350054416719659409978411 57525081625079489114967617)
            ·
              refine ⟨43143811218809616836225713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57525081625079489114967617 43143811218809616836225713)
              ·
                refine ⟨32357858414107212627169285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43143811218809616836225713 32357858414107212627169285)
                ·
                  refine ⟨6067098452645102367594241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32357858414107212627169285 6067098452645102367594241)
                  ·
                    refine ⟨4550323839483826775695681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067098452645102367594241 4550323839483826775695681)
                    ·
                      refine ⟨3412742879612870081771761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550323839483826775695681 3412742879612870081771761)
                      ·
                        rfl

theorem cell23_6646293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_6646293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646293 prefixEnd_6646293 := by exact prefixLift 6646293
  have htrace : WordTrace (prefixWord ++ tailWord_6646293) baseStart_6646293 baseEnd_6646293 := by
    simpa [prefixWord, tailWord_6646293, baseEnd_6646293] using wordTrace_append hprefix tailTrace_6646293
  have hstable : (prefixWord ++ tailWord_6646293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646293).length < 2 ^ (prefixWord ++ tailWord_6646293).sum := by decide
  have hdescent : baseEnd_6646293 < baseStart_6646293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646329 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_6646329 : Nat := 118140960795 + 6646329 * 2 ^ 59
def prefixEnd_6646329 : Nat := 4983230072969 + 3 ^ 40 * 6646329 * 2
def baseEnd_6646329 : Nat := 1137587121638810646973865

theorem tailTrace_6646329 : CollatzResearch.WordTrace tailWord_6646329 prefixEnd_6646329 1137587121638810646973865 := by
  unfold tailWord_6646329
  simp only [CollatzResearch.WordTrace]
  refine ⟨242411533538492610468174041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161607689025661740312116027 242411533538492610468174041)
  ·
    refine ⟨181808650153869457851130531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242411533538492610468174041 181808650153869457851130531)
    ·
      refine ⟨272712975230804186776695797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181808650153869457851130531 272712975230804186776695797)
      ·
        refine ⟨25566841427887892510315231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272712975230804186776695797 25566841427887892510315231)
        ·
          refine ⟨38350262141831838765472847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25566841427887892510315231 38350262141831838765472847)
          ·
            refine ⟨57525393212747758148209271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38350262141831838765472847 57525393212747758148209271)
            ·
              refine ⟨86288089819121637222313907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57525393212747758148209271 86288089819121637222313907)
              ·
                refine ⟨129432134728682455833470861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86288089819121637222313907 129432134728682455833470861)
                ·
                  refine ⟨48537050523255920937551573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129432134728682455833470861 48537050523255920937551573)
                  ·
                    refine ⟨1137587121638810646973865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48537050523255920937551573 1137587121638810646973865)
                    ·
                      rfl

theorem cell23_6646329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_6646329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646329 prefixEnd_6646329 := by exact prefixLift 6646329
  have htrace : WordTrace (prefixWord ++ tailWord_6646329) baseStart_6646329 baseEnd_6646329 := by
    simpa [prefixWord, tailWord_6646329, baseEnd_6646329] using wordTrace_append hprefix tailTrace_6646329
  have hstable : (prefixWord ++ tailWord_6646329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646329).length < 2 ^ (prefixWord ++ tailWord_6646329).sum := by decide
  have hdescent : baseEnd_6646329 < baseStart_6646329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646336 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2]
def baseStart_6646336 : Nat := 118140960795 + 6646336 * 2 ^ 59
def prefixEnd_6646336 : Nat := 4983230072969 + 3 ^ 40 * 6646336 * 2
def baseEnd_6646336 : Nat := 3412764959281013413534063

theorem tailTrace_6646336 : CollatzResearch.WordTrace tailWord_6646336 prefixEnd_6646336 3412764959281013413534063 := by
  unfold tailWord_6646336
  simp only [CollatzResearch.WordTrace]
  refine ⟨121205894424733625331839431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161607859232978167109119241 121205894424733625331839431)
  ·
    refine ⟨181808841637100437997759147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121205894424733625331839431 181808841637100437997759147)
    ·
      refine ⟨272713262455650656996638721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181808841637100437997759147 272713262455650656996638721)
      ·
        refine ⟨204534946841737992747479041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272713262455650656996638721 204534946841737992747479041)
        ·
          refine ⟨153401210131303494560609281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204534946841737992747479041 153401210131303494560609281)
          ·
            refine ⟨115050907598477620920456961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153401210131303494560609281 115050907598477620920456961)
            ·
              refine ⟨86288180698858215690342721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115050907598477620920456961 86288180698858215690342721)
              ·
                refine ⟨64716135524143661767757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86288180698858215690342721 64716135524143661767757041)
                ·
                  refine ⟨48537101643107746325817781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64716135524143661767757041 48537101643107746325817781)
                  ·
                    refine ⟨4550353279041351218045417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48537101643107746325817781 4550353279041351218045417)
                    ·
                      refine ⟨3412764959281013413534063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550353279041351218045417 3412764959281013413534063)
                      ·
                        rfl

theorem cell23_6646336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_6646336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646336 prefixEnd_6646336 := by exact prefixLift 6646336
  have htrace : WordTrace (prefixWord ++ tailWord_6646336) baseStart_6646336 baseEnd_6646336 := by
    simpa [prefixWord, tailWord_6646336, baseEnd_6646336] using wordTrace_append hprefix tailTrace_6646336
  have hstable : (prefixWord ++ tailWord_6646336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646336).length < 2 ^ (prefixWord ++ tailWord_6646336).sum := by decide
  have hdescent : baseEnd_6646336 < baseStart_6646336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646379 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_6646379 : Nat := 118140960795 + 6646379 * 2 ^ 59
def prefixEnd_6646379 : Nat := 4983230072969 + 3 ^ 40 * 6646379 * 2
def baseEnd_6646379 : Nat := 3412787038949156745296365

theorem tailTrace_6646379 : CollatzResearch.WordTrace tailWord_6646379 prefixEnd_6646379 3412787038949156745296365 := by
  unfold tailWord_6646379
  simp only [CollatzResearch.WordTrace]
  refine ⟨242413357188311469007494191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161608904792207646004996127 242413357188311469007494191)
  ·
    refine ⟨363620035782467203511241287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242413357188311469007494191 363620035782467203511241287)
    ·
      refine ⟨545430053673700805266861931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363620035782467203511241287 545430053673700805266861931)
      ·
        refine ⟨818145080510551207900292897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545430053673700805266861931 818145080510551207900292897)
        ·
          refine ⟨613608810382913405925219673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818145080510551207900292897 613608810382913405925219673)
          ·
            refine ⟨460206607787185054443914755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613608810382913405925219673 460206607787185054443914755)
            ·
              refine ⟨690309911680777581665872133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460206607787185054443914755 690309911680777581665872133)
              ·
                refine ⟨129433108440145796562351025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690309911680777581665872133 129433108440145796562351025)
                ·
                  refine ⟨97074831330109347421763269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129433108440145796562351025 97074831330109347421763269)
                  ·
                    refine ⟨18201530874395502641580613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97074831330109347421763269 18201530874395502641580613)
                    ·
                      refine ⟨3412787038949156745296365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18201530874395502641580613 3412787038949156745296365)
                      ·
                        rfl

theorem cell23_6646379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_6646379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646379 prefixEnd_6646379 := by exact prefixLift 6646379
  have htrace : WordTrace (prefixWord ++ tailWord_6646379) baseStart_6646379 baseEnd_6646379 := by
    simpa [prefixWord, tailWord_6646379, baseEnd_6646379] using wordTrace_append hprefix tailTrace_6646379
  have hstable : (prefixWord ++ tailWord_6646379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646379).length < 2 ^ (prefixWord ++ tailWord_6646379).sum := by decide
  have hdescent : baseEnd_6646379 < baseStart_6646379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_6646409 : Nat := 118140960795 + 6646409 * 2 ^ 59
def prefixEnd_6646409 : Nat := 4983230072969 + 3 ^ 40 * 6646409 * 2
def baseEnd_6646409 : Nat := 3412802443368791627921227

theorem tailTrace_6646409 : CollatzResearch.WordTrace tailWord_6646409 prefixEnd_6646409 3412802443368791627921227 := by
  unfold tailWord_6646409
  simp only [CollatzResearch.WordTrace]
  refine ⟨242414451378202784131086281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161609634252135189420724187 242414451378202784131086281)
  ·
    refine ⟨181810838533652088098314711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242414451378202784131086281 181810838533652088098314711)
    ·
      refine ⟨272716257800478132147472067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181810838533652088098314711 272716257800478132147472067)
      ·
        refine ⟨409074386700717198221208101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272716257800478132147472067 409074386700717198221208101)
        ·
          refine ⟨76701447506384474666476519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409074386700717198221208101 76701447506384474666476519)
          ·
            refine ⟨115052171259576711999714779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76701447506384474666476519 115052171259576711999714779)
            ·
              refine ⟨172578256889365067999572169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115052171259576711999714779 172578256889365067999572169)
              ·
                refine ⟨129433692667023800999679127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172578256889365067999572169 129433692667023800999679127)
                ·
                  refine ⟨194150539000535701499518691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129433692667023800999679127 194150539000535701499518691)
                  ·
                    refine ⟨291225808500803552249278037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194150539000535701499518691 291225808500803552249278037)
                    ·
                      refine ⟨3412802443368791627921227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291225808500803552249278037 3412802443368791627921227)
                      ·
                        rfl

theorem cell23_6646409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_6646409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646409 prefixEnd_6646409 := by exact prefixLift 6646409
  have htrace : WordTrace (prefixWord ++ tailWord_6646409) baseStart_6646409 baseEnd_6646409 := by
    simpa [prefixWord, tailWord_6646409, baseEnd_6646409] using wordTrace_append hprefix tailTrace_6646409
  have hstable : (prefixWord ++ tailWord_6646409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646409).length < 2 ^ (prefixWord ++ tailWord_6646409).sum := by decide
  have hdescent : baseEnd_6646409 < baseStart_6646409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646420 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6646420 : Nat := 118140960795 + 6646420 * 2 ^ 59
def prefixEnd_6646420 : Nat := 4983230072969 + 3 ^ 40 * 6646420 * 2
def baseEnd_6646420 : Nat := 3412808091655991084883677

theorem tailTrace_6646420 : CollatzResearch.WordTrace tailWord_6646420 prefixEnd_6646420 3412808091655991084883677 := by
  unfold tailWord_6646420
  simp only [CollatzResearch.WordTrace]
  refine ⟨121207426290581466504868357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161609901720775288673157809 121207426290581466504868357)
  ·
    refine ⟨22726392429484024969662817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121207426290581466504868357 22726392429484024969662817)
    ·
      refine ⟨17044794322113018727247113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22726392429484024969662817 17044794322113018727247113)
      ·
        refine ⟨12783595741584764045435335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17044794322113018727247113 12783595741584764045435335)
        ·
          refine ⟨19175393612377146068153003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783595741584764045435335 19175393612377146068153003)
          ·
            refine ⟨28763090418565719102229505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19175393612377146068153003 28763090418565719102229505)
            ·
              refine ⟨21572317813924289326672129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28763090418565719102229505 21572317813924289326672129)
              ·
                refine ⟨16179238360443216995004097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21572317813924289326672129 16179238360443216995004097)
                ·
                  refine ⟨12134428770332412746253073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16179238360443216995004097 12134428770332412746253073)
                  ·
                    refine ⟨9100821577749309559689805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12134428770332412746253073 9100821577749309559689805)
                    ·
                      refine ⟨3412808091655991084883677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100821577749309559689805 3412808091655991084883677)
                      ·
                        rfl

theorem cell23_6646420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6646420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646420 prefixEnd_6646420 := by exact prefixLift 6646420
  have htrace : WordTrace (prefixWord ++ tailWord_6646420) baseStart_6646420 baseEnd_6646420 := by
    simpa [prefixWord, tailWord_6646420, baseEnd_6646420] using wordTrace_append hprefix tailTrace_6646420
  have hstable : (prefixWord ++ tailWord_6646420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646420).length < 2 ^ (prefixWord ++ tailWord_6646420).sum := by decide
  have hdescent : baseEnd_6646420 < baseStart_6646420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646436 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_6646436 : Nat := 118140960795 + 6646436 * 2 ^ 59
def prefixEnd_6646436 : Nat := 4983230072969 + 3 ^ 40 * 6646436 * 2
def baseEnd_6646436 : Nat := 1137605435782154340761201

theorem tailTrace_6646436 : CollatzResearch.WordTrace tailWord_6646436 prefixEnd_6646436 1137605435782154340761201 := by
  unfold tailWord_6646436
  simp only [CollatzResearch.WordTrace]
  refine ⟨121207718074552483871159581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161610290766069978494879441 121207718074552483871159581)
  ·
    refine ⟨45452894277957181451684843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121207718074552483871159581 45452894277957181451684843)
    ·
      refine ⟨68179341416935772177527265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45452894277957181451684843 68179341416935772177527265)
      ·
        refine ⟨51134506062701829133145449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68179341416935772177527265 51134506062701829133145449)
        ·
          refine ⟨38350879547026371849859087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51134506062701829133145449 38350879547026371849859087)
          ·
            refine ⟨57526319320539557774788631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38350879547026371849859087 57526319320539557774788631)
            ·
              refine ⟨86289478980809336662182947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57526319320539557774788631 86289478980809336662182947)
              ·
                refine ⟨129434218471214004993274421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86289478980809336662182947 129434218471214004993274421)
                ·
                  refine ⟨12134457981676312968119477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129434218471214004993274421 12134457981676312968119477)
                  ·
                    refine ⟨1137605435782154340761201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12134457981676312968119477 1137605435782154340761201)
                    ·
                      rfl

theorem cell23_6646436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_6646436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646436 prefixEnd_6646436 := by exact prefixLift 6646436
  have htrace : WordTrace (prefixWord ++ tailWord_6646436) baseStart_6646436 baseEnd_6646436 := by
    simpa [prefixWord, tailWord_6646436, baseEnd_6646436] using wordTrace_append hprefix tailTrace_6646436
  have hstable : (prefixWord ++ tailWord_6646436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646436).length < 2 ^ (prefixWord ++ tailWord_6646436).sum := by decide
  have hdescent : baseEnd_6646436 < baseStart_6646436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646453 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6646453 : Nat := 118140960795 + 6646453 * 2 ^ 59
def prefixEnd_6646453 : Nat := 4983230072969 + 3 ^ 40 * 6646453 * 2
def baseEnd_6646453 : Nat := 1137608345505863151923675

theorem tailTrace_6646453 : CollatzResearch.WordTrace tailWord_6646453 prefixEnd_6646453 1137608345505863151923675 := by
  unfold tailWord_6646453
  simp only [CollatzResearch.WordTrace]
  refine ⟨242416056190043379645688013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161610704126695586430458675 242416056190043379645688013)
  ·
    refine ⟨90906021071266267367133005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242416056190043379645688013 90906021071266267367133005)
    ·
      refine ⟨34089757901724850262674877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90906021071266267367133005 34089757901724850262674877)
      ·
        refine ⟨12783659213146818848503079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34089757901724850262674877 12783659213146818848503079)
        ·
          refine ⟨19175488819720228272754619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783659213146818848503079 19175488819720228272754619)
          ·
            refine ⟨28763233229580342409131929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19175488819720228272754619 28763233229580342409131929)
            ·
              refine ⟨21572424922185256806848947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28763233229580342409131929 21572424922185256806848947)
              ·
                refine ⟨32358637383277885210273421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21572424922185256806848947 32358637383277885210273421)
                ·
                  refine ⟨12134489018729206953852533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32358637383277885210273421 12134489018729206953852533)
                  ·
                    refine ⟨1137608345505863151923675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12134489018729206953852533 1137608345505863151923675)
                    ·
                      rfl

theorem cell23_6646453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6646453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646453 prefixEnd_6646453 := by exact prefixLift 6646453
  have htrace : WordTrace (prefixWord ++ tailWord_6646453) baseStart_6646453 baseEnd_6646453 := by
    simpa [prefixWord, tailWord_6646453, baseEnd_6646453] using wordTrace_append hprefix tailTrace_6646453
  have hstable : (prefixWord ++ tailWord_6646453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646453).length < 2 ^ (prefixWord ++ tailWord_6646453).sum := by decide
  have hdescent : baseEnd_6646453 < baseStart_6646453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646454 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6646454 : Nat := 118140960795 + 6646454 * 2 ^ 59
def prefixEnd_6646454 : Nat := 4983230072969 + 3 ^ 40 * 6646454 * 2
def baseEnd_6646454 : Nat := 3412825549998243951858521

theorem tailTrace_6646454 : CollatzResearch.WordTrace tailWord_6646454 prefixEnd_6646454 3412825549998243951858521 := by
  unfold tailWord_6646454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151005791439984801029651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161610728442026504544316277 15151005791439984801029651)
  ·
    refine ⟨22726508687159977201544477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151005791439984801029651 22726508687159977201544477)
    ·
      refine ⟨8522440757684991450579179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22726508687159977201544477 8522440757684991450579179)
      ·
        refine ⟨12783661136527487175868769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522440757684991450579179 12783661136527487175868769)
        ·
          refine ⟨9587745852395615381901577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12783661136527487175868769 9587745852395615381901577)
          ·
            refine ⟨7190809389296711536426183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9587745852395615381901577 7190809389296711536426183)
            ·
              refine ⟨10786214083945067304639275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190809389296711536426183 10786214083945067304639275)
              ·
                refine ⟨16179321125917600956958913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10786214083945067304639275 16179321125917600956958913)
                ·
                  refine ⟨12134490844438200717719185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16179321125917600956958913 12134490844438200717719185)
                  ·
                    refine ⟨9100868133328650538289389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12134490844438200717719185 9100868133328650538289389)
                    ·
                      refine ⟨3412825549998243951858521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100868133328650538289389 3412825549998243951858521)
                      ·
                        rfl

theorem cell23_6646454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6646454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646454 prefixEnd_6646454 := by exact prefixLift 6646454
  have htrace : WordTrace (prefixWord ++ tailWord_6646454) baseStart_6646454 baseEnd_6646454 := by
    simpa [prefixWord, tailWord_6646454, baseEnd_6646454] using wordTrace_append hprefix tailTrace_6646454
  have hstable : (prefixWord ++ tailWord_6646454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646454).length < 2 ^ (prefixWord ++ tailWord_6646454).sum := by decide
  have hdescent : baseEnd_6646454 < baseStart_6646454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646510 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_6646510 : Nat := 118140960795 + 6646510 * 2 ^ 59
def prefixEnd_6646510 : Nat := 4983230072969 + 3 ^ 40 * 6646510 * 2
def baseEnd_6646510 : Nat := 3412854304914895732758263

theorem tailTrace_6646510 : CollatzResearch.WordTrace tailWord_6646510 prefixEnd_6646510 3412854304914895732758263 := by
  unfold tailWord_6646510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30302266893854609797564123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161612090100557918920341989 30302266893854609797564123)
  ·
    refine ⟨45453400340781914696346185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30302266893854609797564123 45453400340781914696346185)
    ·
      refine ⟨34090050255586436022259639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45453400340781914696346185 34090050255586436022259639)
      ·
        refine ⟨51135075383379654033389459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34090050255586436022259639 51135075383379654033389459)
        ·
          refine ⟨76702613075069481050084189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51135075383379654033389459 76702613075069481050084189)
          ·
            refine ⟨28763479903151055393781571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76702613075069481050084189 28763479903151055393781571)
            ·
              refine ⟨43145219854726583090672357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28763479903151055393781571 43145219854726583090672357)
              ·
                refine ⟨8089728722761234329501067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43145219854726583090672357 8089728722761234329501067)
                ·
                  refine ⟨12134593084141851494251601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8089728722761234329501067 12134593084141851494251601)
                  ·
                    refine ⟨9100944813106388620688701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12134593084141851494251601 9100944813106388620688701)
                    ·
                      refine ⟨3412854304914895732758263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100944813106388620688701 3412854304914895732758263)
                      ·
                        rfl

theorem cell23_6646510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_6646510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646510 prefixEnd_6646510 := by exact prefixLift 6646510
  have htrace : WordTrace (prefixWord ++ tailWord_6646510) baseStart_6646510 baseEnd_6646510 := by
    simpa [prefixWord, tailWord_6646510, baseEnd_6646510] using wordTrace_append hprefix tailTrace_6646510
  have hstable : (prefixWord ++ tailWord_6646510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646510).length < 2 ^ (prefixWord ++ tailWord_6646510).sum := by decide
  have hdescent : baseEnd_6646510 < baseStart_6646510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646524 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_6646524 : Nat := 118140960795 + 6646524 * 2 ^ 59
def prefixEnd_6646524 : Nat := 4983230072969 + 3 ^ 40 * 6646524 * 2
def baseEnd_6646524 : Nat := 3412861493644058677983199

theorem tailTrace_6646524 : CollatzResearch.WordTrace tailWord_6646524 prefixEnd_6646524 3412861493644058677983199 := by
  unfold tailWord_6646524
  simp only [CollatzResearch.WordTrace]
  refine ⟨121209322886393079385761313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161612430515190772514348417 121209322886393079385761313)
  ·
    refine ⟨90906992164794809539320985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121209322886393079385761313 90906992164794809539320985)
    ·
      refine ⟨68180244123596107154490739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90906992164794809539320985 68180244123596107154490739)
      ·
        refine ⟨102270366185394160731736109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68180244123596107154490739 102270366185394160731736109)
        ·
          refine ⟨38351387319522810274401041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102270366185394160731736109 38351387319522810274401041)
          ·
            refine ⟨28763540489642107705800781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38351387319522810274401041 28763540489642107705800781)
            ·
              refine ⟨10786327683615790389675293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28763540489642107705800781 10786327683615790389675293)
              ·
                refine ⟨4044872881355921396128235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10786327683615790389675293 4044872881355921396128235)
                ·
                  refine ⟨6067309322033882094192353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044872881355921396128235 6067309322033882094192353)
                  ·
                    refine ⟨4550481991525411570644265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067309322033882094192353 4550481991525411570644265)
                    ·
                      refine ⟨3412861493644058677983199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550481991525411570644265 3412861493644058677983199)
                      ·
                        rfl

theorem cell23_6646524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_6646524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646524 prefixEnd_6646524 := by exact prefixLift 6646524
  have htrace : WordTrace (prefixWord ++ tailWord_6646524) baseStart_6646524 baseEnd_6646524 := by
    simpa [prefixWord, tailWord_6646524, baseEnd_6646524] using wordTrace_append hprefix tailTrace_6646524
  have hstable : (prefixWord ++ tailWord_6646524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646524).length < 2 ^ (prefixWord ++ tailWord_6646524).sum := by decide
  have hdescent : baseEnd_6646524 < baseStart_6646524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646540 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_6646540 : Nat := 118140960795 + 6646540 * 2 ^ 59
def prefixEnd_6646540 : Nat := 4983230072969 + 3 ^ 40 * 6646540 * 2
def baseEnd_6646540 : Nat := 3412869709334530615383125

theorem tailTrace_6646540 : CollatzResearch.WordTrace tailWord_6646540 prefixEnd_6646540 3412869709334530615383125 := by
  unfold tailWord_6646540
  simp only [CollatzResearch.WordTrace]
  refine ⟨121209614670364096752052537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161612819560485462336070049 121209614670364096752052537)
  ·
    refine ⟨90907211002773072564039403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121209614670364096752052537 90907211002773072564039403)
    ·
      refine ⟨136360816504159608846059105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90907211002773072564039403 136360816504159608846059105)
      ·
        refine ⟨102270612378119706634544329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136360816504159608846059105 102270612378119706634544329)
        ·
          refine ⟨76702959283589779975908247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102270612378119706634544329 76702959283589779975908247)
          ·
            refine ⟨115054438925384669963862371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76702959283589779975908247 115054438925384669963862371)
            ·
              refine ⟨172581658388077004945793557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115054438925384669963862371 172581658388077004945793557)
              ·
                refine ⟨8089765236941109606834073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172581658388077004945793557 8089765236941109606834073)
                ·
                  refine ⟨6067323927705832205125555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8089765236941109606834073 6067323927705832205125555)
                  ·
                    refine ⟨9100985891558748307688333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067323927705832205125555 9100985891558748307688333)
                    ·
                      refine ⟨3412869709334530615383125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100985891558748307688333 3412869709334530615383125)
                      ·
                        rfl

theorem cell23_6646540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_6646540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646540 prefixEnd_6646540 := by exact prefixLift 6646540
  have htrace : WordTrace (prefixWord ++ tailWord_6646540) baseStart_6646540 baseEnd_6646540 := by
    simpa [prefixWord, tailWord_6646540, baseEnd_6646540] using wordTrace_append hprefix tailTrace_6646540
  have hstable : (prefixWord ++ tailWord_6646540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646540).length < 2 ^ (prefixWord ++ tailWord_6646540).sum := by decide
  have hdescent : baseEnd_6646540 < baseStart_6646540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646620 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 7]
def baseStart_6646620 : Nat := 118140960795 + 6646620 * 2 ^ 59
def prefixEnd_6646620 : Nat := 4983230072969 + 3 ^ 40 * 6646620 * 2
def baseEnd_6646620 : Nat := 379212309754098922486973

theorem tailTrace_6646620 : CollatzResearch.WordTrace tailWord_6646620 prefixEnd_6646620 379212309754098922486973 := by
  unfold tailWord_6646620
  simp only [CollatzResearch.WordTrace]
  refine ⟨121211073590219183583508657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161614764786958911444678209 121211073590219183583508657)
  ·
    refine ⟨90908305192664387687631493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121211073590219183583508657 90908305192664387687631493)
    ·
      refine ⟨17045307223624572691430905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90908305192664387687631493 17045307223624572691430905)
      ·
        refine ⟨12783980417718429518573179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17045307223624572691430905 12783980417718429518573179)
        ·
          refine ⟨19175970626577644277859769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783980417718429518573179 19175970626577644277859769)
          ·
            refine ⟨14381977969933233208394827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19175970626577644277859769 14381977969933233208394827)
            ·
              refine ⟨21572966954899849812592241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14381977969933233208394827 21572966954899849812592241)
              ·
                refine ⟨16179725216174887359444181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21572966954899849812592241 16179725216174887359444181)
                ·
                  refine ⟨379212309754098922486973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16179725216174887359444181 379212309754098922486973)
                  ·
                    rfl

theorem cell23_6646620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_6646620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646620 prefixEnd_6646620 := by exact prefixLift 6646620
  have htrace : WordTrace (prefixWord ++ tailWord_6646620) baseStart_6646620 baseEnd_6646620 := by
    simpa [prefixWord, tailWord_6646620, baseEnd_6646620] using wordTrace_append hprefix tailTrace_6646620
  have hstable : (prefixWord ++ tailWord_6646620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646620).length < 2 ^ (prefixWord ++ tailWord_6646620).sum := by decide
  have hdescent : baseEnd_6646620 < baseStart_6646620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646714 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_6646714 : Nat := 118140960795 + 6646714 * 2 ^ 59
def prefixEnd_6646714 : Nat := 4983230072969 + 3 ^ 40 * 6646714 * 2
def baseEnd_6646714 : Nat := 1137653018322804311535775

theorem tailTrace_6646714 : CollatzResearch.WordTrace tailWord_6646714 prefixEnd_6646714 1137653018322804311535775 := by
  unfold tailWord_6646714
  simp only [CollatzResearch.WordTrace]
  refine ⟨60606393910524455305234799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161617050428065214147292797 60606393910524455305234799)
  ·
    refine ⟨90909590865786682957852199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60606393910524455305234799 90909590865786682957852199)
    ·
      refine ⟨136364386298680024436778299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90909590865786682957852199 136364386298680024436778299)
      ·
        refine ⟨204546579448020036655167449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136364386298680024436778299 204546579448020036655167449)
        ·
          refine ⟨153409934586015027491375587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204546579448020036655167449 153409934586015027491375587)
          ·
            refine ⟨230114901879022541237063381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153409934586015027491375587 230114901879022541237063381)
            ·
              refine ⟨5393318012789590810243673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230114901879022541237063381 5393318012789590810243673)
              ·
                refine ⟨4044988509592193107682755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393318012789590810243673 4044988509592193107682755)
                ·
                  refine ⟨6067482764388289661524133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044988509592193107682755 6067482764388289661524133)
                  ·
                    refine ⟨1137653018322804311535775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6067482764388289661524133 1137653018322804311535775)
                    ·
                      rfl

theorem cell23_6646714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_6646714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646714 prefixEnd_6646714 := by exact prefixLift 6646714
  have htrace : WordTrace (prefixWord ++ tailWord_6646714) baseStart_6646714 baseEnd_6646714 := by
    simpa [prefixWord, tailWord_6646714, baseEnd_6646714] using wordTrace_append hprefix tailTrace_6646714
  have hstable : (prefixWord ++ tailWord_6646714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646714).length < 2 ^ (prefixWord ++ tailWord_6646714).sum := by decide
  have hdescent : baseEnd_6646714 < baseStart_6646714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646723 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 5, 5]
def baseStart_6646723 : Nat := 118140960795 + 6646723 * 2 ^ 59
def prefixEnd_6646723 : Nat := 4983230072969 + 3 ^ 40 * 6646723 * 2
def baseEnd_6646723 : Nat := 1137654558764767799798261

theorem tailTrace_6646723 : CollatzResearch.WordTrace tailWord_6646723 prefixEnd_6646723 1137654558764767799798261 := by
  unfold tailWord_6646723
  simp only [CollatzResearch.WordTrace]
  refine ⟨242425903899065215758016823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161617269266043477172011215 242425903899065215758016823)
  ·
    refine ⟨363638855848597823637025235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242425903899065215758016823 363638855848597823637025235)
    ·
      refine ⟨545458283772896735455537853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363638855848597823637025235 545458283772896735455537853)
      ·
        refine ⟨204546856414836275795826695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545458283772896735455537853 204546856414836275795826695)
        ·
          refine ⟨306820284622254413693740043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204546856414836275795826695 306820284622254413693740043)
          ·
            refine ⟨460230426933381620540610065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306820284622254413693740043 460230426933381620540610065)
            ·
              refine ⟨345172820200036215405457549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460230426933381620540610065 345172820200036215405457549)
              ·
                refine ⟨129439807575013580777046581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345172820200036215405457549 129439807575013580777046581)
                ·
                  refine ⟨12134981960157523197848117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129439807575013580777046581 12134981960157523197848117)
                  ·
                    refine ⟨1137654558764767799798261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12134981960157523197848117 1137654558764767799798261)
                    ·
                      rfl

theorem cell23_6646723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].length) (baseStart_6646723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646723 prefixEnd_6646723 := by exact prefixLift 6646723
  have htrace : WordTrace (prefixWord ++ tailWord_6646723) baseStart_6646723 baseEnd_6646723 := by
    simpa [prefixWord, tailWord_6646723, baseEnd_6646723] using wordTrace_append hprefix tailTrace_6646723
  have hstable : (prefixWord ++ tailWord_6646723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646723).length < 2 ^ (prefixWord ++ tailWord_6646723).sum := by decide
  have hdescent : baseEnd_6646723 < baseStart_6646723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_6646793 : Nat := 118140960795 + 6646793 * 2 ^ 59
def prefixEnd_6646793 : Nat := 4983230072969 + 3 ^ 40 * 6646793 * 2
def baseEnd_6646793 : Nat := 3412999619940118125519461

theorem tailTrace_6646793 : CollatzResearch.WordTrace tailWord_6646793 prefixEnd_6646793 3412999619940118125519461 := by
  unfold tailWord_6646793
  simp only [CollatzResearch.WordTrace]
  refine ⟨242428457008811617713065033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161618971339207745142043355 242428457008811617713065033)
  ·
    refine ⟨181821342756608713284798775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242428457008811617713065033 181821342756608713284798775)
    ·
      refine ⟨272732014134913069927198163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181821342756608713284798775 272732014134913069927198163)
      ·
        refine ⟨409098021202369604890797245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272732014134913069927198163 409098021202369604890797245)
        ·
          refine ⟨153411757950888601834048967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409098021202369604890797245 153411757950888601834048967)
          ·
            refine ⟨230117636926332902751073451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153411757950888601834048967 230117636926332902751073451)
            ·
              refine ⟨345176455389499354126610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230117636926332902751073451 345176455389499354126610177)
              ·
                refine ⟨258882341542124515594957633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345176455389499354126610177 258882341542124515594957633)
                ·
                  refine ⟨194161756156593386696218225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258882341542124515594957633 194161756156593386696218225)
                  ·
                    refine ⟨145621317117445040022163669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194161756156593386696218225 145621317117445040022163669)
                    ·
                      refine ⟨3412999619940118125519461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145621317117445040022163669 3412999619940118125519461)
                      ·
                        rfl

theorem cell23_6646793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_6646793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646793 prefixEnd_6646793 := by exact prefixLift 6646793
  have htrace : WordTrace (prefixWord ++ tailWord_6646793) baseStart_6646793 baseEnd_6646793 := by
    simpa [prefixWord, tailWord_6646793, baseEnd_6646793] using wordTrace_append hprefix tailTrace_6646793
  have hstable : (prefixWord ++ tailWord_6646793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646793).length < 2 ^ (prefixWord ++ tailWord_6646793).sum := by decide
  have hdescent : baseEnd_6646793 < baseStart_6646793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646794 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_6646794 : Nat := 118140960795 + 6646794 * 2 ^ 59
def prefixEnd_6646794 : Nat := 4983230072969 + 3 ^ 40 * 6646794 * 2
def baseEnd_6646794 : Nat := 3413000133420772621606957

theorem tailTrace_6646794 : CollatzResearch.WordTrace tailWord_6646794 prefixEnd_6646794 3413000133420772621606957 := by
  unfold tailWord_6646794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60607123370451998720962859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161618995654538663255900957 60607123370451998720962859)
  ·
    refine ⟨90910685055677998081444289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60607123370451998720962859 90910685055677998081444289)
    ·
      refine ⟨68183013791758498561083217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90910685055677998081444289 68183013791758498561083217)
      ·
        refine ⟨51137260343818873920812413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68183013791758498561083217 51137260343818873920812413)
        ·
          refine ⟨19176472628932077720304655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51137260343818873920812413 19176472628932077720304655)
          ·
            refine ⟨28764708943398116580456983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19176472628932077720304655 28764708943398116580456983)
            ·
              refine ⟨43147063415097174870685475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28764708943398116580456983 43147063415097174870685475)
              ·
                refine ⟨64720595122645762306028213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43147063415097174870685475 64720595122645762306028213)
                ·
                  refine ⟨6067555792748040216190145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64720595122645762306028213 6067555792748040216190145)
                  ·
                    refine ⟨4550666844561030162142609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067555792748040216190145 4550666844561030162142609)
                    ·
                      refine ⟨3413000133420772621606957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550666844561030162142609 3413000133420772621606957)
                      ·
                        rfl

theorem cell23_6646794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_6646794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646794 prefixEnd_6646794 := by exact prefixLift 6646794
  have htrace : WordTrace (prefixWord ++ tailWord_6646794) baseStart_6646794 baseEnd_6646794 := by
    simpa [prefixWord, tailWord_6646794, baseEnd_6646794] using wordTrace_append hprefix tailTrace_6646794
  have hstable : (prefixWord ++ tailWord_6646794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646794).length < 2 ^ (prefixWord ++ tailWord_6646794).sum := by decide
  have hdescent : baseEnd_6646794 < baseStart_6646794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646807 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6646807 : Nat := 118140960795 + 6646807 * 2 ^ 59
def prefixEnd_6646807 : Nat := 4983230072969 + 3 ^ 40 * 6646807 * 2
def baseEnd_6646807 : Nat := 3413006808669281070744397

theorem tailTrace_6646807 : CollatzResearch.WordTrace tailWord_6646807 prefixEnd_6646807 3413006808669281070744397 := by
  unfold tailWord_6646807
  simp only [CollatzResearch.WordTrace]
  refine ⟨242428967630760898104074675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161619311753840598736049783 242428967630760898104074675)
  ·
    refine ⟨363643451446141347156112013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242428967630760898104074675 363643451446141347156112013)
    ·
      refine ⟨136366294292303005183542005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363643451446141347156112013 136366294292303005183542005)
      ·
        refine ⟨12784340089903406735957063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136366294292303005183542005 12784340089903406735957063)
        ·
          refine ⟨19176510134855110103935595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784340089903406735957063 19176510134855110103935595)
          ·
            refine ⟨28764765202282665155903393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19176510134855110103935595 28764765202282665155903393)
            ·
              refine ⟨21573573901711998866927545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28764765202282665155903393 21573573901711998866927545)
              ·
                refine ⟨16180180426283999150195659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21573573901711998866927545 16180180426283999150195659)
                ·
                  refine ⟨24270270639425998725293489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16180180426283999150195659 24270270639425998725293489)
                  ·
                    refine ⟨18202702979569499043970117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24270270639425998725293489 18202702979569499043970117)
                    ·
                      refine ⟨3413006808669281070744397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18202702979569499043970117 3413006808669281070744397)
                      ·
                        rfl

theorem cell23_6646807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6646807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646807 prefixEnd_6646807 := by exact prefixLift 6646807
  have htrace : WordTrace (prefixWord ++ tailWord_6646807) baseStart_6646807 baseEnd_6646807 := by
    simpa [prefixWord, tailWord_6646807, baseEnd_6646807] using wordTrace_append hprefix tailTrace_6646807
  have hstable : (prefixWord ++ tailWord_6646807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646807).length < 2 ^ (prefixWord ++ tailWord_6646807).sum := by decide
  have hdescent : baseEnd_6646807 < baseStart_6646807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646827 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 3]
def baseStart_6646827 : Nat := 118140960795 + 6646827 * 2 ^ 59
def prefixEnd_6646827 : Nat := 4983230072969 + 3 ^ 40 * 6646827 * 2
def baseEnd_6646827 : Nat := 3413017078282370992494305

theorem tailTrace_6646827 : CollatzResearch.WordTrace tailWord_6646827 prefixEnd_6646827 3413017078282370992494305 := by
  unfold tailWord_6646827
  simp only [CollatzResearch.WordTrace]
  refine ⟨242429697090688441519802735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161619798060458961013201823 242429697090688441519802735)
  ·
    refine ⟨363644545636032662279704103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242429697090688441519802735 363644545636032662279704103)
    ·
      refine ⟨545466818454048993419556155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363644545636032662279704103 545466818454048993419556155)
      ·
        refine ⟨818200227681073490129334233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545466818454048993419556155 818200227681073490129334233)
        ·
          refine ⟨613650170760805117597000675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818200227681073490129334233 613650170760805117597000675)
          ·
            refine ⟨920475256141207676395501013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613650170760805117597000675 920475256141207676395501013)
            ·
              refine ⟨21573638815809554915519555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 920475256141207676395501013 21573638815809554915519555)
              ·
                refine ⟨32360458223714332373279333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21573638815809554915519555 32360458223714332373279333)
                ·
                  refine ⟨6067585916946437319989875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32360458223714332373279333 6067585916946437319989875)
                  ·
                    refine ⟨9101378875419655979984813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067585916946437319989875 9101378875419655979984813)
                    ·
                      refine ⟨3413017078282370992494305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101378875419655979984813 3413017078282370992494305)
                      ·
                        rfl

theorem cell23_6646827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 3].length) (baseStart_6646827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646827 prefixEnd_6646827 := by exact prefixLift 6646827
  have htrace : WordTrace (prefixWord ++ tailWord_6646827) baseStart_6646827 baseEnd_6646827 := by
    simpa [prefixWord, tailWord_6646827, baseEnd_6646827] using wordTrace_append hprefix tailTrace_6646827
  have hstable : (prefixWord ++ tailWord_6646827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646827).length < 2 ^ (prefixWord ++ tailWord_6646827).sum := by decide
  have hdescent : baseEnd_6646827 < baseStart_6646827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646844 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_6646844 : Nat := 118140960795 + 6646844 * 2 ^ 59
def prefixEnd_6646844 : Nat := 4983230072969 + 3 ^ 40 * 6646844 * 2
def baseEnd_6646844 : Nat := 3413025807453497425981727

theorem tailTrace_6646844 : CollatzResearch.WordTrace tailWord_6646844 prefixEnd_6646844 3413025807453497425981727 := by
  unfold tailWord_6646844
  simp only [CollatzResearch.WordTrace]
  refine ⟨121215158565813426711585793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161620211421084568948781057 121215158565813426711585793)
  ·
    refine ⟨90911368924360070033689345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121215158565813426711585793 90911368924360070033689345)
    ·
      refine ⟨68183526693270052525267009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90911368924360070033689345 68183526693270052525267009)
      ·
        refine ⟨51137645019952539393950257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68183526693270052525267009 51137645019952539393950257)
        ·
          refine ⟨38353233764964404545462693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51137645019952539393950257 38353233764964404545462693)
          ·
            refine ⟨7191231330930825852274255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38353233764964404545462693 7191231330930825852274255)
            ·
              refine ⟨10786846996396238778411383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191231330930825852274255 10786846996396238778411383)
              ·
                refine ⟨16180270494594358167617075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10786846996396238778411383 16180270494594358167617075)
                ·
                  refine ⟨24270405741891537251425613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16180270494594358167617075 24270405741891537251425613)
                  ·
                    refine ⟨9101402153209326469284605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24270405741891537251425613 9101402153209326469284605)
                    ·
                      refine ⟨3413025807453497425981727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101402153209326469284605 3413025807453497425981727)
                      ·
                        rfl

theorem cell23_6646844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_6646844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646844 prefixEnd_6646844 := by exact prefixLift 6646844
  have htrace : WordTrace (prefixWord ++ tailWord_6646844) baseStart_6646844 baseEnd_6646844 := by
    simpa [prefixWord, tailWord_6646844, baseEnd_6646844] using wordTrace_append hprefix tailTrace_6646844
  have hstable : (prefixWord ++ tailWord_6646844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646844).length < 2 ^ (prefixWord ++ tailWord_6646844).sum := by decide
  have hdescent : baseEnd_6646844 < baseStart_6646844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646878 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6646878 : Nat := 118140960795 + 6646878 * 2 ^ 59
def prefixEnd_6646878 : Nat := 4983230072969 + 3 ^ 40 * 6646878 * 2
def baseEnd_6646878 : Nat := 3413043265795750292956571

theorem tailTrace_6646878 : CollatzResearch.WordTrace tailWord_6646878 prefixEnd_6646878 3413043265795750292956571 := by
  unfold tailWord_6646878
  simp only [CollatzResearch.WordTrace]
  refine ⟨30303944651687959653738661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161621038142335784819939525 30303944651687959653738661)
  ·
    refine ⟨5681989622191492435075999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30303944651687959653738661 5681989622191492435075999)
    ·
      refine ⟨8522984433287238652613999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681989622191492435075999 8522984433287238652613999)
      ·
        refine ⟨12784476649930857978920999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522984433287238652613999 12784476649930857978920999)
        ·
          refine ⟨19176714974896286968381499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784476649930857978920999 19176714974896286968381499)
          ·
            refine ⟨28765072462344430452572249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19176714974896286968381499 28765072462344430452572249)
            ·
              refine ⟨21573804346758322839429187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28765072462344430452572249 21573804346758322839429187)
              ·
                refine ⟨32360706520137484259143781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21573804346758322839429187 32360706520137484259143781)
                ·
                  refine ⟨6067632472525778298589459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32360706520137484259143781 6067632472525778298589459)
                  ·
                    refine ⟨9101448708788667447884189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067632472525778298589459 9101448708788667447884189)
                    ·
                      refine ⟨3413043265795750292956571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101448708788667447884189 3413043265795750292956571)
                      ·
                        rfl

theorem cell23_6646878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6646878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646878 prefixEnd_6646878 := by exact prefixLift 6646878
  have htrace : WordTrace (prefixWord ++ tailWord_6646878) baseStart_6646878 baseEnd_6646878 := by
    simpa [prefixWord, tailWord_6646878, baseEnd_6646878] using wordTrace_append hprefix tailTrace_6646878
  have hstable : (prefixWord ++ tailWord_6646878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646878).length < 2 ^ (prefixWord ++ tailWord_6646878).sum := by decide
  have hdescent : baseEnd_6646878 < baseStart_6646878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646960 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_6646960 : Nat := 118140960795 + 6646960 * 2 ^ 59
def prefixEnd_6646960 : Nat := 4983230072969 + 3 ^ 40 * 6646960 * 2
def baseEnd_6646960 : Nat := 3413085371209418972131193

theorem tailTrace_6646960 : CollatzResearch.WordTrace tailWord_6646960 prefixEnd_6646960 3413085371209418972131193 := by
  unfold tailWord_6646960
  simp only [CollatzResearch.WordTrace]
  refine ⟨121217273999603302617197167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161623031999471070156262889 121217273999603302617197167)
  ·
    refine ⟨181825910999404953925795751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121217273999603302617197167 181825910999404953925795751)
    ·
      refine ⟨272738866499107430888693627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181825910999404953925795751 272738866499107430888693627)
      ·
        refine ⟨409108299748661146333040441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272738866499107430888693627 409108299748661146333040441)
        ·
          refine ⟨306831224811495859749780331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409108299748661146333040441 306831224811495859749780331)
          ·
            refine ⟨460246837217243789624670497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306831224811495859749780331 460246837217243789624670497)
            ·
              refine ⟨345185127912932842218502873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460246837217243789624670497 345185127912932842218502873)
              ·
                refine ⟨258888845934699631663877155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345185127912932842218502873 258888845934699631663877155)
                ·
                  refine ⟨388333268902049447495815733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258888845934699631663877155 388333268902049447495815733)
                  ·
                    refine ⟨36406243959567135702732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 388333268902049447495815733 36406243959567135702732725)
                    ·
                      refine ⟨3413085371209418972131193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36406243959567135702732725 3413085371209418972131193)
                      ·
                        rfl

theorem cell23_6646960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_6646960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646960 prefixEnd_6646960 := by exact prefixLift 6646960
  have htrace : WordTrace (prefixWord ++ tailWord_6646960) baseStart_6646960 baseEnd_6646960 := by
    simpa [prefixWord, tailWord_6646960, baseEnd_6646960] using wordTrace_append hprefix tailTrace_6646960
  have hstable : (prefixWord ++ tailWord_6646960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646960).length < 2 ^ (prefixWord ++ tailWord_6646960).sum := by decide
  have hdescent : baseEnd_6646960 < baseStart_6646960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646974 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6646974 : Nat := 118140960795 + 6646974 * 2 ^ 59
def prefixEnd_6646974 : Nat := 4983230072969 + 3 ^ 40 * 6646974 * 2
def baseEnd_6646974 : Nat := 3413092559938581917356129

theorem tailTrace_6646974 : CollatzResearch.WordTrace tailWord_6646974 prefixEnd_6646974 3413092559938581917356129 := by
  unfold tailWord_6646974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30304382327644485703175497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161623372414103923750269317 30304382327644485703175497)
  ·
    refine ⟨22728286745733364277381623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30304382327644485703175497 22728286745733364277381623)
    ·
      refine ⟨34092430118600046416072435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22728286745733364277381623 34092430118600046416072435)
      ·
        refine ⟨51138645177900069624108653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34092430118600046416072435 51138645177900069624108653)
        ·
          refine ⟨19176991941712526109040745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51138645177900069624108653 19176991941712526109040745)
          ·
            refine ⟨14382743956284394581780559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19176991941712526109040745 14382743956284394581780559)
            ·
              refine ⟨21574115934426591872670839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382743956284394581780559 21574115934426591872670839)
              ·
                refine ⟨32361173901639887809006259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21574115934426591872670839 32361173901639887809006259)
                ·
                  refine ⟨48541760852459831713509389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32361173901639887809006259 48541760852459831713509389)
                  ·
                    refine ⟨18203160319672436892566021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48541760852459831713509389 18203160319672436892566021)
                    ·
                      refine ⟨3413092559938581917356129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18203160319672436892566021 3413092559938581917356129)
                      ·
                        rfl

theorem cell23_6646974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6646974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646974 prefixEnd_6646974 := by exact prefixLift 6646974
  have htrace : WordTrace (prefixWord ++ tailWord_6646974) baseStart_6646974 baseEnd_6646974 := by
    simpa [prefixWord, tailWord_6646974, baseEnd_6646974] using wordTrace_append hprefix tailTrace_6646974
  have hstable : (prefixWord ++ tailWord_6646974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646974).length < 2 ^ (prefixWord ++ tailWord_6646974).sum := by decide
  have hdescent : baseEnd_6646974 < baseStart_6646974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6646994 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6646994 : Nat := 118140960795 + 6646994 * 2 ^ 59
def prefixEnd_6646994 : Nat := 4983230072969 + 3 ^ 40 * 6646994 * 2
def baseEnd_6646994 : Nat := 3413102829551671839106037

theorem tailTrace_6646994 : CollatzResearch.WordTrace tailWord_6646994 prefixEnd_6646994 3413102829551671839106037 := by
  unfold tailWord_6646994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60608947020270857260283009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161623858720722286027421357 60608947020270857260283009)
  ·
    refine ⟨45456710265203142945212257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60608947020270857260283009 45456710265203142945212257)
    ·
      refine ⟨34092532698902357208909193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45456710265203142945212257 34092532698902357208909193)
      ·
        refine ⟨25569399524176767906681895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34092532698902357208909193 25569399524176767906681895)
        ·
          refine ⟨38354099286265151860022843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25569399524176767906681895 38354099286265151860022843)
          ·
            refine ⟨57531148929397727790034265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38354099286265151860022843 57531148929397727790034265)
            ·
              refine ⟨43148361697048295842525699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57531148929397727790034265 43148361697048295842525699)
              ·
                refine ⟨64722542545572443763788549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43148361697048295842525699 64722542545572443763788549)
                ·
                  refine ⟨12135476727294833205710353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64722542545572443763788549 12135476727294833205710353)
                  ·
                    refine ⟨9101607545471124904282765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12135476727294833205710353 9101607545471124904282765)
                    ·
                      refine ⟨3413102829551671839106037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101607545471124904282765 3413102829551671839106037)
                      ·
                        rfl

theorem cell23_6646994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6646994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6646994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6646994 prefixEnd_6646994 := by exact prefixLift 6646994
  have htrace : WordTrace (prefixWord ++ tailWord_6646994) baseStart_6646994 baseEnd_6646994 := by
    simpa [prefixWord, tailWord_6646994, baseEnd_6646994] using wordTrace_append hprefix tailTrace_6646994
  have hstable : (prefixWord ++ tailWord_6646994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6646994).length < 2 ^ (prefixWord ++ tailWord_6646994).sum := by decide
  have hdescent : baseEnd_6646994 < baseStart_6646994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6646994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647034 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_6647034 : Nat := 118140960795 + 6647034 * 2 ^ 59
def prefixEnd_6647034 : Nat := 4983230072969 + 3 ^ 40 * 6647034 * 2
def baseEnd_6647034 : Nat := 3413123368777851682605853

theorem tailTrace_6647034 : CollatzResearch.WordTrace tailWord_6647034 prefixEnd_6647034 3413123368777851682605853 := by
  unfold tailWord_6647034
  simp only [CollatzResearch.WordTrace]
  refine ⟨60609311750234628968147039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161624831333959010581725437 60609311750234628968147039)
  ·
    refine ⟨90913967625351943452220559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60609311750234628968147039 90913967625351943452220559)
    ·
      refine ⟨136370951438027915178330839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90913967625351943452220559 136370951438027915178330839)
      ·
        refine ⟨204556427157041872767496259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136370951438027915178330839 204556427157041872767496259)
        ·
          refine ⟨306834640735562809151244389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204556427157041872767496259 306834640735562809151244389)
          ·
            refine ⟨57531495137918026715858323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306834640735562809151244389 57531495137918026715858323)
            ·
              refine ⟨86297242706877040073787485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57531495137918026715858323 86297242706877040073787485)
              ·
                refine ⟨32361466015078890027670307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86297242706877040073787485 32361466015078890027670307)
                ·
                  refine ⟨48542199022618335041505461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32361466015078890027670307 48542199022618335041505461)
                  ·
                    refine ⟨4550831158370468910141137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48542199022618335041505461 4550831158370468910141137)
                    ·
                      refine ⟨3413123368777851682605853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550831158370468910141137 3413123368777851682605853)
                      ·
                        rfl

theorem cell23_6647034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_6647034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647034 prefixEnd_6647034 := by exact prefixLift 6647034
  have htrace : WordTrace (prefixWord ++ tailWord_6647034) baseStart_6647034 baseEnd_6647034 := by
    simpa [prefixWord, tailWord_6647034, baseEnd_6647034] using wordTrace_append hprefix tailTrace_6647034
  have hstable : (prefixWord ++ tailWord_6647034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647034).length < 2 ^ (prefixWord ++ tailWord_6647034).sum := by decide
  have hdescent : baseEnd_6647034 < baseStart_6647034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647051 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 2, 3, 2]
def baseStart_6647051 : Nat := 118140960795 + 6647051 * 2 ^ 59
def prefixEnd_6647051 : Nat := 4983230072969 + 3 ^ 40 * 6647051 * 2
def baseEnd_6647051 : Nat := 3413132097948978116093275

theorem tailTrace_6647051 : CollatzResearch.WordTrace tailWord_6647051 prefixEnd_6647051 3413132097948978116093275 := by
  unfold tailWord_6647051
  simp only [CollatzResearch.WordTrace]
  refine ⟨242437867041876927775957007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161625244694584618517304671 242437867041876927775957007)
  ·
    refine ⟨363656800562815391663935511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242437867041876927775957007 363656800562815391663935511)
    ·
      refine ⟨545485200844223087495903267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363656800562815391663935511 545485200844223087495903267)
      ·
        refine ⟨818227801266334631243854901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545485200844223087495903267 818227801266334631243854901)
        ·
          refine ⟨76708856368718871679111397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 818227801266334631243854901 76708856368718871679111397)
          ·
            refine ⟨14382910569134788439833387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76708856368718871679111397 14382910569134788439833387)
            ·
              refine ⟨21574365853702182659750081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382910569134788439833387 21574365853702182659750081)
              ·
                refine ⟨16180774390276636994812561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21574365853702182659750081 16180774390276636994812561)
                ·
                  refine ⟨12135580792707477746109421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16180774390276636994812561 12135580792707477746109421)
                  ·
                    refine ⟨4550842797265304154791033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12135580792707477746109421 4550842797265304154791033)
                    ·
                      refine ⟨3413132097948978116093275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550842797265304154791033 3413132097948978116093275)
                      ·
                        rfl

theorem cell23_6647051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3, 2].length) (baseStart_6647051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647051 prefixEnd_6647051 := by exact prefixLift 6647051
  have htrace : WordTrace (prefixWord ++ tailWord_6647051) baseStart_6647051 baseEnd_6647051 := by
    simpa [prefixWord, tailWord_6647051, baseEnd_6647051] using wordTrace_append hprefix tailTrace_6647051
  have hstable : (prefixWord ++ tailWord_6647051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647051).length < 2 ^ (prefixWord ++ tailWord_6647051).sum := by decide
  have hdescent : baseEnd_6647051 < baseStart_6647051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647067 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3]
def baseStart_6647067 : Nat := 118140960795 + 6647067 * 2 ^ 59
def prefixEnd_6647067 : Nat := 4983230072969 + 3 ^ 40 * 6647067 * 2
def baseEnd_6647067 : Nat := 3413140313639450053493201

theorem tailTrace_6647067 : CollatzResearch.WordTrace tailWord_6647067 prefixEnd_6647067 3413140313639450053493201 := by
  unfold tailWord_6647067
  simp only [CollatzResearch.WordTrace]
  refine ⟨242438450609818962508539455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161625633739879308339026303 242438450609818962508539455)
  ·
    refine ⟨363657675914728443762809183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242438450609818962508539455 363657675914728443762809183)
    ·
      refine ⟨545486513872092665644213775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363657675914728443762809183 545486513872092665644213775)
      ·
        refine ⟨818229770808138998466320663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545486513872092665644213775 818229770808138998466320663)
        ·
          refine ⟨1227344656212208497699480995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818229770808138998466320663 1227344656212208497699480995)
          ·
            refine ⟨1841016984318312746549221493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227344656212208497699480995 1841016984318312746549221493)
            ·
              refine ⟨172595342279841819988989515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1841016984318312746549221493 172595342279841819988989515)
              ·
                refine ⟨258893013419762729983484273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172595342279841819988989515 258893013419762729983484273)
                ·
                  refine ⟨194169760064822047487613205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258893013419762729983484273 194169760064822047487613205)
                  ·
                    refine ⟨9101707503038533475981869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194169760064822047487613205 9101707503038533475981869)
                    ·
                      refine ⟨3413140313639450053493201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101707503038533475981869 3413140313639450053493201)
                      ·
                        rfl

theorem cell23_6647067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].length) (baseStart_6647067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647067 prefixEnd_6647067 := by exact prefixLift 6647067
  have htrace : WordTrace (prefixWord ++ tailWord_6647067) baseStart_6647067 baseEnd_6647067 := by
    simpa [prefixWord, tailWord_6647067, baseEnd_6647067] using wordTrace_append hprefix tailTrace_6647067
  have hstable : (prefixWord ++ tailWord_6647067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647067).length < 2 ^ (prefixWord ++ tailWord_6647067).sum := by decide
  have hdescent : baseEnd_6647067 < baseStart_6647067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647085 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6647085 : Nat := 118140960795 + 6647085 * 2 ^ 59
def prefixEnd_6647085 : Nat := 4983230072969 + 3 ^ 40 * 6647085 * 2
def baseEnd_6647085 : Nat := 3413149556291230983068119

theorem tailTrace_6647085 : CollatzResearch.WordTrace tailWord_6647085 prefixEnd_6647085 3413149556291230983068119 := by
  unfold tailWord_6647085
  simp only [CollatzResearch.WordTrace]
  refine ⟨242439107123753751582694709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161626071415835834388463139 242439107123753751582694709)
  ·
    refine ⟨22728666292851914210877629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242439107123753751582694709 22728666292851914210877629)
    ·
      refine ⟨8523249859819467829079111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22728666292851914210877629 8523249859819467829079111)
      ·
        refine ⟨12784874789729201743618667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523249859819467829079111 12784874789729201743618667)
        ·
          refine ⟨19177312184593802615428001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784874789729201743618667 19177312184593802615428001)
          ·
            refine ⟨14382984138445351961571001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19177312184593802615428001 14382984138445351961571001)
            ·
              refine ⟨10787238103834013971178251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14382984138445351961571001 10787238103834013971178251)
              ·
                refine ⟨16180857155751020956767377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787238103834013971178251 16180857155751020956767377)
                ·
                  refine ⟨12135642866813265717575533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16180857155751020956767377 12135642866813265717575533)
                  ·
                    refine ⟨4550866075054974644090825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12135642866813265717575533 4550866075054974644090825)
                    ·
                      refine ⟨3413149556291230983068119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550866075054974644090825 3413149556291230983068119)
                      ·
                        rfl

theorem cell23_6647085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6647085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647085 prefixEnd_6647085 := by exact prefixLift 6647085
  have htrace : WordTrace (prefixWord ++ tailWord_6647085) baseStart_6647085 baseEnd_6647085 := by
    simpa [prefixWord, tailWord_6647085, baseEnd_6647085] using wordTrace_append hprefix tailTrace_6647085
  have hstable : (prefixWord ++ tailWord_6647085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647085).length < 2 ^ (prefixWord ++ tailWord_6647085).sum := by decide
  have hdescent : baseEnd_6647085 < baseStart_6647085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647108 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6647108 : Nat := 118140960795 + 6647108 * 2 ^ 59
def prefixEnd_6647108 : Nat := 4983230072969 + 3 ^ 40 * 6647108 * 2
def baseEnd_6647108 : Nat := 1137720455448761464360171

theorem tailTrace_6647108 : CollatzResearch.WordTrace tailWord_6647108 prefixEnd_6647108 1137720455448761464360171 := by
  unfold tailWord_6647108
  simp only [CollatzResearch.WordTrace]
  refine ⟨121219973001335213255390989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161626630668446951007187985 121219973001335213255390989)
  ·
    refine ⟨45457489875500704970771621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121219973001335213255390989 45457489875500704970771621)
    ·
      refine ⟨8523279351656382182019679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45457489875500704970771621 8523279351656382182019679)
      ·
        refine ⟨12784919027484573273029519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523279351656382182019679 12784919027484573273029519)
        ·
          refine ⟨19177378541226859909544279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784919027484573273029519 19177378541226859909544279)
          ·
            refine ⟨28766067811840289864316419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177378541226859909544279 28766067811840289864316419)
            ·
              refine ⟨43149101717760434796474629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28766067811840289864316419 43149101717760434796474629)
              ·
                refine ⟨8090456572080081524338993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43149101717760434796474629 8090456572080081524338993)
                ·
                  refine ⟨6067842429060061143254245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8090456572080081524338993 6067842429060061143254245)
                  ·
                    refine ⟨1137720455448761464360171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6067842429060061143254245 1137720455448761464360171)
                    ·
                      rfl

theorem cell23_6647108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6647108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647108 prefixEnd_6647108 := by exact prefixLift 6647108
  have htrace : WordTrace (prefixWord ++ tailWord_6647108) baseStart_6647108 baseEnd_6647108 := by
    simpa [prefixWord, tailWord_6647108, baseEnd_6647108] using wordTrace_append hprefix tailTrace_6647108
  have hstable : (prefixWord ++ tailWord_6647108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647108).length < 2 ^ (prefixWord ++ tailWord_6647108).sum := by decide
  have hdescent : baseEnd_6647108 < baseStart_6647108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647141 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_6647141 : Nat := 118140960795 + 6647141 * 2 ^ 59
def prefixEnd_6647141 : Nat := 4983230072969 + 3 ^ 40 * 6647141 * 2
def baseEnd_6647141 : Nat := 3413178311207882763967861

theorem tailTrace_6647141 : CollatzResearch.WordTrace tailWord_6647141 prefixEnd_6647141 3413178311207882763967861 := by
  unfold tailWord_6647141
  simp only [CollatzResearch.WordTrace]
  refine ⟨242441149611550873146733277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161627433074367248764488851 242441149611550873146733277)
  ·
    refine ⟨90915431104331577430024979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242441149611550873146733277 90915431104331577430024979)
    ·
      refine ⟨136373146656497366145037469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90915431104331577430024979 136373146656497366145037469)
      ·
        refine ⟨51139929996186512304389051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136373146656497366145037469 51139929996186512304389051)
        ·
          refine ⟨76709894994279768456583577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51139929996186512304389051 76709894994279768456583577)
          ·
            refine ⟨57532421245709826342437683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76709894994279768456583577 57532421245709826342437683)
            ·
              refine ⟨86298631868564739513656525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57532421245709826342437683 86298631868564739513656525)
              ·
                refine ⟨32361986950711777317621197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86298631868564739513656525 32361986950711777317621197)
                ·
                  refine ⟨12135745106516916494107949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32361986950711777317621197 12135745106516916494107949)
                  ·
                    refine ⟨4550904414943843685290481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12135745106516916494107949 4550904414943843685290481)
                    ·
                      refine ⟨3413178311207882763967861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550904414943843685290481 3413178311207882763967861)
                      ·
                        rfl

theorem cell23_6647141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_6647141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647141 prefixEnd_6647141 := by exact prefixLift 6647141
  have htrace : WordTrace (prefixWord ++ tailWord_6647141) baseStart_6647141 baseEnd_6647141 := by
    simpa [prefixWord, tailWord_6647141, baseEnd_6647141] using wordTrace_append hprefix tailTrace_6647141
  have hstable : (prefixWord ++ tailWord_6647141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647141).length < 2 ^ (prefixWord ++ tailWord_6647141).sum := by decide
  have hdescent : baseEnd_6647141 < baseStart_6647141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647147 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 6]
def baseStart_6647147 : Nat := 118140960795 + 6647147 * 2 ^ 59
def prefixEnd_6647147 : Nat := 4983230072969 + 3 ^ 40 * 6647147 * 2
def baseEnd_6647147 : Nat := 1137727130697269913497611

theorem tailTrace_6647147 : CollatzResearch.WordTrace tailWord_6647147 prefixEnd_6647147 1137727130697269913497611 := by
  unfold tailWord_6647147
  simp only [CollatzResearch.WordTrace]
  refine ⟨242441368449529136171451695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161627578966352757447634463 242441368449529136171451695)
  ·
    refine ⟨363662052674293704257177543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242441368449529136171451695 363662052674293704257177543)
    ·
      refine ⟨545493079011440556385766315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363662052674293704257177543 545493079011440556385766315)
      ·
        refine ⟨818239618517160834578649473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545493079011440556385766315 818239618517160834578649473)
        ·
          refine ⟨613679713887870625933987105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818239618517160834578649473 613679713887870625933987105)
          ·
            refine ⟨460259785415902969450490329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613679713887870625933987105 460259785415902969450490329)
            ·
              refine ⟨345194839061927227087867747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460259785415902969450490329 345194839061927227087867747)
              ·
                refine ⟨517792258592890840631801621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345194839061927227087867747 517792258592890840631801621)
                ·
                  refine ⟨24271512121541758154615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 517792258592890840631801621 24271512121541758154615701)
                  ·
                    refine ⟨1137727130697269913497611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24271512121541758154615701 1137727130697269913497611)
                    ·
                      rfl

theorem cell23_6647147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_6647147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647147 prefixEnd_6647147 := by exact prefixLift 6647147
  have htrace : WordTrace (prefixWord ++ tailWord_6647147) baseStart_6647147 baseEnd_6647147 := by
    simpa [prefixWord, tailWord_6647147, baseEnd_6647147] using wordTrace_append hprefix tailTrace_6647147
  have hstable : (prefixWord ++ tailWord_6647147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647147).length < 2 ^ (prefixWord ++ tailWord_6647147).sum := by decide
  have hdescent : baseEnd_6647147 < baseStart_6647147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647167 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_6647167 : Nat := 118140960795 + 6647167 * 2 ^ 59
def prefixEnd_6647167 : Nat := 4983230072969 + 3 ^ 40 * 6647167 * 2
def baseEnd_6647167 : Nat := 3413191661704899662242741

theorem tailTrace_6647167 : CollatzResearch.WordTrace tailWord_6647167 prefixEnd_6647167 3413191661704899662242741 := by
  unfold tailWord_6647167
  simp only [CollatzResearch.WordTrace]
  refine ⟨242442097909456679587179755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161628065272971119724786503 242442097909456679587179755)
  ·
    refine ⟨363663146864185019380769633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242442097909456679587179755 363663146864185019380769633)
    ·
      refine ⟨272747360148138764535577225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363663146864185019380769633 272747360148138764535577225)
      ·
        refine ⟨204560520111104073401682919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272747360148138764535577225 204560520111104073401682919)
        ·
          refine ⟨306840780166656110102524379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204560520111104073401682919 306840780166656110102524379)
          ·
            refine ⟨460261170249984165153786569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306840780166656110102524379 460261170249984165153786569)
            ·
              refine ⟨345195877687488123865339927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460261170249984165153786569 345195877687488123865339927)
              ·
                refine ⟨517793816531232185798009891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345195877687488123865339927 517793816531232185798009891)
                ·
                  refine ⟨776690724796848278697014837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517793816531232185798009891 776690724796848278697014837)
                  ·
                    refine ⟨72814755449704526127845141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 776690724796848278697014837 72814755449704526127845141)
                    ·
                      refine ⟨3413191661704899662242741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72814755449704526127845141 3413191661704899662242741)
                      ·
                        rfl

theorem cell23_6647167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_6647167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647167 prefixEnd_6647167 := by exact prefixLift 6647167
  have htrace : WordTrace (prefixWord ++ tailWord_6647167) baseStart_6647167 baseEnd_6647167 := by
    simpa [prefixWord, tailWord_6647167, baseEnd_6647167] using wordTrace_append hprefix tailTrace_6647167
  have hstable : (prefixWord ++ tailWord_6647167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647167).length < 2 ^ (prefixWord ++ tailWord_6647167).sum := by decide
  have hdescent : baseEnd_6647167 < baseStart_6647167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647182 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6647182 : Nat := 118140960795 + 6647182 * 2 ^ 59
def prefixEnd_6647182 : Nat := 4983230072969 + 3 ^ 40 * 6647182 * 2
def baseEnd_6647182 : Nat := 3413199363914717103555173

theorem tailTrace_6647182 : CollatzResearch.WordTrace tailWord_6647182 prefixEnd_6647182 3413199363914717103555173 := by
  unfold tailWord_6647182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305330625550292143621975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161628430002934891432650533 30305330625550292143621975)
  ·
    refine ⟨45457995938325438215432963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30305330625550292143621975 45457995938325438215432963)
    ·
      refine ⟨68186993907488157323149445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45457995938325438215432963 68186993907488157323149445)
      ·
        refine ⟨12785061357654029498090521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68186993907488157323149445 12785061357654029498090521)
        ·
          refine ⟨9588796018240522123567891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785061357654029498090521 9588796018240522123567891)
          ·
            refine ⟨14383194027360783185351837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588796018240522123567891 14383194027360783185351837)
            ·
              refine ⟨5393697760260293694506939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14383194027360783185351837 5393697760260293694506939)
              ·
                refine ⟨8090546640390440541760409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393697760260293694506939 8090546640390440541760409)
                ·
                  refine ⟨6067909980292830406320307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8090546640390440541760409 6067909980292830406320307)
                  ·
                    refine ⟨9101864970439245609480461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067909980292830406320307 9101864970439245609480461)
                    ·
                      refine ⟨3413199363914717103555173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9101864970439245609480461 3413199363914717103555173)
                      ·
                        rfl

theorem cell23_6647182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6647182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647182 prefixEnd_6647182 := by exact prefixLift 6647182
  have htrace : WordTrace (prefixWord ++ tailWord_6647182) baseStart_6647182 baseEnd_6647182 := by
    simpa [prefixWord, tailWord_6647182, baseEnd_6647182] using wordTrace_append hprefix tailTrace_6647182
  have hstable : (prefixWord ++ tailWord_6647182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647182).length < 2 ^ (prefixWord ++ tailWord_6647182).sum := by decide
  have hdescent : baseEnd_6647182 < baseStart_6647182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647187 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_6647187 : Nat := 118140960795 + 6647187 * 2 ^ 59
def prefixEnd_6647187 : Nat := 4983230072969 + 3 ^ 40 * 6647187 * 2
def baseEnd_6647187 : Nat := 3413201931317989583992649

theorem tailTrace_6647187 : CollatzResearch.WordTrace tailWord_6647187 prefixEnd_6647187 3413201931317989583992649 := by
  unfold tailWord_6647187
  simp only [CollatzResearch.WordTrace]
  refine ⟨242442827369384223002907815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161628551579589482001938543 242442827369384223002907815)
  ·
    refine ⟨363664241054076334504361723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242442827369384223002907815 363664241054076334504361723)
    ·
      refine ⟨545496361581114501756542585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363664241054076334504361723 545496361581114501756542585)
      ·
        refine ⟨409122271185835876317406939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545496361581114501756542585 409122271185835876317406939)
        ·
          refine ⟨613683406778753814476110409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409122271185835876317406939 613683406778753814476110409)
          ·
            refine ⟨460262555084065360857082807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613683406778753814476110409 460262555084065360857082807)
            ·
              refine ⟨690393832626098041285624211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460262555084065360857082807 690393832626098041285624211)
              ·
                refine ⟨1035590748939147061928436317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690393832626098041285624211 1035590748939147061928436317)
                ·
                  refine ⟨388346530852180148223163619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035590748939147061928436317 388346530852180148223163619)
                  ·
                    refine ⟨582519796278270222334745429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388346530852180148223163619 582519796278270222334745429)
                    ·
                      refine ⟨3413201931317989583992649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 582519796278270222334745429 3413201931317989583992649)
                      ·
                        rfl

theorem cell23_6647187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_6647187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647187 prefixEnd_6647187 := by exact prefixLift 6647187
  have htrace : WordTrace (prefixWord ++ tailWord_6647187) baseStart_6647187 baseEnd_6647187 := by
    simpa [prefixWord, tailWord_6647187, baseEnd_6647187] using wordTrace_append hprefix tailTrace_6647187
  have hstable : (prefixWord ++ tailWord_6647187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647187).length < 2 ^ (prefixWord ++ tailWord_6647187).sum := by decide
  have hdescent : baseEnd_6647187 < baseStart_6647187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647194 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_6647194 : Nat := 118140960795 + 6647194 * 2 ^ 59
def prefixEnd_6647194 : Nat := 4983230072969 + 3 ^ 40 * 6647194 * 2
def baseEnd_6647194 : Nat := 379245058409174561845013

theorem tailTrace_6647194 : CollatzResearch.WordTrace tailWord_6647194 prefixEnd_6647194 379245058409174561845013 := by
  unfold tailWord_6647194
  simp only [CollatzResearch.WordTrace]
  refine ⟨60610770670089715799603159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161628721786905908798941757 60610770670089715799603159)
  ·
    refine ⟨90916156005134573699404739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60610770670089715799603159 90916156005134573699404739)
    ·
      refine ⟨136374234007701860549107109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90916156005134573699404739 136374234007701860549107109)
      ·
        refine ⟨25570168876444098852957583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136374234007701860549107109 25570168876444098852957583)
        ·
          refine ⟨38355253314666148279436375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25570168876444098852957583 38355253314666148279436375)
          ·
            refine ⟨57532879971999222419154563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38355253314666148279436375 57532879971999222419154563)
            ·
              refine ⟨86299319957998833628731845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57532879971999222419154563 86299319957998833628731845)
              ·
                refine ⟨16181122492124781305387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86299319957998833628731845 16181122492124781305387221)
                ·
                  refine ⟨379245058409174561845013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16181122492124781305387221 379245058409174561845013)
                  ·
                    rfl

theorem cell23_6647194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_6647194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647194 prefixEnd_6647194 := by exact prefixLift 6647194
  have htrace : WordTrace (prefixWord ++ tailWord_6647194) baseStart_6647194 baseEnd_6647194 := by
    simpa [prefixWord, tailWord_6647194, baseEnd_6647194] using wordTrace_append hprefix tailTrace_6647194
  have hstable : (prefixWord ++ tailWord_6647194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647194).length < 2 ^ (prefixWord ++ tailWord_6647194).sum := by decide
  have hdescent : baseEnd_6647194 < baseStart_6647194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647208 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6647208 : Nat := 118140960795 + 6647208 * 2 ^ 59
def prefixEnd_6647208 : Nat := 4983230072969 + 3 ^ 40 * 6647208 * 2
def baseEnd_6647208 : Nat := 3413212714411734001830053

theorem tailTrace_6647208 : CollatzResearch.WordTrace tailWord_6647208 prefixEnd_6647208 3413212714411734001830053 := by
  unfold tailWord_6647208
  simp only [CollatzResearch.WordTrace]
  refine ⟨121221796651154071794711139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161629062201538762392948185 121221796651154071794711139)
  ·
    refine ⟨181832694976731107692066709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121221796651154071794711139 181832694976731107692066709)
    ·
      refine ⟨8523407577034270673065627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181832694976731107692066709 8523407577034270673065627)
      ·
        refine ⟨12785111365551406009598441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523407577034270673065627 12785111365551406009598441)
        ·
          refine ⟨9588833524163554507198831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785111365551406009598441 9588833524163554507198831)
          ·
            refine ⟨14383250286245331760798247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588833524163554507198831 14383250286245331760798247)
            ·
              refine ⟨21574875429367997641197371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14383250286245331760798247 21574875429367997641197371)
              ·
                refine ⟨32362313144051996461796057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21574875429367997641197371 32362313144051996461796057)
                ·
                  refine ⟨24271734858038997346347043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32362313144051996461796057 24271734858038997346347043)
                  ·
                    refine ⟨36407602287058496019520565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24271734858038997346347043 36407602287058496019520565)
                    ·
                      refine ⟨3413212714411734001830053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36407602287058496019520565 3413212714411734001830053)
                      ·
                        rfl

theorem cell23_6647208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6647208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647208 prefixEnd_6647208 := by exact prefixLift 6647208
  have htrace : WordTrace (prefixWord ++ tailWord_6647208) baseStart_6647208 baseEnd_6647208 := by
    simpa [prefixWord, tailWord_6647208, baseEnd_6647208] using wordTrace_append hprefix tailTrace_6647208
  have hstable : (prefixWord ++ tailWord_6647208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647208).length < 2 ^ (prefixWord ++ tailWord_6647208).sum := by decide
  have hdescent : baseEnd_6647208 < baseStart_6647208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647224 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_6647224 : Nat := 118140960795 + 6647224 * 2 ^ 59
def prefixEnd_6647224 : Nat := 4983230072969 + 3 ^ 40 * 6647224 * 2
def baseEnd_6647224 : Nat := 1137740310034068646409993

theorem tailTrace_6647224 : CollatzResearch.WordTrace tailWord_6647224 prefixEnd_6647224 1137740310034068646409993 := by
  unfold tailWord_6647224
  simp only [CollatzResearch.WordTrace]
  refine ⟨121222088435125089161002363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161629451246833452214669817 121222088435125089161002363)
  ·
    refine ⟨181833132652687633741503545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121222088435125089161002363 181833132652687633741503545)
    ·
      refine ⟨136374849489515725306127659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181833132652687633741503545 136374849489515725306127659)
      ·
        refine ⟨204562274234273587959191489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136374849489515725306127659 204562274234273587959191489)
        ·
          refine ⟨153421705675705190969393617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204562274234273587959191489 153421705675705190969393617)
          ·
            refine ⟨115066279256778893227045213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153421705675705190969393617 115066279256778893227045213)
            ·
              refine ⟨43149854721292084960141955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115066279256778893227045213 43149854721292084960141955)
              ·
                refine ⟨64724782081938127440212933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43149854721292084960141955 64724782081938127440212933)
                ·
                  refine ⟨12135896640363398895039925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64724782081938127440212933 12135896640363398895039925)
                  ·
                    refine ⟨1137740310034068646409993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12135896640363398895039925 1137740310034068646409993)
                    ·
                      rfl

theorem cell23_6647224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_6647224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647224 prefixEnd_6647224 := by exact prefixLift 6647224
  have htrace : WordTrace (prefixWord ++ tailWord_6647224) baseStart_6647224 baseEnd_6647224 := by
    simpa [prefixWord, tailWord_6647224, baseEnd_6647224] using wordTrace_append hprefix tailTrace_6647224
  have hstable : (prefixWord ++ tailWord_6647224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647224).length < 2 ^ (prefixWord ++ tailWord_6647224).sum := by decide
  have hdescent : baseEnd_6647224 < baseStart_6647224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647228 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 7]
def baseStart_6647228 : Nat := 118140960795 + 6647228 * 2 ^ 59
def prefixEnd_6647228 : Nat := 4983230072969 + 3 ^ 40 * 6647228 * 2
def baseEnd_6647228 : Nat := 379246998224980435953329

theorem tailTrace_6647228 : CollatzResearch.WordTrace tailWord_6647228 prefixEnd_6647228 379246998224980435953329 := by
  unfold tailWord_6647228
  simp only [CollatzResearch.WordTrace]
  refine ⟨121222161381117843502575169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161629548508157124670100225 121222161381117843502575169)
  ·
    refine ⟨90916621035838382626931377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121222161381117843502575169 90916621035838382626931377)
    ·
      refine ⟨68187465776878786970198533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90916621035838382626931377 68187465776878786970198533)
      ·
        refine ⟨12785149833164772556912225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68187465776878786970198533 12785149833164772556912225)
        ·
          refine ⟨9588862374873579417684169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785149833164772556912225 9588862374873579417684169)
          ·
            refine ⟨7191646781155184563263127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9588862374873579417684169 7191646781155184563263127)
            ·
              refine ⟨10787470171732776844894691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191646781155184563263127 10787470171732776844894691)
              ·
                refine ⟨16181205257599165267342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787470171732776844894691 16181205257599165267342037)
                ·
                  refine ⟨379246998224980435953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16181205257599165267342037 379246998224980435953329)
                  ·
                    rfl

theorem cell23_6647228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_6647228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647228 prefixEnd_6647228 := by exact prefixLift 6647228
  have htrace : WordTrace (prefixWord ++ tailWord_6647228) baseStart_6647228 baseEnd_6647228 := by
    simpa [prefixWord, tailWord_6647228, baseEnd_6647228] using wordTrace_append hprefix tailTrace_6647228
  have hstable : (prefixWord ++ tailWord_6647228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647228).length < 2 ^ (prefixWord ++ tailWord_6647228).sum := by decide
  have hdescent : baseEnd_6647228 < baseStart_6647228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647278 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_6647278 : Nat := 118140960795 + 6647278 * 2 ^ 59
def prefixEnd_6647278 : Nat := 4983230072969 + 3 ^ 40 * 6647278 * 2
def baseEnd_6647278 : Nat := 3413248658057548727954731

theorem tailTrace_6647278 : CollatzResearch.WordTrace tailWord_6647278 prefixEnd_6647278 3413248658057548727954731 := by
  unfold tailWord_6647278
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305768301506818193058811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161630764274703030362980325 30305768301506818193058811)
  ·
    refine ⟨45458652452260227289588217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30305768301506818193058811 45458652452260227289588217)
    ·
      refine ⟨34093989339195170467191163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45458652452260227289588217 34093989339195170467191163)
      ·
        refine ⟨51140984008792755700786745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093989339195170467191163 51140984008792755700786745)
        ·
          refine ⟨38355738006594566775590059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51140984008792755700786745 38355738006594566775590059)
          ·
            refine ⟨57533607009891850163385089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38355738006594566775590059 57533607009891850163385089)
            ·
              refine ⟨43150205257418887622538817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57533607009891850163385089 43150205257418887622538817)
              ·
                refine ⟨32362653943064165716904113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43150205257418887622538817 32362653943064165716904113)
                ·
                  refine ⟨24271990457298124287678085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32362653943064165716904113 24271990457298124287678085)
                  ·
                    refine ⟨4550998210743398303939641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24271990457298124287678085 4550998210743398303939641)
                    ·
                      refine ⟨3413248658057548727954731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4550998210743398303939641 3413248658057548727954731)
                      ·
                        rfl

theorem cell23_6647278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_6647278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647278 prefixEnd_6647278 := by exact prefixLift 6647278
  have htrace : WordTrace (prefixWord ++ tailWord_6647278) baseStart_6647278 baseEnd_6647278 := by
    simpa [prefixWord, tailWord_6647278, baseEnd_6647278] using wordTrace_append hprefix tailTrace_6647278
  have hstable : (prefixWord ++ tailWord_6647278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647278).length < 2 ^ (prefixWord ++ tailWord_6647278).sum := by decide
  have hdescent : baseEnd_6647278 < baseStart_6647278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647309 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6647309 : Nat := 118140960795 + 6647309 * 2 ^ 59
def prefixEnd_6647309 : Nat := 4983230072969 + 3 ^ 40 * 6647309 * 2
def baseEnd_6647309 : Nat := 1137754858652612702222363

theorem tailTrace_6647309 : CollatzResearch.WordTrace tailWord_6647309 prefixEnd_6647309 1137754858652612702222363 := by
  unfold tailWord_6647309
  simp only [CollatzResearch.WordTrace]
  refine ⟨242447277074942237838848981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161631518049961491892565987 242447277074942237838848981)
  ·
    refine ⟨5682358056443958699348023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 242447277074942237838848981 5682358056443958699348023)
    ·
      refine ⟨8523537084665938049022035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682358056443958699348023 8523537084665938049022035)
      ·
        refine ⟨12785305626998907073533053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523537084665938049022035 12785305626998907073533053)
        ·
          refine ⟨4794489610124590152574895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12785305626998907073533053 4794489610124590152574895)
          ·
            refine ⟨7191734415186885228862343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794489610124590152574895 7191734415186885228862343)
            ·
              refine ⟨10787601622780327843293515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191734415186885228862343 10787601622780327843293515)
              ·
                refine ⟨16181402434170491764940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787601622780327843293515 16181402434170491764940273)
                ·
                  refine ⟨12136051825627868823705205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16181402434170491764940273 12136051825627868823705205)
                  ·
                    refine ⟨1137754858652612702222363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12136051825627868823705205 1137754858652612702222363)
                    ·
                      rfl

theorem cell23_6647309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6647309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647309 prefixEnd_6647309 := by exact prefixLift 6647309
  have htrace : WordTrace (prefixWord ++ tailWord_6647309) baseStart_6647309 baseEnd_6647309 := by
    simpa [prefixWord, tailWord_6647309, baseEnd_6647309] using wordTrace_append hprefix tailTrace_6647309
  have hstable : (prefixWord ++ tailWord_6647309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647309).length < 2 ^ (prefixWord ++ tailWord_6647309).sum := by decide
  have hdescent : baseEnd_6647309 < baseStart_6647309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647378 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_6647378 : Nat := 118140960795 + 6647378 * 2 ^ 59
def prefixEnd_6647378 : Nat := 4983230072969 + 3 ^ 40 * 6647378 * 2
def baseEnd_6647378 : Nat := 1137766668707666112234757

theorem tailTrace_6647378 : CollatzResearch.WordTrace tailWord_6647378 prefixEnd_6647378 1137766668707666112234757 := by
  unfold tailWord_6647378
  simp only [CollatzResearch.WordTrace]
  refine ⟨60612448427923065655777697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161633195807794841748740525 60612448427923065655777697)
  ·
    refine ⟨45459336320942299241833273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60612448427923065655777697 45459336320942299241833273)
    ·
      refine ⟨34094502240706724431374955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45459336320942299241833273 34094502240706724431374955)
      ·
        refine ⟨51141753361060086647062433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34094502240706724431374955 51141753361060086647062433)
        ·
          refine ⟨38356315020795064985296825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51141753361060086647062433 38356315020795064985296825)
          ·
            refine ⟨28767236265596298738972619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38356315020795064985296825 28767236265596298738972619)
            ·
              refine ⟨43150854398394448108458929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28767236265596298738972619 43150854398394448108458929)
              ·
                refine ⟨32363140798795836081344197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43150854398394448108458929 32363140798795836081344197)
                ·
                  refine ⟨6068088899774219265252037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32363140798795836081344197 6068088899774219265252037)
                  ·
                    refine ⟨1137766668707666112234757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068088899774219265252037 1137766668707666112234757)
                    ·
                      rfl

theorem cell23_6647378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_6647378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647378 prefixEnd_6647378 := by exact prefixLift 6647378
  have htrace : WordTrace (prefixWord ++ tailWord_6647378) baseStart_6647378 baseEnd_6647378 := by
    simpa [prefixWord, tailWord_6647378, baseEnd_6647378] using wordTrace_append hprefix tailTrace_6647378
  have hstable : (prefixWord ++ tailWord_6647378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647378).length < 2 ^ (prefixWord ++ tailWord_6647378).sum := by decide
  have hdescent : baseEnd_6647378 < baseStart_6647378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647381 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6647381 : Nat := 118140960795 + 6647381 * 2 ^ 59
def prefixEnd_6647381 : Nat := 4983230072969 + 3 ^ 40 * 6647381 * 2
def baseEnd_6647381 : Nat := 3413301546564961824966757

theorem tailTrace_6647381 : CollatzResearch.WordTrace tailWord_6647381 prefixEnd_6647381 3413301546564961824966757 := by
  unfold tailWord_6647381
  simp only [CollatzResearch.WordTrace]
  refine ⟨242449903130681394135469997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161633268753787596090313331 242449903130681394135469997)
  ·
    refine ⟨90918713674005522800801249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242449903130681394135469997 90918713674005522800801249)
    ·
      refine ⟨68189035255504142100600937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90918713674005522800801249 68189035255504142100600937)
      ·
        refine ⟨51141776441628106575450703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68189035255504142100600937 51141776441628106575450703)
        ·
          refine ⟨76712664662442159863176055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51141776441628106575450703 76712664662442159863176055)
          ·
            refine ⟨115068996993663239794764083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76712664662442159863176055 115068996993663239794764083)
            ·
              refine ⟨172603495490494859692146125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115068996993663239794764083 172603495490494859692146125)
              ·
                refine ⟨64726310808935572384554797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172603495490494859692146125 64726310808935572384554797)
                ·
                  refine ⟨24272366553350839644208049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64726310808935572384554797 24272366553350839644208049)
                  ·
                    refine ⟨18204274915013129733156037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24272366553350839644208049 18204274915013129733156037)
                    ·
                      refine ⟨3413301546564961824966757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18204274915013129733156037 3413301546564961824966757)
                      ·
                        rfl

theorem cell23_6647381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6647381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647381 prefixEnd_6647381 := by exact prefixLift 6647381
  have htrace : WordTrace (prefixWord ++ tailWord_6647381) baseStart_6647381 baseEnd_6647381 := by
    simpa [prefixWord, tailWord_6647381, baseEnd_6647381] using wordTrace_append hprefix tailTrace_6647381
  have hstable : (prefixWord ++ tailWord_6647381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647381).length < 2 ^ (prefixWord ++ tailWord_6647381).sum := by decide
  have hdescent : baseEnd_6647381 < baseStart_6647381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647388 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6647388 : Nat := 118140960795 + 6647388 * 2 ^ 59
def prefixEnd_6647388 : Nat := 4983230072969 + 3 ^ 40 * 6647388 * 2
def baseEnd_6647388 : Nat := 3413305140929543297579225

theorem tailTrace_6647388 : CollatzResearch.WordTrace tailWord_6647388 prefixEnd_6647388 3413305140929543297579225 := by
  unfold tailWord_6647388
  simp only [CollatzResearch.WordTrace]
  refine ⟨121225079220828017165487409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161633438961104022887316545 121225079220828017165487409)
  ·
    refine ⟨90918809415621012874115557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121225079220828017165487409 90918809415621012874115557)
    ·
      refine ⟨17047276765428939913896667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90918809415621012874115557 17047276765428939913896667)
      ·
        refine ⟨25570915148143409870845001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17047276765428939913896667 25570915148143409870845001)
        ·
          refine ⟨19178186361107557403133751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25570915148143409870845001 19178186361107557403133751)
          ·
            refine ⟨28767279541661336104700627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19178186361107557403133751 28767279541661336104700627)
            ·
              refine ⟨43150919312492004157050941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28767279541661336104700627 43150919312492004157050941)
              ·
                refine ⟨16181594742184501558894103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43150919312492004157050941 16181594742184501558894103)
                ·
                  refine ⟨24272392113276752338341155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16181594742184501558894103 24272392113276752338341155)
                  ·
                    refine ⟨36408588169915128507511733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24272392113276752338341155 36408588169915128507511733)
                    ·
                      refine ⟨3413305140929543297579225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36408588169915128507511733 3413305140929543297579225)
                      ·
                        rfl

theorem cell23_6647388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6647388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647388 prefixEnd_6647388 := by exact prefixLift 6647388
  have htrace : WordTrace (prefixWord ++ tailWord_6647388) baseStart_6647388 baseEnd_6647388 := by
    simpa [prefixWord, tailWord_6647388, baseEnd_6647388] using wordTrace_append hprefix tailTrace_6647388
  have hstable : (prefixWord ++ tailWord_6647388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647388).length < 2 ^ (prefixWord ++ tailWord_6647388).sum := by decide
  have hdescent : baseEnd_6647388 < baseStart_6647388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647389 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6647389 : Nat := 118140960795 + 6647389 * 2 ^ 59
def prefixEnd_6647389 : Nat := 4983230072969 + 3 ^ 40 * 6647389 * 2
def baseEnd_6647389 : Nat := 3413305654410197793666721

theorem tailTrace_6647389 : CollatzResearch.WordTrace tailWord_6647389 prefixEnd_6647389 3413305654410197793666721 := by
  unfold tailWord_6647389
  simp only [CollatzResearch.WordTrace]
  refine ⟨242450194914652411501761221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161633463276434941001174147 242450194914652411501761221)
  ·
    refine ⟨45459411546497327156580229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242450194914652411501761221 45459411546497327156580229)
    ·
      refine ⟨8523639664968248841858793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45459411546497327156580229 8523639664968248841858793)
      ·
        refine ⟨6392729748726186631394095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523639664968248841858793 6392729748726186631394095)
        ·
          refine ⟨9589094623089279947091143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392729748726186631394095 9589094623089279947091143)
          ·
            refine ⟨14383641934633919920636715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589094623089279947091143 14383641934633919920636715)
            ·
              refine ⟨21575462901950879880955073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14383641934633919920636715 21575462901950879880955073)
              ·
                refine ⟨16181597176463159910716305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21575462901950879880955073 16181597176463159910716305)
                ·
                  refine ⟨12136197882347369933037229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16181597176463159910716305 12136197882347369933037229)
                  ·
                    refine ⟨4551074205880263724888961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12136197882347369933037229 4551074205880263724888961)
                    ·
                      refine ⟨3413305654410197793666721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551074205880263724888961 3413305654410197793666721)
                      ·
                        rfl

theorem cell23_6647389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6647389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647389 prefixEnd_6647389 := by exact prefixLift 6647389
  have htrace : WordTrace (prefixWord ++ tailWord_6647389) baseStart_6647389 baseEnd_6647389 := by
    simpa [prefixWord, tailWord_6647389, baseEnd_6647389] using wordTrace_append hprefix tailTrace_6647389
  have hstable : (prefixWord ++ tailWord_6647389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647389).length < 2 ^ (prefixWord ++ tailWord_6647389).sum := by decide
  have hdescent : baseEnd_6647389 < baseStart_6647389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647402 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_6647402 : Nat := 118140960795 + 6647402 * 2 ^ 59
def prefixEnd_6647402 : Nat := 4983230072969 + 3 ^ 40 * 6647402 * 2
def baseEnd_6647402 : Nat := 3413312329658706242804161

theorem tailTrace_6647402 : CollatzResearch.WordTrace tailWord_6647402 prefixEnd_6647402 3413312329658706242804161 := by
  unfold tailWord_6647402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60612667265901328680496115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161633779375736876481322973 60612667265901328680496115)
  ·
    refine ⟨90919000898851993020744173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60612667265901328680496115 90919000898851993020744173)
    ·
      refine ⟨34094625337069497382779065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90919000898851993020744173 34094625337069497382779065)
      ·
        refine ⟨25570969002802123037084299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34094625337069497382779065 25570969002802123037084299)
        ·
          refine ⟨38356453504203184555626449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25570969002802123037084299 38356453504203184555626449)
          ·
            refine ⟨28767340128152388416719837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38356453504203184555626449 28767340128152388416719837)
            ·
              refine ⟨10787752548057145656269939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28767340128152388416719837 10787752548057145656269939)
              ·
                refine ⟨16181628822085718484404909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787752548057145656269939 16181628822085718484404909)
                ·
                  refine ⟨6068110808282144431651841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16181628822085718484404909 6068110808282144431651841)
                  ·
                    refine ⟨4551083106211608323738881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068110808282144431651841 4551083106211608323738881)
                    ·
                      refine ⟨3413312329658706242804161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551083106211608323738881 3413312329658706242804161)
                      ·
                        rfl

theorem cell23_6647402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_6647402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647402 prefixEnd_6647402 := by exact prefixLift 6647402
  have htrace : WordTrace (prefixWord ++ tailWord_6647402) baseStart_6647402 baseEnd_6647402 := by
    simpa [prefixWord, tailWord_6647402, baseEnd_6647402] using wordTrace_append hprefix tailTrace_6647402
  have hstable : (prefixWord ++ tailWord_6647402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647402).length < 2 ^ (prefixWord ++ tailWord_6647402).sum := by decide
  have hdescent : baseEnd_6647402 < baseStart_6647402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647418 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_6647418 : Nat := 118140960795 + 6647418 * 2 ^ 59
def prefixEnd_6647418 : Nat := 4983230072969 + 3 ^ 40 * 6647418 * 2
def baseEnd_6647418 : Nat := 3413320545349178180204087

theorem tailTrace_6647418 : CollatzResearch.WordTrace tailWord_6647418 prefixEnd_6647418 3413320545349178180204087 := by
  unfold tailWord_6647418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60612813157886837363641727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161634168421031566303044605 60612813157886837363641727)
  ·
    refine ⟨90919219736830256045462591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60612813157886837363641727 90919219736830256045462591)
    ·
      refine ⟨136378829605245384068193887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90919219736830256045462591 136378829605245384068193887)
      ·
        refine ⟨204568244407868076102290831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136378829605245384068193887 204568244407868076102290831)
        ·
          refine ⟨306852366611802114153436247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204568244407868076102290831 306852366611802114153436247)
          ·
            refine ⟨460278549917703171230154371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306852366611802114153436247 460278549917703171230154371)
            ·
              refine ⟨690417824876554756845231557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460278549917703171230154371 690417824876554756845231557)
              ·
                refine ⟨129453342164354016908480917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690417824876554756845231557 129453342164354016908480917)
                ·
                  refine ⟨6068125413954094542585043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129453342164354016908480917 6068125413954094542585043)
                  ·
                    refine ⟨9102188120931141813877565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068125413954094542585043 9102188120931141813877565)
                    ·
                      refine ⟨3413320545349178180204087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102188120931141813877565 3413320545349178180204087)
                      ·
                        rfl

theorem cell23_6647418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_6647418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647418 prefixEnd_6647418 := by exact prefixLift 6647418
  have htrace : WordTrace (prefixWord ++ tailWord_6647418) baseStart_6647418 baseEnd_6647418 := by
    simpa [prefixWord, tailWord_6647418, baseEnd_6647418] using wordTrace_append hprefix tailTrace_6647418
  have hstable : (prefixWord ++ tailWord_6647418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647418).length < 2 ^ (prefixWord ++ tailWord_6647418).sum := by decide
  have hdescent : baseEnd_6647418 < baseStart_6647418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647445 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_6647445 : Nat := 118140960795 + 6647445 * 2 ^ 59
def prefixEnd_6647445 : Nat := 4983230072969 + 3 ^ 40 * 6647445 * 2
def baseEnd_6647445 : Nat := 3413334409326849574566463

theorem tailTrace_6647445 : CollatzResearch.WordTrace tailWord_6647445 prefixEnd_6647445 3413334409326849574566463 := by
  unfold tailWord_6647445
  simp only [CollatzResearch.WordTrace]
  refine ⟨242452237402449533065799789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161634824934966355377199859 242452237402449533065799789)
  ·
    refine ⟨90919589025918574899674921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242452237402449533065799789 90919589025918574899674921)
    ·
      refine ⟨68189691769438931174756191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90919589025918574899674921 68189691769438931174756191)
      ·
        refine ⟨102284537654158396762134287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68189691769438931174756191 102284537654158396762134287)
        ·
          refine ⟨153426806481237595143201431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102284537654158396762134287 153426806481237595143201431)
          ·
            refine ⟨230140209721856392714802147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153426806481237595143201431 230140209721856392714802147)
            ·
              refine ⟨345210314582784589072203221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230140209721856392714802147 345210314582784589072203221)
              ·
                refine ⟨8090866748034013806379763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 345210314582784589072203221 8090866748034013806379763)
                ·
                  refine ⟨12136300122051020709569645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090866748034013806379763 12136300122051020709569645)
                  ·
                    refine ⟨4551112545769132766088617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12136300122051020709569645 4551112545769132766088617)
                    ·
                      refine ⟨3413334409326849574566463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551112545769132766088617 3413334409326849574566463)
                      ·
                        rfl

theorem cell23_6647445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_6647445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647445 prefixEnd_6647445 := by exact prefixLift 6647445
  have htrace : WordTrace (prefixWord ++ tailWord_6647445) baseStart_6647445 baseEnd_6647445 := by
    simpa [prefixWord, tailWord_6647445, baseEnd_6647445] using wordTrace_append hprefix tailTrace_6647445
  have hstable : (prefixWord ++ tailWord_6647445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647445).length < 2 ^ (prefixWord ++ tailWord_6647445).sum := by decide
  have hdescent : baseEnd_6647445 < baseStart_6647445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647461 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6647461 : Nat := 118140960795 + 6647461 * 2 ^ 59
def prefixEnd_6647461 : Nat := 4983230072969 + 3 ^ 40 * 6647461 * 2
def baseEnd_6647461 : Nat := 3413342625017321511966389

theorem tailTrace_6647461 : CollatzResearch.WordTrace tailWord_6647461 prefixEnd_6647461 3413342625017321511966389 := by
  unfold tailWord_6647461
  simp only [CollatzResearch.WordTrace]
  refine ⟨242452820970391567798382237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161635213980261045198921491 242452820970391567798382237)
  ·
    refine ⟨90919807863896837924393339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242452820970391567798382237 90919807863896837924393339)
    ·
      refine ⟨136379711795845256886590009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90919807863896837924393339 136379711795845256886590009)
      ·
        refine ⟨102284783846883942664942507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136379711795845256886590009 102284783846883942664942507)
        ·
          refine ⟨153427175770325913997413761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102284783846883942664942507 153427175770325913997413761)
          ·
            refine ⟨115070381827744435498060321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153427175770325913997413761 115070381827744435498060321)
            ·
              refine ⟨86302786370808326623545241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115070381827744435498060321 86302786370808326623545241)
              ·
                refine ⟨64727089778106244967658931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86302786370808326623545241 64727089778106244967658931)
                ·
                  refine ⟨97090634667159367451488397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64727089778106244967658931 97090634667159367451488397)
                  ·
                    refine ⟨36408988000184762794308149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97090634667159367451488397 36408988000184762794308149)
                    ·
                      refine ⟨3413342625017321511966389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36408988000184762794308149 3413342625017321511966389)
                      ·
                        rfl

theorem cell23_6647461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6647461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647461 prefixEnd_6647461 := by exact prefixLift 6647461
  have htrace : WordTrace (prefixWord ++ tailWord_6647461) baseStart_6647461 baseEnd_6647461 := by
    simpa [prefixWord, tailWord_6647461, baseEnd_6647461] using wordTrace_append hprefix tailTrace_6647461
  have hstable : (prefixWord ++ tailWord_6647461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647461).length < 2 ^ (prefixWord ++ tailWord_6647461).sum := by decide
  have hdescent : baseEnd_6647461 < baseStart_6647461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647475 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 4, 2]
def baseStart_6647475 : Nat := 118140960795 + 6647475 * 2 ^ 59
def prefixEnd_6647475 : Nat := 4983230072969 + 3 ^ 40 * 6647475 * 2
def baseEnd_6647475 : Nat := 3413349813746484457191325

theorem tailTrace_6647475 : CollatzResearch.WordTrace tailWord_6647475 prefixEnd_6647475 3413349813746484457191325 := by
  unfold tailWord_6647475
  simp only [CollatzResearch.WordTrace]
  refine ⟨242453331592340848189391879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161635554394893898792927919 242453331592340848189391879)
  ·
    refine ⟨363679997388511272284087819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242453331592340848189391879 363679997388511272284087819)
    ·
      refine ⟨545519996082766908426131729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363679997388511272284087819 545519996082766908426131729)
      ·
        refine ⟨409139997062075181319598797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545519996082766908426131729 409139997062075181319598797)
        ·
          refine ⟨153427498898278192994849549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409139997062075181319598797 153427498898278192994849549)
          ·
            refine ⟨57535312086854322373068581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153427498898278192994849549 57535312086854322373068581)
            ·
              refine ⟨10787871016285185444950359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57535312086854322373068581 10787871016285185444950359)
              ·
                refine ⟨16181806524427778167425539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787871016285185444950359 16181806524427778167425539)
                ·
                  refine ⟨24272709786641667251138309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16181806524427778167425539 24272709786641667251138309)
                  ·
                    refine ⟨4551133084995312609588433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24272709786641667251138309 4551133084995312609588433)
                    ·
                      refine ⟨3413349813746484457191325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551133084995312609588433 3413349813746484457191325)
                      ·
                        rfl

theorem cell23_6647475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4, 2].length) (baseStart_6647475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647475 prefixEnd_6647475 := by exact prefixLift 6647475
  have htrace : WordTrace (prefixWord ++ tailWord_6647475) baseStart_6647475 baseEnd_6647475 := by
    simpa [prefixWord, tailWord_6647475, baseEnd_6647475] using wordTrace_append hprefix tailTrace_6647475
  have hstable : (prefixWord ++ tailWord_6647475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647475).length < 2 ^ (prefixWord ++ tailWord_6647475).sum := by decide
  have hdescent : baseEnd_6647475 < baseStart_6647475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647481 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 9]
def baseStart_6647481 : Nat := 118140960795 + 6647481 * 2 ^ 59
def prefixEnd_6647481 : Nat := 4983230072969 + 3 ^ 40 * 6647481 * 2
def baseEnd_6647481 : Nat := 379261432736712381524033

theorem tailTrace_6647481 : CollatzResearch.WordTrace tailWord_6647481 prefixEnd_6647481 379261432736712381524033 := by
  unfold tailWord_6647481
  simp only [CollatzResearch.WordTrace]
  refine ⟨242453550430319111214110297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161635700286879407476073531 242453550430319111214110297)
  ·
    refine ⟨181840162822739333410582723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242453550430319111214110297 181840162822739333410582723)
    ·
      refine ⟨272760244234109000115874085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181840162822739333410582723 272760244234109000115874085)
      ·
        refine ⟨51142545793895437521726391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272760244234109000115874085 51142545793895437521726391)
        ·
          refine ⟨76713818690843156282589587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51142545793895437521726391 76713818690843156282589587)
          ·
            refine ⟨115070728036264734423884381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76713818690843156282589587 115070728036264734423884381)
            ·
              refine ⟨43151523013599275408956643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115070728036264734423884381 43151523013599275408956643)
              ·
                refine ⟨64727284520398913113434965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43151523013599275408956643 64727284520398913113434965)
                ·
                  refine ⟨379261432736712381524033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64727284520398913113434965 379261432736712381524033)
                  ·
                    rfl

theorem cell23_6647481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_6647481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647481 prefixEnd_6647481 := by exact prefixLift 6647481
  have htrace : WordTrace (prefixWord ++ tailWord_6647481) baseStart_6647481 baseEnd_6647481 := by
    simpa [prefixWord, tailWord_6647481, baseEnd_6647481] using wordTrace_append hprefix tailTrace_6647481
  have hstable : (prefixWord ++ tailWord_6647481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647481).length < 2 ^ (prefixWord ++ tailWord_6647481).sum := by decide
  have hdescent : baseEnd_6647481 < baseStart_6647481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647490 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6647490 : Nat := 118140960795 + 6647490 * 2 ^ 59
def prefixEnd_6647490 : Nat := 4983230072969 + 3 ^ 40 * 6647490 * 2
def baseEnd_6647490 : Nat := 3413357515956301898503757

theorem tailTrace_6647490 : CollatzResearch.WordTrace tailWord_6647490 prefixEnd_6647490 3413357515956301898503757 := by
  unfold tailWord_6647490
  simp only [CollatzResearch.WordTrace]
  refine ⟨60613469671821626437796981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161635919124857670500791949 60613469671821626437796981)
  ·
    refine ⟨5682512781733277478543467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60613469671821626437796981 5682512781733277478543467)
    ·
      refine ⟨8523769172599916217815201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682512781733277478543467 8523769172599916217815201)
      ·
        refine ⟨6392826879449937163361401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523769172599916217815201 6392826879449937163361401)
        ·
          refine ⟨4794620159587452872521051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392826879449937163361401 4794620159587452872521051)
          ·
            refine ⟨7191930239381179308781577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794620159587452872521051 7191930239381179308781577)
            ·
              refine ⟨5393947679535884481586183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7191930239381179308781577 5393947679535884481586183)
              ·
                refine ⟨8090921519303826722379275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393947679535884481586183 8090921519303826722379275)
                ·
                  refine ⟨12136382278955740083568913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090921519303826722379275 12136382278955740083568913)
                  ·
                    refine ⟨9102286709216805062676685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12136382278955740083568913 9102286709216805062676685)
                    ·
                      refine ⟨3413357515956301898503757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102286709216805062676685 3413357515956301898503757)
                      ·
                        rfl

theorem cell23_6647490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6647490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647490 prefixEnd_6647490 := by exact prefixLift 6647490
  have htrace : WordTrace (prefixWord ++ tailWord_6647490) baseStart_6647490 baseEnd_6647490 := by
    simpa [prefixWord, tailWord_6647490, baseEnd_6647490] using wordTrace_append hprefix tailTrace_6647490
  have hstable : (prefixWord ++ tailWord_6647490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647490).length < 2 ^ (prefixWord ++ tailWord_6647490).sum := by decide
  have hdescent : baseEnd_6647490 < baseStart_6647490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647492 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6647492 : Nat := 118140960795 + 6647492 * 2 ^ 59
def prefixEnd_6647492 : Nat := 4983230072969 + 3 ^ 40 * 6647492 * 2
def baseEnd_6647492 : Nat := 3413358542917610890678747

theorem tailTrace_6647492 : CollatzResearch.WordTrace tailWord_6647492 prefixEnd_6647492 3413358542917610890678747 := by
  unfold tailWord_6647492
  simp only [CollatzResearch.WordTrace]
  refine ⟨121226975816639630046380365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161635967755519506728507153 121226975816639630046380365)
  ·
    refine ⟨45460115931239861267392637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121226975816639630046380365 45460115931239861267392637)
    ·
      refine ⟨17047543474214947975272239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45460115931239861267392637 17047543474214947975272239)
      ·
        refine ⟨25571315211322421962908359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17047543474214947975272239 25571315211322421962908359)
        ·
          refine ⟨38356972816983632944362539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25571315211322421962908359 38356972816983632944362539)
          ·
            refine ⟨57535459225475449416543809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38356972816983632944362539 57535459225475449416543809)
            ·
              refine ⟨43151594419106587062407857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57535459225475449416543809 43151594419106587062407857)
              ·
                refine ⟨32363695814329940296805893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43151594419106587062407857 32363695814329940296805893)
                ·
                  refine ⟨6068192965186863805651105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32363695814329940296805893 6068192965186863805651105)
                  ·
                    refine ⟨4551144723890147854238329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068192965186863805651105 4551144723890147854238329)
                    ·
                      refine ⟨3413358542917610890678747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551144723890147854238329 3413358542917610890678747)
                      ·
                        rfl

theorem cell23_6647492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6647492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647492 prefixEnd_6647492 := by exact prefixLift 6647492
  have htrace : WordTrace (prefixWord ++ tailWord_6647492) baseStart_6647492 baseEnd_6647492 := by
    simpa [prefixWord, tailWord_6647492, baseEnd_6647492] using wordTrace_append hprefix tailTrace_6647492
  have hstable : (prefixWord ++ tailWord_6647492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647492).length < 2 ^ (prefixWord ++ tailWord_6647492).sum := by decide
  have hdescent : baseEnd_6647492 < baseStart_6647492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647528 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6647528 : Nat := 118140960795 + 6647528 * 2 ^ 59
def prefixEnd_6647528 : Nat := 4983230072969 + 3 ^ 40 * 6647528 * 2
def baseEnd_6647528 : Nat := 1137792342740390916609527

theorem tailTrace_6647528 : CollatzResearch.WordTrace tailWord_6647528 prefixEnd_6647528 1137792342740390916609527 := by
  unfold tailWord_6647528
  simp only [CollatzResearch.WordTrace]
  refine ⟨121227632330574419120535619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161636843107432558827380825 121227632330574419120535619)
  ·
    refine ⟨181841448495861628680803429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121227632330574419120535619 181841448495861628680803429)
    ·
      refine ⟨34095271592974055377650643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181841448495861628680803429 34095271592974055377650643)
      ·
        refine ⟨51142907389461083066475965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34095271592974055377650643 51142907389461083066475965)
        ·
          refine ⟨19178590271047906149928487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51142907389461083066475965 19178590271047906149928487)
          ·
            refine ⟨28767885406571859224892731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19178590271047906149928487 28767885406571859224892731)
            ·
              refine ⟨43151828109857788837339097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28767885406571859224892731 43151828109857788837339097)
              ·
                refine ⟨32363871082393341628004323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43151828109857788837339097 32363871082393341628004323)
                ·
                  refine ⟨48545806623590012442006485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32363871082393341628004323 48545806623590012442006485)
                  ·
                    refine ⟨1137792342740390916609527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48545806623590012442006485 1137792342740390916609527)
                    ·
                      rfl

theorem cell23_6647528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6647528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647528 prefixEnd_6647528 := by exact prefixLift 6647528
  have htrace : WordTrace (prefixWord ++ tailWord_6647528) baseStart_6647528 baseEnd_6647528 := by
    simpa [prefixWord, tailWord_6647528, baseEnd_6647528] using wordTrace_append hprefix tailTrace_6647528
  have hstable : (prefixWord ++ tailWord_6647528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647528).length < 2 ^ (prefixWord ++ tailWord_6647528).sum := by decide
  have hdescent : baseEnd_6647528 < baseStart_6647528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647548 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_6647548 : Nat := 118140960795 + 6647548 * 2 ^ 59
def prefixEnd_6647548 : Nat := 4983230072969 + 3 ^ 40 * 6647548 * 2
def baseEnd_6647548 : Nat := 3413387297834262671578489

theorem tailTrace_6647548 : CollatzResearch.WordTrace tailWord_6647548 prefixEnd_6647548 3413387297834262671578489 := by
  unfold tailWord_6647548
  simp only [CollatzResearch.WordTrace]
  refine ⟨121227997060538190828399649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161637329414050921104532865 121227997060538190828399649)
  ·
    refine ⟨90920997795403643121299737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121227997060538190828399649 90920997795403643121299737)
    ·
      refine ⟨68190748346552732340974803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90920997795403643121299737 68190748346552732340974803)
      ·
        refine ⟨102286122519829098511462205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68190748346552732340974803 102286122519829098511462205)
        ·
          refine ⟨38357295944935911941798327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102286122519829098511462205 38357295944935911941798327)
          ·
            refine ⟨57535943917403867912697491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38357295944935911941798327 57535943917403867912697491)
            ·
              refine ⟨86303915876105801869046237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57535943917403867912697491 86303915876105801869046237)
              ·
                refine ⟨32363968453539675700892339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86303915876105801869046237 32363968453539675700892339)
                ·
                  refine ⟨48545952680309513551338509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32363968453539675700892339 48545952680309513551338509)
                  ·
                    refine ⟨18204732255116067581751941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48545952680309513551338509 18204732255116067581751941)
                    ·
                      refine ⟨3413387297834262671578489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18204732255116067581751941 3413387297834262671578489)
                      ·
                        rfl

theorem cell23_6647548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_6647548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647548 prefixEnd_6647548 := by exact prefixLift 6647548
  have htrace : WordTrace (prefixWord ++ tailWord_6647548) baseStart_6647548 baseEnd_6647548 := by
    simpa [prefixWord, tailWord_6647548, baseEnd_6647548] using wordTrace_append hprefix tailTrace_6647548
  have hstable : (prefixWord ++ tailWord_6647548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647548).length < 2 ^ (prefixWord ++ tailWord_6647548).sum := by decide
  have hdescent : baseEnd_6647548 < baseStart_6647548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647602 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_6647602 : Nat := 118140960795 + 6647602 * 2 ^ 59
def prefixEnd_6647602 : Nat := 4983230072969 + 3 ^ 40 * 6647602 * 2
def baseEnd_6647602 : Nat := 3413415025789605460303241

theorem tailTrace_6647602 : CollatzResearch.WordTrace tailWord_6647602 prefixEnd_6647602 3413415025789605460303241 := by
  unfold tailWord_6647602
  simp only [CollatzResearch.WordTrace]
  refine ⟨60614490915720187219816265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161638642441920499252843373 60614490915720187219816265)
  ·
    refine ⟨45460868186790140414862199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60614490915720187219816265 45460868186790140414862199)
    ·
      refine ⟨68191302280185210622293299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45460868186790140414862199 68191302280185210622293299)
      ·
        refine ⟨102286953420277815933439949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68191302280185210622293299 102286953420277815933439949)
        ·
          refine ⟨38357607532604180975039981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102286953420277815933439949 38357607532604180975039981)
          ·
            refine ⟨14384102824726567865639993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38357607532604180975039981 14384102824726567865639993)
            ·
              refine ⟨10788077118544925899229995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384102824726567865639993 10788077118544925899229995)
              ·
                refine ⟨16182115677817388848844993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788077118544925899229995 16182115677817388848844993)
                ·
                  refine ⟨12136586758363041636633745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16182115677817388848844993 12136586758363041636633745)
                  ·
                    refine ⟨9102440068772281227475309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12136586758363041636633745 9102440068772281227475309)
                    ·
                      refine ⟨3413415025789605460303241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102440068772281227475309 3413415025789605460303241)
                      ·
                        rfl

theorem cell23_6647602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_6647602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647602 prefixEnd_6647602 := by exact prefixLift 6647602
  have htrace : WordTrace (prefixWord ++ tailWord_6647602) baseStart_6647602 baseEnd_6647602 := by
    simpa [prefixWord, tailWord_6647602, baseEnd_6647602] using wordTrace_append hprefix tailTrace_6647602
  have hstable : (prefixWord ++ tailWord_6647602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647602).length < 2 ^ (prefixWord ++ tailWord_6647602).sum := by decide
  have hdescent : baseEnd_6647602 < baseStart_6647602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647655 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6647655 : Nat := 118140960795 + 6647655 * 2 ^ 59
def prefixEnd_6647655 : Nat := 4983230072969 + 3 ^ 40 * 6647655 * 2
def baseEnd_6647655 : Nat := 3413442240264293752940497

theorem tailTrace_6647655 : CollatzResearch.WordTrace tailWord_6647655 prefixEnd_6647655 3413442240264293752940497 := by
  unfold tailWord_6647655
  simp only [CollatzResearch.WordTrace]
  refine ⟨242459896731688738930944419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161639931154459159287296279 242459896731688738930944419)
  ·
    refine ⟨363689845097533108396416629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242459896731688738930944419 363689845097533108396416629)
    ·
      refine ⟨34095922977893728912164059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363689845097533108396416629 34095922977893728912164059)
      ·
        refine ⟨51143884466840593368246089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34095922977893728912164059 51143884466840593368246089)
        ·
          refine ⟨38357913350130445026184567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51143884466840593368246089 38357913350130445026184567)
          ·
            refine ⟨57536870025195667539276851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38357913350130445026184567 57536870025195667539276851)
            ·
              refine ⟨86305305037793501308915277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57536870025195667539276851 86305305037793501308915277)
              ·
                refine ⟨32364489389172562990843229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86305305037793501308915277 32364489389172562990843229)
                ·
                  refine ⟨12136683520939711121566211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32364489389172562990843229 12136683520939711121566211)
                  ·
                    refine ⟨18205025281409566682349317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12136683520939711121566211 18205025281409566682349317)
                    ·
                      refine ⟨3413442240264293752940497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18205025281409566682349317 3413442240264293752940497)
                      ·
                        rfl

theorem cell23_6647655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6647655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647655 prefixEnd_6647655 := by exact prefixLift 6647655
  have htrace : WordTrace (prefixWord ++ tailWord_6647655) baseStart_6647655 baseEnd_6647655 := by
    simpa [prefixWord, tailWord_6647655, baseEnd_6647655] using wordTrace_append hprefix tailTrace_6647655
  have hstable : (prefixWord ++ tailWord_6647655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647655).length < 2 ^ (prefixWord ++ tailWord_6647655).sum := by decide
  have hdescent : baseEnd_6647655 < baseStart_6647655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647665 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_6647665 : Nat := 118140960795 + 6647665 * 2 ^ 59
def prefixEnd_6647665 : Nat := 4983230072969 + 3 ^ 40 * 6647665 * 2
def baseEnd_6647665 : Nat := 1137815791690279571271817

theorem tailTrace_6647665 : CollatzResearch.WordTrace tailWord_6647665 prefixEnd_6647665 1137815791690279571271817 := by
  unfold tailWord_6647665
  simp only [CollatzResearch.WordTrace]
  refine ⟨242460261461652510638808449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161640174307768340425872299 242460261461652510638808449)
  ·
    refine ⟨181845196096239382979106337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242460261461652510638808449 181845196096239382979106337)
    ·
      refine ⟨136383897072179537234329753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181845196096239382979106337 136383897072179537234329753)
      ·
        refine ⟨102287922804134652925747315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136383897072179537234329753 102287922804134652925747315)
        ·
          refine ⟨153431884206201979388620973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102287922804134652925747315 153431884206201979388620973)
          ·
            refine ⟨57536956577325742270732865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153431884206201979388620973 57536956577325742270732865)
            ·
              refine ⟨43152717432994306703049649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57536956577325742270732865 43152717432994306703049649)
              ·
                refine ⟨32364538074745730027287237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43152717432994306703049649 32364538074745730027287237)
                ·
                  refine ⟨6068350889014824380116357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32364538074745730027287237 6068350889014824380116357)
                  ·
                    refine ⟨1137815791690279571271817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068350889014824380116357 1137815791690279571271817)
                    ·
                      rfl

theorem cell23_6647665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_6647665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647665 prefixEnd_6647665 := by exact prefixLift 6647665
  have htrace : WordTrace (prefixWord ++ tailWord_6647665) baseStart_6647665 baseEnd_6647665 := by
    simpa [prefixWord, tailWord_6647665, baseEnd_6647665] using wordTrace_append hprefix tailTrace_6647665
  have hstable : (prefixWord ++ tailWord_6647665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647665).length < 2 ^ (prefixWord ++ tailWord_6647665).sum := by decide
  have hdescent : baseEnd_6647665 < baseStart_6647665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647689 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 3, 2, 2]
def baseStart_6647689 : Nat := 118140960795 + 6647689 * 2 ^ 59
def prefixEnd_6647689 : Nat := 4983230072969 + 3 ^ 40 * 6647689 * 2
def baseEnd_6647689 : Nat := 3413459698606546619915341

theorem tailTrace_6647689 : CollatzResearch.WordTrace tailWord_6647689 prefixEnd_6647689 3413459698606546619915341 := by
  unfold tailWord_6647689
  simp only [CollatzResearch.WordTrace]
  refine ⟨242461136813565562737682121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161640757875710375158454747 242461136813565562737682121)
  ·
    refine ⟨181845852610174172053261591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242461136813565562737682121 181845852610174172053261591)
    ·
      refine ⟨272768778915261258079892387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181845852610174172053261591 272768778915261258079892387)
      ·
        refine ⟨409153168372891887119838581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272768778915261258079892387 409153168372891887119838581)
        ·
          refine ⟨38358109534958614417484867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409153168372891887119838581 38358109534958614417484867)
          ·
            refine ⟨57537164302437921626227301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38358109534958614417484867 57537164302437921626227301)
            ·
              refine ⟨10788218306707110304917619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57537164302437921626227301 10788218306707110304917619)
              ·
                refine ⟨16182327460060665457376429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788218306707110304917619 16182327460060665457376429)
                ·
                  refine ⟨6068372797522749546516161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16182327460060665457376429 6068372797522749546516161)
                  ·
                    refine ⟨4551279598142062159887121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068372797522749546516161 4551279598142062159887121)
                    ·
                      refine ⟨3413459698606546619915341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551279598142062159887121 3413459698606546619915341)
                      ·
                        rfl

theorem cell23_6647689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2, 2].length) (baseStart_6647689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647689 prefixEnd_6647689 := by exact prefixLift 6647689
  have htrace : WordTrace (prefixWord ++ tailWord_6647689) baseStart_6647689 baseEnd_6647689 := by
    simpa [prefixWord, tailWord_6647689, baseEnd_6647689] using wordTrace_append hprefix tailTrace_6647689
  have hstable : (prefixWord ++ tailWord_6647689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647689).length < 2 ^ (prefixWord ++ tailWord_6647689).sum := by decide
  have hdescent : baseEnd_6647689 < baseStart_6647689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647709 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_6647709 : Nat := 118140960795 + 6647709 * 2 ^ 59
def prefixEnd_6647709 : Nat := 4983230072969 + 3 ^ 40 * 6647709 * 2
def baseEnd_6647709 : Nat := 3413469968219636541665249

theorem tailTrace_6647709 : CollatzResearch.WordTrace tailWord_6647709 prefixEnd_6647709 3413469968219636541665249 := by
  unfold tailWord_6647709
  simp only [CollatzResearch.WordTrace]
  refine ⟨242461866273493106153410181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161641244182328737435606787 242461866273493106153410181)
  ·
    refine ⟨45461599926279957403764409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242461866273493106153410181 45461599926279957403764409)
    ·
      refine ⟨34096199944709968052823307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45461599926279957403764409 34096199944709968052823307)
      ·
        refine ⟨51144299917064952079234961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34096199944709968052823307 51144299917064952079234961)
        ·
          refine ⟨38358224937798714059426221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51144299917064952079234961 38358224937798714059426221)
          ·
            refine ⟨14384334351674517772284833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38358224937798714059426221 14384334351674517772284833)
            ·
              refine ⟨10788250763755888329213625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384334351674517772284833 10788250763755888329213625)
              ·
                refine ⟨8091188072816916246910219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788250763755888329213625 8091188072816916246910219)
                ·
                  refine ⟨12136782109225374370365329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091188072816916246910219 12136782109225374370365329)
                  ·
                    refine ⟨9102586581919030777773997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12136782109225374370365329 9102586581919030777773997)
                    ·
                      refine ⟨3413469968219636541665249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102586581919030777773997 3413469968219636541665249)
                      ·
                        rfl

theorem cell23_6647709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_6647709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647709 prefixEnd_6647709 := by exact prefixLift 6647709
  have htrace : WordTrace (prefixWord ++ tailWord_6647709) baseStart_6647709 baseEnd_6647709 := by
    simpa [prefixWord, tailWord_6647709, baseEnd_6647709] using wordTrace_append hprefix tailTrace_6647709
  have hstable : (prefixWord ++ tailWord_6647709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647709).length < 2 ^ (prefixWord ++ tailWord_6647709).sum := by decide
  have hdescent : baseEnd_6647709 < baseStart_6647709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647728 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_6647728 : Nat := 118140960795 + 6647728 * 2 ^ 59
def prefixEnd_6647728 : Nat := 4983230072969 + 3 ^ 40 * 6647728 * 2
def baseEnd_6647728 : Nat := 3413479724352071967327661

theorem tailTrace_6647728 : CollatzResearch.WordTrace tailWord_6647728 prefixEnd_6647728 3413479724352071967327661 := by
  unfold tailWord_6647728
  simp only [CollatzResearch.WordTrace]
  refine ⟨121231279630212136199175919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161641706173616181598901225 121231279630212136199175919)
  ·
    refine ⟨181846919445318204298763879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121231279630212136199175919 181846919445318204298763879)
    ·
      refine ⟨272770379167977306448145819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181846919445318204298763879 272770379167977306448145819)
      ·
        refine ⟨409155568751965959672218729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272770379167977306448145819 409155568751965959672218729)
        ·
          refine ⟨306866676563974469754164047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409155568751965959672218729 306866676563974469754164047)
          ·
            refine ⟨460300014845961704631246071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306866676563974469754164047 460300014845961704631246071)
            ·
              refine ⟨690450022268942556946869107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460300014845961704631246071 690450022268942556946869107)
              ·
                refine ⟨1035675033403413835420303661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690450022268942556946869107 1035675033403413835420303661)
                ·
                  refine ⟨388378137526280188282613873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035675033403413835420303661 388378137526280188282613873)
                  ·
                    refine ⟨291283603144710141211960405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 388378137526280188282613873 291283603144710141211960405)
                    ·
                      refine ⟨3413479724352071967327661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291283603144710141211960405 3413479724352071967327661)
                      ·
                        rfl

theorem cell23_6647728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_6647728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647728 prefixEnd_6647728 := by exact prefixLift 6647728
  have htrace : WordTrace (prefixWord ++ tailWord_6647728) baseStart_6647728 baseEnd_6647728 := by
    simpa [prefixWord, tailWord_6647728, baseEnd_6647728] using wordTrace_append hprefix tailTrace_6647728
  have hstable : (prefixWord ++ tailWord_6647728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647728).length < 2 ^ (prefixWord ++ tailWord_6647728).sum := by decide
  have hdescent : baseEnd_6647728 < baseStart_6647728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647740 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6647740 : Nat := 118140960795 + 6647740 * 2 ^ 59
def prefixEnd_6647740 : Nat := 4983230072969 + 3 ^ 40 * 6647740 * 2
def baseEnd_6647740 : Nat := 3413485886119925920377607

theorem tailTrace_6647740 : CollatzResearch.WordTrace tailWord_6647740 prefixEnd_6647740 3413485886119925920377607 := by
  unfold tailWord_6647740
  simp only [CollatzResearch.WordTrace]
  refine ⟨121231498468190399223894337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161641997957587198965192449 121231498468190399223894337)
  ·
    refine ⟨90923623851142799417920753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121231498468190399223894337 90923623851142799417920753)
    ·
      refine ⟨68192717888357099563440565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90923623851142799417920753 68192717888357099563440565)
      ·
        refine ⟨6393067302033478084072553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68192717888357099563440565 6393067302033478084072553)
        ·
          refine ⟨4794800476525108563054415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393067302033478084072553 4794800476525108563054415)
          ·
            refine ⟨7192200714787662844581623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794800476525108563054415 7192200714787662844581623)
            ·
              refine ⟨10788301072181494266872435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192200714787662844581623 10788301072181494266872435)
              ·
                refine ⟨16182451608272241400308653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788301072181494266872435 16182451608272241400308653)
                ·
                  refine ⟨6068419353102090525115745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16182451608272241400308653 6068419353102090525115745)
                  ·
                    refine ⟨4551314514826567893836809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068419353102090525115745 4551314514826567893836809)
                    ·
                      refine ⟨3413485886119925920377607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551314514826567893836809 3413485886119925920377607)
                      ·
                        rfl

theorem cell23_6647740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6647740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647740 prefixEnd_6647740 := by exact prefixLift 6647740
  have htrace : WordTrace (prefixWord ++ tailWord_6647740) baseStart_6647740 baseEnd_6647740 := by
    simpa [prefixWord, tailWord_6647740, baseEnd_6647740] using wordTrace_append hprefix tailTrace_6647740
  have hstable : (prefixWord ++ tailWord_6647740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647740).length < 2 ^ (prefixWord ++ tailWord_6647740).sum := by decide
  have hdescent : baseEnd_6647740 < baseStart_6647740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647756 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6647756 : Nat := 118140960795 + 6647756 * 2 ^ 59
def prefixEnd_6647756 : Nat := 4983230072969 + 3 ^ 40 * 6647756 * 2
def baseEnd_6647756 : Nat := 3413494101810397857777533

theorem tailTrace_6647756 : CollatzResearch.WordTrace tailWord_6647756 prefixEnd_6647756 3413494101810397857777533 := by
  unfold tailWord_6647756
  simp only [CollatzResearch.WordTrace]
  refine ⟨121231790252161416590185561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161642387002881888786914081 121231790252161416590185561)
  ·
    refine ⟨90923842689121062442639171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121231790252161416590185561 90923842689121062442639171)
    ·
      refine ⟨136385764033681593663958757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90923842689121062442639171 136385764033681593663958757)
      ·
        refine ⟨25572330756315298811992267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136385764033681593663958757 25572330756315298811992267)
        ·
          refine ⟨38358496134472948217988401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25572330756315298811992267 38358496134472948217988401)
          ·
            refine ⟨28768872100854711163491301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38358496134472948217988401 28768872100854711163491301)
            ·
              refine ⟨5394163518910258343154619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28768872100854711163491301 5394163518910258343154619)
              ·
                refine ⟨8091245278365387514731929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394163518910258343154619 8091245278365387514731929)
                ·
                  refine ⟨6068433958774040636048947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091245278365387514731929 6068433958774040636048947)
                  ·
                    refine ⟨9102650938161060954073421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068433958774040636048947 9102650938161060954073421)
                    ·
                      refine ⟨3413494101810397857777533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102650938161060954073421 3413494101810397857777533)
                      ·
                        rfl

theorem cell23_6647756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6647756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647756 prefixEnd_6647756 := by exact prefixLift 6647756
  have htrace : WordTrace (prefixWord ++ tailWord_6647756) baseStart_6647756 baseEnd_6647756 := by
    simpa [prefixWord, tailWord_6647756, baseEnd_6647756] using wordTrace_append hprefix tailTrace_6647756
  have hstable : (prefixWord ++ tailWord_6647756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647756).length < 2 ^ (prefixWord ++ tailWord_6647756).sum := by decide
  have hdescent : baseEnd_6647756 < baseStart_6647756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647779 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6647779 : Nat := 118140960795 + 6647779 * 2 ^ 59
def prefixEnd_6647779 : Nat := 4983230072969 + 3 ^ 40 * 6647779 * 2
def baseEnd_6647779 : Nat := 3413505911865451267789927

theorem tailTrace_6647779 : CollatzResearch.WordTrace tailWord_6647779 prefixEnd_6647779 3413505911865451267789927 := by
  unfold tailWord_6647779
  simp only [CollatzResearch.WordTrace]
  refine ⟨242464419383239508108458391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161642946255493005405638927 242464419383239508108458391)
  ·
    refine ⟨363696629074859262162687587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242464419383239508108458391 363696629074859262162687587)
    ·
      refine ⟨545544943612288893244031381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363696629074859262162687587 545544943612288893244031381)
      ·
        refine ⟨25572419231826041870813971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 545544943612288893244031381 25572419231826041870813971)
        ·
          refine ⟨38358628847739062806220957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25572419231826041870813971 38358628847739062806220957)
          ·
            refine ⟨14384485817902148552332859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38358628847739062806220957 14384485817902148552332859)
            ·
              refine ⟨21576728726853222828499289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384485817902148552332859 21576728726853222828499289)
              ·
                refine ⟨16182546545139917121374467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21576728726853222828499289 16182546545139917121374467)
                ·
                  refine ⟨24273819817709875682061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16182546545139917121374467 24273819817709875682061701)
                  ·
                    refine ⟨4551341215820601690386569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24273819817709875682061701 4551341215820601690386569)
                    ·
                      refine ⟨3413505911865451267789927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551341215820601690386569 3413505911865451267789927)
                      ·
                        rfl

theorem cell23_6647779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6647779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647779 prefixEnd_6647779 := by exact prefixLift 6647779
  have htrace : WordTrace (prefixWord ++ tailWord_6647779) baseStart_6647779 baseEnd_6647779 := by
    simpa [prefixWord, tailWord_6647779, baseEnd_6647779] using wordTrace_append hprefix tailTrace_6647779
  have hstable : (prefixWord ++ tailWord_6647779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647779).length < 2 ^ (prefixWord ++ tailWord_6647779).sum := by decide
  have hdescent : baseEnd_6647779 < baseStart_6647779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647783 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6647783 : Nat := 118140960795 + 6647783 * 2 ^ 59
def prefixEnd_6647783 : Nat := 4983230072969 + 3 ^ 40 * 6647783 * 2
def baseEnd_6647783 : Nat := 3413507965788069252139909

theorem tailTrace_6647783 : CollatzResearch.WordTrace tailWord_6647783 prefixEnd_6647783 3413507965788069252139909 := by
  unfold tailWord_6647783
  simp only [CollatzResearch.WordTrace]
  refine ⟨242464565275225016791604003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161643043516816677861069335 242464565275225016791604003)
  ·
    refine ⟨363696847912837525187406005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242464565275225016791604003 363696847912837525187406005)
    ·
      refine ⟨34096579491828517986319313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363696847912837525187406005 34096579491828517986319313)
      ·
        refine ⟨25572434618871388489739485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34096579491828517986319313 25572434618871388489739485)
        ·
          refine ⟨9589662982076770683652307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25572434618871388489739485 9589662982076770683652307)
          ·
            refine ⟨14384494473115156025478461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589662982076770683652307 14384494473115156025478461)
            ·
              refine ⟨5394185427418183509554423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14384494473115156025478461 5394185427418183509554423)
              ·
                refine ⟨8091278141127275264331635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394185427418183509554423 8091278141127275264331635)
                ·
                  refine ⟨12136917211690912896497453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091278141127275264331635 12136917211690912896497453)
                  ·
                    refine ⟨4551343954384092336186545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12136917211690912896497453 4551343954384092336186545)
                    ·
                      refine ⟨3413507965788069252139909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551343954384092336186545 3413507965788069252139909)
                      ·
                        rfl

theorem cell23_6647783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6647783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647783 prefixEnd_6647783 := by exact prefixLift 6647783
  have htrace : WordTrace (prefixWord ++ tailWord_6647783) baseStart_6647783 baseEnd_6647783 := by
    simpa [prefixWord, tailWord_6647783, baseEnd_6647783] using wordTrace_append hprefix tailTrace_6647783
  have hstable : (prefixWord ++ tailWord_6647783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647783).length < 2 ^ (prefixWord ++ tailWord_6647783).sum := by decide
  have hdescent : baseEnd_6647783 < baseStart_6647783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647795 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3]
def baseStart_6647795 : Nat := 118140960795 + 6647795 * 2 ^ 59
def prefixEnd_6647795 : Nat := 4983230072969 + 3 ^ 40 * 6647795 * 2
def baseEnd_6647795 : Nat := 3413514127555923205189853

theorem tailTrace_6647795 : CollatzResearch.WordTrace tailWord_6647795 prefixEnd_6647795 3413514127555923205189853 := by
  unfold tailWord_6647795
  simp only [CollatzResearch.WordTrace]
  refine ⟨242465002951181542841040839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161643335300787695227360559 242465002951181542841040839)
  ·
    refine ⟨363697504426772314261561259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242465002951181542841040839 363697504426772314261561259)
    ·
      refine ⟨545546256640158471392341889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363697504426772314261561259 545546256640158471392341889)
      ·
        refine ⟨409159692480118853544256417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545546256640158471392341889 409159692480118853544256417)
        ·
          refine ⟨306869769360089140158192313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409159692480118853544256417 306869769360089140158192313)
          ·
            refine ⟨230152327020066855118644235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306869769360089140158192313 230152327020066855118644235)
            ·
              refine ⟨345228490530100282677966353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230152327020066855118644235 345228490530100282677966353)
              ·
                refine ⟨258921367897575212008474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345228490530100282677966353 258921367897575212008474765)
                ·
                  refine ⟨97095512961590704503178037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258921367897575212008474765 97095512961590704503178037)
                  ·
                    refine ⟨9102704340149128547172941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97095512961590704503178037 9102704340149128547172941)
                    ·
                      refine ⟨3413514127555923205189853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102704340149128547172941 3413514127555923205189853)
                      ·
                        rfl

theorem cell23_6647795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_6647795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647795 prefixEnd_6647795 := by exact prefixLift 6647795
  have htrace : WordTrace (prefixWord ++ tailWord_6647795) baseStart_6647795 baseEnd_6647795 := by
    simpa [prefixWord, tailWord_6647795, baseEnd_6647795] using wordTrace_append hprefix tailTrace_6647795
  have hstable : (prefixWord ++ tailWord_6647795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647795).length < 2 ^ (prefixWord ++ tailWord_6647795).sum := by decide
  have hdescent : baseEnd_6647795 < baseStart_6647795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647847 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6647847 : Nat := 118140960795 + 6647847 * 2 ^ 59
def prefixEnd_6647847 : Nat := 4983230072969 + 3 ^ 40 * 6647847 * 2
def baseEnd_6647847 : Nat := 3413540828549957001739615

theorem tailTrace_6647847 : CollatzResearch.WordTrace tailWord_6647847 prefixEnd_6647847 3413540828549957001739615 := by
  unfold tailWord_6647847
  simp only [CollatzResearch.WordTrace]
  refine ⟨242466899546993155721933795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161644599697995437147955863 242466899546993155721933795)
  ·
    refine ⟨363700349320489733582900693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242466899546993155721933795 363700349320489733582900693)
    ·
      refine ⟨8524226937198978130849235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 363700349320489733582900693 8524226937198978130849235)
      ·
        refine ⟨12786340405798467196273853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524226937198978130849235 12786340405798467196273853)
        ·
          refine ⟨4794877652174425198602695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12786340405798467196273853 4794877652174425198602695)
          ·
            refine ⟨7192316478261637797904043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794877652174425198602695 7192316478261637797904043)
            ·
              refine ⟨10788474717392456696856065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192316478261637797904043 10788474717392456696856065)
              ·
                refine ⟨8091356038044342522642049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788474717392456696856065 8091356038044342522642049)
                ·
                  refine ⟨6068517028533256891981537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091356038044342522642049 6068517028533256891981537)
                  ·
                    refine ⟨4551387771399942668986153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068517028533256891981537 4551387771399942668986153)
                    ·
                      refine ⟨3413540828549957001739615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551387771399942668986153 3413540828549957001739615)
                      ·
                        rfl

theorem cell23_6647847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6647847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647847 prefixEnd_6647847 := by exact prefixLift 6647847
  have htrace : WordTrace (prefixWord ++ tailWord_6647847) baseStart_6647847 baseEnd_6647847 := by
    simpa [prefixWord, tailWord_6647847, baseEnd_6647847] using wordTrace_append hprefix tailTrace_6647847
  have hstable : (prefixWord ++ tailWord_6647847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647847).length < 2 ^ (prefixWord ++ tailWord_6647847).sum := by decide
  have hdescent : baseEnd_6647847 < baseStart_6647847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647869 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6647869 : Nat := 118140960795 + 6647869 * 2 ^ 59
def prefixEnd_6647869 : Nat := 4983230072969 + 3 ^ 40 * 6647869 * 2
def baseEnd_6647869 : Nat := 3413552125124355915664513

theorem tailTrace_6647869 : CollatzResearch.WordTrace tailWord_6647869 prefixEnd_6647869 3413552125124355915664513 := by
  unfold tailWord_6647869
  simp only [CollatzResearch.WordTrace]
  refine ⟨242467701952913453479234661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161645134635275635652823107 242467701952913453479234661)
  ·
    refine ⟨45462694116171272527356499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242467701952913453479234661 45462694116171272527356499)
    ·
      refine ⟨68194041174256908791034749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45462694116171272527356499 68194041174256908791034749)
      ·
        refine ⟨25572765440346340796638031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68194041174256908791034749 25572765440346340796638031)
        ·
          refine ⟨38359148160519511194957047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25572765440346340796638031 38359148160519511194957047)
          ·
            refine ⟨57538722240779266792435571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38359148160519511194957047 57538722240779266792435571)
            ·
              refine ⟨86308083361168900188653357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57538722240779266792435571 86308083361168900188653357)
              ·
                refine ⟨32365531260438337570745009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86308083361168900188653357 32365531260438337570745009)
                ·
                  refine ⟨24274148445328753178058757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32365531260438337570745009 24274148445328753178058757)
                  ·
                    refine ⟨4551402833499141220886017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24274148445328753178058757 4551402833499141220886017)
                    ·
                      refine ⟨3413552125124355915664513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551402833499141220886017 3413552125124355915664513)
                      ·
                        rfl

theorem cell23_6647869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6647869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647869 prefixEnd_6647869 := by exact prefixLift 6647869
  have htrace : WordTrace (prefixWord ++ tailWord_6647869) baseStart_6647869 baseEnd_6647869 := by
    simpa [prefixWord, tailWord_6647869, baseEnd_6647869] using wordTrace_append hprefix tailTrace_6647869
  have hstable : (prefixWord ++ tailWord_6647869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647869).length < 2 ^ (prefixWord ++ tailWord_6647869).sum := by decide
  have hdescent : baseEnd_6647869 < baseStart_6647869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647872 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_6647872 : Nat := 118140960795 + 6647872 * 2 ^ 59
def prefixEnd_6647872 : Nat := 4983230072969 + 3 ^ 40 * 6647872 * 2
def baseEnd_6647872 : Nat := 3413553665566319403926999

theorem tailTrace_6647872 : CollatzResearch.WordTrace tailWord_6647872 prefixEnd_6647872 3413553665566319403926999 := by
  unfold tailWord_6647872
  simp only [CollatzResearch.WordTrace]
  refine ⟨121233905685951292495796935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161645207581268389994395913 121233905685951292495796935)
  ·
    refine ⟨181850858528926938743695403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121233905685951292495796935 181850858528926938743695403)
    ·
      refine ⟨272776287793390408115543105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181850858528926938743695403 272776287793390408115543105)
      ·
        refine ⟨204582215845042806086657329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272776287793390408115543105 204582215845042806086657329)
        ·
          refine ⟨153436661883782104564992997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204582215845042806086657329 153436661883782104564992997)
          ·
            refine ⟨28769374103209144605936187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153436661883782104564992997 28769374103209144605936187)
            ·
              refine ⟨43154061154813716908904281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28769374103209144605936187 43154061154813716908904281)
              ·
                refine ⟨32365545866110287681678211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43154061154813716908904281 32365545866110287681678211)
                ·
                  refine ⟨48548318799165431522517317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32365545866110287681678211 48548318799165431522517317)
                  ·
                    refine ⟨9102809774843518410471997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48548318799165431522517317 9102809774843518410471997)
                    ·
                      refine ⟨3413553665566319403926999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102809774843518410471997 3413553665566319403926999)
                      ·
                        rfl

theorem cell23_6647872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_6647872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647872 prefixEnd_6647872 := by exact prefixLift 6647872
  have htrace : WordTrace (prefixWord ++ tailWord_6647872) baseStart_6647872 baseEnd_6647872 := by
    simpa [prefixWord, tailWord_6647872, baseEnd_6647872] using wordTrace_append hprefix tailTrace_6647872
  have hstable : (prefixWord ++ tailWord_6647872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647872).length < 2 ^ (prefixWord ++ tailWord_6647872).sum := by decide
  have hdescent : baseEnd_6647872 < baseStart_6647872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647896 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 1, 4]
def baseStart_6647896 : Nat := 118140960795 + 6647896 * 2 ^ 59
def prefixEnd_6647896 : Nat := 4983230072969 + 3 ^ 40 * 6647896 * 2
def baseEnd_6647896 : Nat := 1137855329700675770008963

theorem tailTrace_6647896 : CollatzResearch.WordTrace tailWord_6647896 prefixEnd_6647896 1137855329700675770008963 := by
  unfold tailWord_6647896
  simp only [CollatzResearch.WordTrace]
  refine ⟨121234343361907818545233771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161645791149210424726978361 121234343361907818545233771)
  ·
    refine ⟨181851515042861727817850657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121234343361907818545233771 181851515042861727817850657)
    ·
      refine ⟨136388636282146295863387993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181851515042861727817850657 136388636282146295863387993)
      ·
        refine ⟨102291477211609721897540995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136388636282146295863387993 102291477211609721897540995)
        ·
          refine ⟨153437215817414582846311493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102291477211609721897540995 153437215817414582846311493)
          ·
            refine ⟨28769477965765234283683405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153437215817414582846311493 28769477965765234283683405)
            ·
              refine ⟨10788554237161962856381277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28769477965765234283683405 10788554237161962856381277)
              ·
                refine ⟨4045707838935736071142979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10788554237161962856381277 4045707838935736071142979)
                ·
                  refine ⟨6068561758403604106714469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045707838935736071142979 6068561758403604106714469)
                  ·
                    refine ⟨1137855329700675770008963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068561758403604106714469 1137855329700675770008963)
                    ·
                      rfl

theorem cell23_6647896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_6647896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647896 prefixEnd_6647896 := by exact prefixLift 6647896
  have htrace : WordTrace (prefixWord ++ tailWord_6647896) baseStart_6647896 baseEnd_6647896 := by
    simpa [prefixWord, tailWord_6647896, baseEnd_6647896] using wordTrace_append hprefix tailTrace_6647896
  have hstable : (prefixWord ++ tailWord_6647896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647896).length < 2 ^ (prefixWord ++ tailWord_6647896).sum := by decide
  have hdescent : baseEnd_6647896 < baseStart_6647896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647926 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6647926 : Nat := 118140960795 + 6647926 * 2 ^ 59
def prefixEnd_6647926 : Nat := 4983230072969 + 3 ^ 40 * 6647926 * 2
def baseEnd_6647926 : Nat := 379286821502406910294639

theorem tailTrace_6647926 : CollatzResearch.WordTrace tailWord_6647926 prefixEnd_6647926 379286821502406910294639 := by
  unfold tailWord_6647926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15154361307106684513378727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161646520609137968142706421 15154361307106684513378727)
  ·
    refine ⟨22731541960660026770068091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15154361307106684513378727 22731541960660026770068091)
    ·
      refine ⟨34097312940990040155102137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22731541960660026770068091 34097312940990040155102137)
      ·
        refine ⟨25572984705742530116326603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34097312940990040155102137 25572984705742530116326603)
        ·
          refine ⟨38359477058613795174489905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25572984705742530116326603 38359477058613795174489905)
          ·
            refine ⟨28769607793960346380867429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38359477058613795174489905 28769607793960346380867429)
            ·
              refine ⟨5394301461367564946412643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28769607793960346380867429 5394301461367564946412643)
              ·
                refine ⟨8091452192051347419618965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394301461367564946412643 8091452192051347419618965)
                ·
                  refine ⟨379286821502406910294639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8091452192051347419618965 379286821502406910294639)
                  ·
                    rfl

theorem cell23_6647926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6647926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647926 prefixEnd_6647926 := by exact prefixLift 6647926
  have htrace : WordTrace (prefixWord ++ tailWord_6647926) baseStart_6647926 baseEnd_6647926 := by
    simpa [prefixWord, tailWord_6647926, baseEnd_6647926] using wordTrace_append hprefix tailTrace_6647926
  have hstable : (prefixWord ++ tailWord_6647926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647926).length < 2 ^ (prefixWord ++ tailWord_6647926).sum := by decide
  have hdescent : baseEnd_6647926 < baseStart_6647926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647939 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 1, 5]
def baseStart_6647939 : Nat := 118140960795 + 6647939 * 2 ^ 59
def prefixEnd_6647939 : Nat := 4983230072969 + 3 ^ 40 * 6647939 * 2
def baseEnd_6647939 : Nat := 1137862689590056880596397

theorem tailTrace_6647939 : CollatzResearch.WordTrace tailWord_6647939 prefixEnd_6647939 1137862689590056880596397 := by
  unfold tailWord_6647939
  simp only [CollatzResearch.WordTrace]
  refine ⟨242470255062659855434282871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161646836708439903622855247 242470255062659855434282871)
  ·
    refine ⟨363705382593989783151424307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242470255062659855434282871 363705382593989783151424307)
    ·
      refine ⟨545558073890984674727136461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363705382593989783151424307 545558073890984674727136461)
      ·
        refine ⟨204584277709119253022676173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545558073890984674727136461 204584277709119253022676173)
        ·
          refine ⟨76719104140919719883503565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204584277709119253022676173 76719104140919719883503565)
          ·
            refine ⟨28769664052844894956313837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76719104140919719883503565 28769664052844894956313837)
            ·
              refine ⟨10788624019816835608617689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28769664052844894956313837 10788624019816835608617689)
              ·
                refine ⟨8091468014862626706463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788624019816835608617689 8091468014862626706463267)
                ·
                  refine ⟨12137202022293940059694901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091468014862626706463267 12137202022293940059694901)
                  ·
                    refine ⟨1137862689590056880596397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12137202022293940059694901 1137862689590056880596397)
                    ·
                      rfl

theorem cell23_6647939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 5].length) (baseStart_6647939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647939 prefixEnd_6647939 := by exact prefixLift 6647939
  have htrace : WordTrace (prefixWord ++ tailWord_6647939) baseStart_6647939 baseEnd_6647939 := by
    simpa [prefixWord, tailWord_6647939, baseEnd_6647939] using wordTrace_append hprefix tailTrace_6647939
  have hstable : (prefixWord ++ tailWord_6647939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647939).length < 2 ^ (prefixWord ++ tailWord_6647939).sum := by decide
  have hdescent : baseEnd_6647939 < baseStart_6647939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647946 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_6647946 : Nat := 118140960795 + 6647946 * 2 ^ 59
def prefixEnd_6647946 : Nat := 4983230072969 + 3 ^ 40 * 6647946 * 2
def baseEnd_6647946 : Nat := 3413591663134752114401659

theorem tailTrace_6647946 : CollatzResearch.WordTrace tailWord_6647946 prefixEnd_6647946 3413591663134752114401659 := by
  unfold tailWord_6647946
  simp only [CollatzResearch.WordTrace]
  refine ⟨60617627593408623907446923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161647006915756330419858461 60617627593408623907446923)
  ·
    refine ⟨90926441390112935861170385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60617627593408623907446923 90926441390112935861170385)
    ·
      refine ⟨68194831042584701895877789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90926441390112935861170385 68194831042584701895877789)
      ·
        refine ⟨25573061640969263210954171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68194831042584701895877789 25573061640969263210954171)
        ·
          refine ⟨38359592461453894816431257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25573061640969263210954171 38359592461453894816431257)
          ·
            refine ⟨28769694346090421112323443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38359592461453894816431257 28769694346090421112323443)
            ·
              refine ⟨43154541519135631668485165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28769694346090421112323443 43154541519135631668485165)
              ·
                refine ⟨16182953069675861875681937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43154541519135631668485165 16182953069675861875681937)
                ·
                  refine ⟨12137214802256896406761453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16182953069675861875681937 12137214802256896406761453)
                  ·
                    refine ⟨4551455550846336152535545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12137214802256896406761453 4551455550846336152535545)
                    ·
                      refine ⟨3413591663134752114401659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551455550846336152535545 3413591663134752114401659)
                      ·
                        rfl

theorem cell23_6647946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_6647946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647946 prefixEnd_6647946 := by exact prefixLift 6647946
  have htrace : WordTrace (prefixWord ++ tailWord_6647946) baseStart_6647946 baseEnd_6647946 := by
    simpa [prefixWord, tailWord_6647946, baseEnd_6647946] using wordTrace_append hprefix tailTrace_6647946
  have hstable : (prefixWord ++ tailWord_6647946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647946).length < 2 ^ (prefixWord ++ tailWord_6647946).sum := by decide
  have hdescent : baseEnd_6647946 < baseStart_6647946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647952 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_6647952 : Nat := 118140960795 + 6647952 * 2 ^ 59
def prefixEnd_6647952 : Nat := 4983230072969 + 3 ^ 40 * 6647952 * 2
def baseEnd_6647952 : Nat := 1137864914672893030308877

theorem tailTrace_6647952 : CollatzResearch.WordTrace tailWord_6647952 prefixEnd_6647952 1137864914672893030308877 := by
  unfold tailWord_6647952
  simp only [CollatzResearch.WordTrace]
  refine ⟨121235364605806379327253055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161647152807741839103004073 121235364605806379327253055)
  ·
    refine ⟨181853046908709568990879583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121235364605806379327253055 181853046908709568990879583)
    ·
      refine ⟨272779570363064353486319375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181853046908709568990879583 272779570363064353486319375)
      ·
        refine ⟨409169355544596530229479063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272779570363064353486319375 409169355544596530229479063)
        ·
          refine ⟨613754033316894795344218595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409169355544596530229479063 613754033316894795344218595)
          ·
            refine ⟨920631049975342193016327893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613754033316894795344218595 920631049975342193016327893)
            ·
              refine ⟨21577290233797082648820185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 920631049975342193016327893 21577290233797082648820185)
              ·
                refine ⟨16182967675347811986615139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21577290233797082648820185 16182967675347811986615139)
                ·
                  refine ⟨24274451513021717979922709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16182967675347811986615139 24274451513021717979922709)
                  ·
                    refine ⟨1137864914672893030308877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24274451513021717979922709 1137864914672893030308877)
                    ·
                      rfl

theorem cell23_6647952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_6647952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647952 prefixEnd_6647952 := by exact prefixLift 6647952
  have htrace : WordTrace (prefixWord ++ tailWord_6647952) baseStart_6647952 baseEnd_6647952 := by
    simpa [prefixWord, tailWord_6647952, baseEnd_6647952] using wordTrace_append hprefix tailTrace_6647952
  have hstable : (prefixWord ++ tailWord_6647952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647952).length < 2 ^ (prefixWord ++ tailWord_6647952).sum := by decide
  have hdescent : baseEnd_6647952 < baseStart_6647952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6647970 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6647970 : Nat := 118140960795 + 6647970 * 2 ^ 59
def prefixEnd_6647970 : Nat := 4983230072969 + 3 ^ 40 * 6647970 * 2
def baseEnd_6647970 : Nat := 3413603986670460020501549

theorem tailTrace_6647970 : CollatzResearch.WordTrace tailWord_6647970 prefixEnd_6647970 3413603986670460020501549 := by
  unfold tailWord_6647970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60617846431386886932165341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161647590483698365152440909 60617846431386886932165341)
  ·
    refine ⟨22731692411770082599562003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60617846431386886932165341 22731692411770082599562003)
    ·
      refine ⟨34097538617655123899343005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22731692411770082599562003 34097538617655123899343005)
      ·
        refine ⟨12786576981620671462253627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34097538617655123899343005 12786576981620671462253627)
        ·
          refine ⟨19179865472431007193380441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786576981620671462253627 19179865472431007193380441)
          ·
            refine ⟨14384899104323255395035331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19179865472431007193380441 14384899104323255395035331)
            ·
              refine ⟨21577348656484883092552997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384899104323255395035331 21577348656484883092552997)
              ·
                refine ⟨4045752873090915579853687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21577348656484883092552997 4045752873090915579853687)
                ·
                  refine ⟨6068629309636373369780531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045752873090915579853687 6068629309636373369780531)
                  ·
                    refine ⟨9102943964454560054670797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068629309636373369780531 9102943964454560054670797)
                    ·
                      refine ⟨3413603986670460020501549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9102943964454560054670797 3413603986670460020501549)
                      ·
                        rfl

theorem cell23_6647970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6647970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6647970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6647970 prefixEnd_6647970 := by exact prefixLift 6647970
  have htrace : WordTrace (prefixWord ++ tailWord_6647970) baseStart_6647970 baseEnd_6647970 := by
    simpa [prefixWord, tailWord_6647970, baseEnd_6647970] using wordTrace_append hprefix tailTrace_6647970
  have hstable : (prefixWord ++ tailWord_6647970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6647970).length < 2 ^ (prefixWord ++ tailWord_6647970).sum := by decide
  have hdescent : baseEnd_6647970 < baseStart_6647970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6647970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648010 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_6648010 : Nat := 118140960795 + 6648010 * 2 ^ 59
def prefixEnd_6648010 : Nat := 4983230072969 + 3 ^ 40 * 6648010 * 2
def baseEnd_6648010 : Nat := 3413624525896639864001365

theorem tailTrace_6648010 : CollatzResearch.WordTrace tailWord_6648010 prefixEnd_6648010 3413624525896639864001365 := by
  unfold tailWord_6648010
  simp only [CollatzResearch.WordTrace]
  refine ⟨60618211161350658640029371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161648563096935089706744989 60618211161350658640029371)
  ·
    refine ⟨90927316742025987960044057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60618211161350658640029371 90927316742025987960044057)
    ·
      refine ⟨68195487556519490970033043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90927316742025987960044057 68195487556519490970033043)
      ·
        refine ⟨102293231334779236455049565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68195487556519490970033043 102293231334779236455049565)
        ·
          refine ⟨38359961750542213670643587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102293231334779236455049565 38359961750542213670643587)
          ·
            refine ⟨57539942625813320505965381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38359961750542213670643587 57539942625813320505965381)
            ·
              refine ⟨10788739242339997594868509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57539942625813320505965381 10788739242339997594868509)
              ·
                refine ⟨4045777215877499098075691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10788739242339997594868509 4045777215877499098075691)
                ·
                  refine ⟨6068665823816248647113537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045777215877499098075691 6068665823816248647113537)
                  ·
                    refine ⟨4551499367862186485335153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068665823816248647113537 4551499367862186485335153)
                    ·
                      refine ⟨3413624525896639864001365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551499367862186485335153 3413624525896639864001365)
                      ·
                        rfl

theorem cell23_6648010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_6648010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648010 prefixEnd_6648010 := by exact prefixLift 6648010
  have htrace : WordTrace (prefixWord ++ tailWord_6648010) baseStart_6648010 baseEnd_6648010 := by
    simpa [prefixWord, tailWord_6648010, baseEnd_6648010] using wordTrace_append hprefix tailTrace_6648010
  have hstable : (prefixWord ++ tailWord_6648010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648010).length < 2 ^ (prefixWord ++ tailWord_6648010).sum := by decide
  have hdescent : baseEnd_6648010 < baseStart_6648010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648043 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 2, 1, 3]
def baseStart_6648043 : Nat := 118140960795 + 6648043 * 2 ^ 59
def prefixEnd_6648043 : Nat := 4983230072969 + 3 ^ 40 * 6648043 * 2
def baseEnd_6648043 : Nat := 3413641470758238234888713

theorem tailTrace_6648043 : CollatzResearch.WordTrace tailWord_6648043 prefixEnd_6648043 3413641470758238234888713 := by
  unfold tailWord_6648043
  simp only [CollatzResearch.WordTrace]
  refine ⟨242474048254283081196068783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161649365502855387464045855 242474048254283081196068783)
  ·
    refine ⟨363711072381424621794103175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242474048254283081196068783 363711072381424621794103175)
    ·
      refine ⟨545566608572136932691154763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363711072381424621794103175 545566608572136932691154763)
      ·
        refine ⟨818349912858205399036732145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545566608572136932691154763 818349912858205399036732145)
        ·
          refine ⟨613762434643654049277549109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818349912858205399036732145 613762434643654049277549109)
          ·
            refine ⟨57540228247842567119770229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613762434643654049277549109 57540228247842567119770229)
            ·
              refine ⟨5394396398235240667478459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57540228247842567119770229 5394396398235240667478459)
              ·
                refine ⟨8091594597352861001217689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394396398235240667478459 8091594597352861001217689)
                ·
                  refine ⟨6068695948014645750913267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091594597352861001217689 6068695948014645750913267)
                  ·
                    refine ⟨9103043922021968626369901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068695948014645750913267 9103043922021968626369901)
                    ·
                      refine ⟨3413641470758238234888713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103043922021968626369901 3413641470758238234888713)
                      ·
                        rfl

theorem cell23_6648043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 2, 1, 3].length) (baseStart_6648043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648043 prefixEnd_6648043 := by exact prefixLift 6648043
  have htrace : WordTrace (prefixWord ++ tailWord_6648043) baseStart_6648043 baseEnd_6648043 := by
    simpa [prefixWord, tailWord_6648043, baseEnd_6648043] using wordTrace_append hprefix tailTrace_6648043
  have hstable : (prefixWord ++ tailWord_6648043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648043).length < 2 ^ (prefixWord ++ tailWord_6648043).sum := by decide
  have hdescent : baseEnd_6648043 < baseStart_6648043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648094 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6648094 : Nat := 118140960795 + 6648094 * 2 ^ 59
def prefixEnd_6648094 : Nat := 4983230072969 + 3 ^ 40 * 6648094 * 2
def baseEnd_6648094 : Nat := 3413667658271617535350979

theorem tailTrace_6648094 : CollatzResearch.WordTrace tailWord_6648094 prefixEnd_6648094 3413667658271617535350979 := by
  unfold tailWord_6648094
  simp only [CollatzResearch.WordTrace]
  refine ⟨30309488547137289613271917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161650605584732211270783557 30309488547137289613271917)
  ·
    refine ⟨11366058205176483604976969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30309488547137289613271917 11366058205176483604976969)
    ·
      refine ⟨8524543653882362703732727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366058205176483604976969 8524543653882362703732727)
      ·
        refine ⟨12786815480823544055599091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524543653882362703732727 12786815480823544055599091)
        ·
          refine ⟨19180223221235316083398637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786815480823544055599091 19180223221235316083398637)
          ·
            refine ⟨7192583707963243531274489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19180223221235316083398637 7192583707963243531274489)
            ·
              refine ⟨5394437780972432648455867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192583707963243531274489 5394437780972432648455867)
              ·
                refine ⟨8091656671458648972683801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394437780972432648455867 8091656671458648972683801)
                ·
                  refine ⟨6068742503593986729512851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091656671458648972683801 6068742503593986729512851)
                  ·
                    refine ⟨9103113755390980094269277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068742503593986729512851 9103113755390980094269277)
                    ·
                      refine ⟨3413667658271617535350979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103113755390980094269277 3413667658271617535350979)
                      ·
                        rfl

theorem cell23_6648094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6648094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648094 prefixEnd_6648094 := by exact prefixLift 6648094
  have htrace : WordTrace (prefixWord ++ tailWord_6648094) baseStart_6648094 baseEnd_6648094 := by
    simpa [prefixWord, tailWord_6648094, baseEnd_6648094] using wordTrace_append hprefix tailTrace_6648094
  have hstable : (prefixWord ++ tailWord_6648094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648094).length < 2 ^ (prefixWord ++ tailWord_6648094).sum := by decide
  have hdescent : baseEnd_6648094 < baseStart_6648094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648099 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3]
def baseStart_6648099 : Nat := 118140960795 + 6648099 * 2 ^ 59
def prefixEnd_6648099 : Nat := 4983230072969 + 3 ^ 40 * 6648099 * 2
def baseEnd_6648099 : Nat := 3413670225674890015788455

theorem tailTrace_6648099 : CollatzResearch.WordTrace tailWord_6648099 prefixEnd_6648099 3413670225674890015788455 := by
  unfold tailWord_6648099
  simp only [CollatzResearch.WordTrace]
  refine ⟨242476090742080202760107351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161650727161386801840071567 242476090742080202760107351)
  ·
    refine ⟨363714136113120304140161027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242476090742080202760107351 363714136113120304140161027)
    ·
      refine ⟨545571204169680456210241541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363714136113120304140161027 545571204169680456210241541)
      ·
        refine ⟨102294600781815085539420289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545571204169680456210241541 102294600781815085539420289)
        ·
          refine ⟨76720950586361314154565217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102294600781815085539420289 76720950586361314154565217)
          ·
            refine ⟨57540712939770985615923913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76720950586361314154565217 57540712939770985615923913)
            ·
              refine ⟨43155534704828239211942935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57540712939770985615923913 43155534704828239211942935)
              ·
                refine ⟨64733302057242358817914403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43155534704828239211942935 64733302057242358817914403)
                ·
                  refine ⟨97099953085863538226871605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64733302057242358817914403 97099953085863538226871605)
                  ·
                    refine ⟨9103120601799706708769213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97099953085863538226871605 9103120601799706708769213)
                    ·
                      refine ⟨3413670225674890015788455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103120601799706708769213 3413670225674890015788455)
                      ·
                        rfl

theorem cell23_6648099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_6648099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648099 prefixEnd_6648099 := by exact prefixLift 6648099
  have htrace : WordTrace (prefixWord ++ tailWord_6648099) baseStart_6648099 baseEnd_6648099 := by
    simpa [prefixWord, tailWord_6648099, baseEnd_6648099] using wordTrace_append hprefix tailTrace_6648099
  have hstable : (prefixWord ++ tailWord_6648099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648099).length < 2 ^ (prefixWord ++ tailWord_6648099).sum := by decide
  have hdescent : baseEnd_6648099 < baseStart_6648099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648100 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_6648100 : Nat := 118140960795 + 6648100 * 2 ^ 59
def prefixEnd_6648100 : Nat := 4983230072969 + 3 ^ 40 * 6648100 * 2
def baseEnd_6648100 : Nat := 3413670739155544511875951

theorem tailTrace_6648100 : CollatzResearch.WordTrace tailWord_6648100 prefixEnd_6648100 3413670739155544511875951 := by
  unfold tailWord_6648100
  simp only [CollatzResearch.WordTrace]
  refine ⟨121238063607538289965446877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161650751476717719953929169 121238063607538289965446877)
  ·
    refine ⟨45464273852826858737042579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121238063607538289965446877 45464273852826858737042579)
    ·
      refine ⟨68196410779240288105563869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45464273852826858737042579 68196410779240288105563869)
      ·
        refine ⟨25573654042215108039586451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68196410779240288105563869 25573654042215108039586451)
        ·
          refine ⟨38360481063322662059379677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25573654042215108039586451 38360481063322662059379677)
          ·
            refine ⟨14385180398745998272267379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38360481063322662059379677 14385180398745998272267379)
            ·
              refine ⟨21577770598118997408401069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14385180398745998272267379 21577770598118997408401069)
              ·
                refine ⟨8091663974294624028150401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21577770598118997408401069 8091663974294624028150401)
                ·
                  refine ⟨6068747980720968021112801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091663974294624028150401 6068747980720968021112801)
                  ·
                    refine ⟨4551560985540726015834601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068747980720968021112801 4551560985540726015834601)
                    ·
                      refine ⟨3413670739155544511875951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551560985540726015834601 3413670739155544511875951)
                      ·
                        rfl

theorem cell23_6648100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_6648100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648100 prefixEnd_6648100 := by exact prefixLift 6648100
  have htrace : WordTrace (prefixWord ++ tailWord_6648100) baseStart_6648100 baseEnd_6648100 := by
    simpa [prefixWord, tailWord_6648100, baseEnd_6648100] using wordTrace_append hprefix tailTrace_6648100
  have hstable : (prefixWord ++ tailWord_6648100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648100).length < 2 ^ (prefixWord ++ tailWord_6648100).sum := by decide
  have hdescent : baseEnd_6648100 < baseStart_6648100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648139 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4]
def baseStart_6648139 : Nat := 118140960795 + 6648139 * 2 ^ 59
def prefixEnd_6648139 : Nat := 4983230072969 + 3 ^ 40 * 6648139 * 2
def baseEnd_6648139 : Nat := 3413690764901069859288271

theorem tailTrace_6648139 : CollatzResearch.WordTrace tailWord_6648139 prefixEnd_6648139 3413690764901069859288271 := by
  unfold tailWord_6648139
  simp only [CollatzResearch.WordTrace]
  refine ⟨242477549661935289591563471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161651699774623526394375647 242477549661935289591563471)
  ·
    refine ⟨363716324492902934387345207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242477549661935289591563471 363716324492902934387345207)
    ·
      refine ⟨545574486739354401581017811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363716324492902934387345207 545574486739354401581017811)
      ·
        refine ⟨818361730109031602371526717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545574486739354401581017811 818361730109031602371526717)
        ·
          refine ⟨306885648790886850889322519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 818361730109031602371526717 306885648790886850889322519)
          ·
            refine ⟨460328473186330276333983779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306885648790886850889322519 460328473186330276333983779)
            ·
              refine ⟨690492709779495414500975669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460328473186330276333983779 690492709779495414500975669)
              ·
                refine ⟨64733691541827695109466469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690492709779495414500975669 64733691541827695109466469)
                ·
                  refine ⟨12137567164092692833024963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64733691541827695109466469 12137567164092692833024963)
                  ·
                    refine ⟨18206350746139039249537445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12137567164092692833024963 18206350746139039249537445)
                    ·
                      refine ⟨3413690764901069859288271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18206350746139039249537445 3413690764901069859288271)
                      ·
                        rfl

theorem cell23_6648139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_6648139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648139 prefixEnd_6648139 := by exact prefixLift 6648139
  have htrace : WordTrace (prefixWord ++ tailWord_6648139) baseStart_6648139 baseEnd_6648139 := by
    simpa [prefixWord, tailWord_6648139, baseEnd_6648139] using wordTrace_append hprefix tailTrace_6648139
  have hstable : (prefixWord ++ tailWord_6648139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648139).length < 2 ^ (prefixWord ++ tailWord_6648139).sum := by decide
  have hdescent : baseEnd_6648139 < baseStart_6648139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648176 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_6648176 : Nat := 118140960795 + 6648176 * 2 ^ 59
def prefixEnd_6648176 : Nat := 4983230072969 + 3 ^ 40 * 6648176 * 2
def baseEnd_6648176 : Nat := 3413709763685286214525601

theorem tailTrace_6648176 : CollatzResearch.WordTrace tailWord_6648176 prefixEnd_6648176 3413709763685286214525601 := by
  unfold tailWord_6648176
  simp only [CollatzResearch.WordTrace]
  refine ⟨121239449581400622455330191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161652599441867496607106921 121239449581400622455330191)
  ·
    refine ⟨181859174372100933682995287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121239449581400622455330191 181859174372100933682995287)
    ·
      refine ⟨272788761558151400524492931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181859174372100933682995287 272788761558151400524492931)
      ·
        refine ⟨409183142337227100786739397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272788761558151400524492931 409183142337227100786739397)
        ·
          refine ⟨76721839188230081397513637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409183142337227100786739397 76721839188230081397513637)
          ·
            refine ⟨14385344847793140262033807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76721839188230081397513637 14385344847793140262033807)
            ·
              refine ⟨21578017271689710393050711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14385344847793140262033807 21578017271689710393050711)
              ·
                refine ⟨32367025907534565589576067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21578017271689710393050711 32367025907534565589576067)
                ·
                  refine ⟨48550538861301848384364101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32367025907534565589576067 48550538861301848384364101)
                  ·
                    refine ⟨9103226036494096572068269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48550538861301848384364101 9103226036494096572068269)
                    ·
                      refine ⟨3413709763685286214525601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103226036494096572068269 3413709763685286214525601)
                      ·
                        rfl

theorem cell23_6648176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_6648176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648176 prefixEnd_6648176 := by exact prefixLift 6648176
  have htrace : WordTrace (prefixWord ++ tailWord_6648176) baseStart_6648176 baseEnd_6648176 := by
    simpa [prefixWord, tailWord_6648176, baseEnd_6648176] using wordTrace_append hprefix tailTrace_6648176
  have hstable : (prefixWord ++ tailWord_6648176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648176).length < 2 ^ (prefixWord ++ tailWord_6648176).sum := by decide
  have hdescent : baseEnd_6648176 < baseStart_6648176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648199 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_6648199 : Nat := 118140960795 + 6648199 * 2 ^ 59
def prefixEnd_6648199 : Nat := 4983230072969 + 3 ^ 40 * 6648199 * 2
def baseEnd_6648199 : Nat := 3413721573740339624537995

theorem tailTrace_6648199 : CollatzResearch.WordTrace tailWord_6648199 prefixEnd_6648199 3413721573740339624537995 := by
  unfold tailWord_6648199
  simp only [CollatzResearch.WordTrace]
  refine ⟨242479738041717919838747651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161653158694478613225831767 242479738041717919838747651)
  ·
    refine ⟨363719607062576879758121477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242479738041717919838747651 363719607062576879758121477)
    ·
      refine ⟨68197426324233164954647777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363719607062576879758121477 68197426324233164954647777)
      ·
        refine ⟨51148069743174873715985833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68197426324233164954647777 51148069743174873715985833)
        ·
          refine ⟨38361052307381155286989375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51148069743174873715985833 38361052307381155286989375)
          ·
            refine ⟨57541578461071732930484063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38361052307381155286989375 57541578461071732930484063)
            ·
              refine ⟨86312367691607599395726095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57541578461071732930484063 86312367691607599395726095)
              ·
                refine ⟨129468551537411399093589143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86312367691607599395726095 129468551537411399093589143)
                ·
                  refine ⟨194202827306117098640383715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129468551537411399093589143 194202827306117098640383715)
                  ·
                    refine ⟨291304240959175647960575573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194202827306117098640383715 291304240959175647960575573)
                    ·
                      refine ⟨3413721573740339624537995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291304240959175647960575573 3413721573740339624537995)
                      ·
                        rfl

theorem cell23_6648199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_6648199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648199 prefixEnd_6648199 := by exact prefixLift 6648199
  have htrace : WordTrace (prefixWord ++ tailWord_6648199) baseStart_6648199 baseEnd_6648199 := by
    simpa [prefixWord, tailWord_6648199, baseEnd_6648199] using wordTrace_append hprefix tailTrace_6648199
  have hstable : (prefixWord ++ tailWord_6648199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648199).length < 2 ^ (prefixWord ++ tailWord_6648199).sum := by decide
  have hdescent : baseEnd_6648199 < baseStart_6648199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648223 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6648223 : Nat := 118140960795 + 6648223 * 2 ^ 59
def prefixEnd_6648223 : Nat := 4983230072969 + 3 ^ 40 * 6648223 * 2
def baseEnd_6648223 : Nat := 3413733897276047530637885

theorem tailTrace_6648223 : CollatzResearch.WordTrace tailWord_6648223 prefixEnd_6648223 3413733897276047530637885 := by
  unfold tailWord_6648223
  simp only [CollatzResearch.WordTrace]
  refine ⟨242480613393630971937621323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161653742262420647958414215 242480613393630971937621323)
  ·
    refine ⟨363720920090446457906431985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242480613393630971937621323 363720920090446457906431985)
    ·
      refine ⟨272790690067834843429823989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363720920090446457906431985 272790690067834843429823989)
      ·
        refine ⟨25574127193859516571545999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272790690067834843429823989 25574127193859516571545999)
        ·
          refine ⟨38361190790789274857318999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25574127193859516571545999 38361190790789274857318999)
          ·
            refine ⟨57541786186183912285978499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38361190790789274857318999 57541786186183912285978499)
            ·
              refine ⟨86312679279275868428967749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57541786186183912285978499 86312679279275868428967749)
              ·
                refine ⟨16183627364864225330431453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86312679279275868428967749 16183627364864225330431453)
                ·
                  refine ⟨6068860261824084498911795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16183627364864225330431453 6068860261824084498911795)
                  ·
                    refine ⟨9103290392736126748367693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068860261824084498911795 9103290392736126748367693)
                    ·
                      refine ⟨3413733897276047530637885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103290392736126748367693 3413733897276047530637885)
                      ·
                        rfl

theorem cell23_6648223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6648223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648223 prefixEnd_6648223 := by exact prefixLift 6648223
  have htrace : WordTrace (prefixWord ++ tailWord_6648223) baseStart_6648223 baseEnd_6648223 := by
    simpa [prefixWord, tailWord_6648223, baseEnd_6648223] using wordTrace_append hprefix tailTrace_6648223
  have hstable : (prefixWord ++ tailWord_6648223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648223).length < 2 ^ (prefixWord ++ tailWord_6648223).sum := by decide
  have hdescent : baseEnd_6648223 < baseStart_6648223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648266 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_6648266 : Nat := 118140960795 + 6648266 * 2 ^ 59
def prefixEnd_6648266 : Nat := 4983230072969 + 3 ^ 40 * 6648266 * 2
def baseEnd_6648266 : Nat := 3413755976944190862400187

theorem tailTrace_6648266 : CollatzResearch.WordTrace tailWord_6648266 prefixEnd_6648266 3413755976944190862400187 := by
  unfold tailWord_6648266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60620545433118797570359163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161654787821650126854291101 60620545433118797570359163)
  ·
    refine ⟨90930818149678196355538745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60620545433118797570359163 90930818149678196355538745)
    ·
      refine ⟨68198113612258647266654059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90930818149678196355538745 68198113612258647266654059)
      ·
        refine ⟨102297170418387970899981089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68198113612258647266654059 102297170418387970899981089)
        ·
          refine ⟨76722877813790978174985817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102297170418387970899981089 76722877813790978174985817)
          ·
            refine ⟨57542158360343233631239363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76722877813790978174985817 57542158360343233631239363)
            ·
              refine ⟨86313237540514850446859045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57542158360343233631239363 86313237540514850446859045)
              ·
                refine ⟨16183732038846534458786071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86313237540514850446859045 16183732038846534458786071)
                ·
                  refine ⟨24275598058269801688179107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16183732038846534458786071 24275598058269801688179107)
                  ·
                    refine ⟨36413397087404702532268661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24275598058269801688179107 36413397087404702532268661)
                    ·
                      refine ⟨3413755976944190862400187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36413397087404702532268661 3413755976944190862400187)
                      ·
                        rfl

theorem cell23_6648266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_6648266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648266 prefixEnd_6648266 := by exact prefixLift 6648266
  have htrace : WordTrace (prefixWord ++ tailWord_6648266) baseStart_6648266 baseEnd_6648266 := by
    simpa [prefixWord, tailWord_6648266, baseEnd_6648266] using wordTrace_append hprefix tailTrace_6648266
  have hstable : (prefixWord ++ tailWord_6648266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648266).length < 2 ^ (prefixWord ++ tailWord_6648266).sum := by decide
  have hdescent : baseEnd_6648266 < baseStart_6648266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648300 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_6648300 : Nat := 118140960795 + 6648300 * 2 ^ 59
def prefixEnd_6648300 : Nat := 4983230072969 + 3 ^ 40 * 6648300 * 2
def baseEnd_6648300 : Nat := 3413773435286443729375031

theorem tailTrace_6648300 : CollatzResearch.WordTrace tailWord_6648300 prefixEnd_6648300 3413773435286443729375031 := by
  unfold tailWord_6648300
  simp only [CollatzResearch.WordTrace]
  refine ⟨121241710907176007044087177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161655614542901342725449569 121241710907176007044087177)
  ·
    refine ⟨90931283180382005283065383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121241710907176007044087177 90931283180382005283065383)
    ·
      refine ⟨136396924770573007924598075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90931283180382005283065383 136396924770573007924598075)
      ·
        refine ⟨204595387155859511886897113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136396924770573007924598075 204595387155859511886897113)
        ·
          refine ⟨153446540366894633915172835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204595387155859511886897113 153446540366894633915172835)
          ·
            refine ⟨230169810550341950872759253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153446540366894633915172835 230169810550341950872759253)
            ·
              refine ⟨5394604934773639473580295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230169810550341950872759253 5394604934773639473580295)
              ·
                refine ⟨8091907402160459210370443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394604934773639473580295 8091907402160459210370443)
                ·
                  refine ⟨12137861103240688815555665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091907402160459210370443 12137861103240688815555665)
                  ·
                    refine ⟨9103395827430516611666749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12137861103240688815555665 9103395827430516611666749)
                    ·
                      refine ⟨3413773435286443729375031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103395827430516611666749 3413773435286443729375031)
                      ·
                        rfl

theorem cell23_6648300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_6648300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648300 prefixEnd_6648300 := by exact prefixLift 6648300
  have htrace : WordTrace (prefixWord ++ tailWord_6648300) baseStart_6648300 baseEnd_6648300 := by
    simpa [prefixWord, tailWord_6648300, baseEnd_6648300] using wordTrace_append hprefix tailTrace_6648300
  have hstable : (prefixWord ++ tailWord_6648300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648300).length < 2 ^ (prefixWord ++ tailWord_6648300).sum := by decide
  have hdescent : baseEnd_6648300 < baseStart_6648300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648313 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_6648313 : Nat := 118140960795 + 6648313 * 2 ^ 59
def prefixEnd_6648313 : Nat := 4983230072969 + 3 ^ 40 * 6648313 * 2
def baseEnd_6648313 : Nat := 3413780110534952178512471

theorem tailTrace_6648313 : CollatzResearch.WordTrace tailWord_6648313 prefixEnd_6648313 3413780110534952178512471 := by
  unfold tailWord_6648313
  simp only [CollatzResearch.WordTrace]
  refine ⟨242483895963304917308397593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161655930642203278205598395 242483895963304917308397593)
  ·
    refine ⟨181862921972478687981298195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242483895963304917308397593 181862921972478687981298195)
    ·
      refine ⟨272794382958718031971947293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181862921972478687981298195 272794382958718031971947293)
      ·
        refine ⟨102297893609519261989480235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272794382958718031971947293 102297893609519261989480235)
        ·
          refine ⟨153446840414278892984220353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102297893609519261989480235 153446840414278892984220353)
          ·
            refine ⟨115085130310709169738165265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153446840414278892984220353 115085130310709169738165265)
            ·
              refine ⟨86313847733031877303623949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115085130310709169738165265 86313847733031877303623949)
              ·
                refine ⟨32367692899886953988858981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86313847733031877303623949 32367692899886953988858981)
                ·
                  refine ⟨6068942418728803872911059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32367692899886953988858981 6068942418728803872911059)
                  ·
                    refine ⟨9103413628093205809366589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068942418728803872911059 9103413628093205809366589)
                    ·
                      refine ⟨3413780110534952178512471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103413628093205809366589 3413780110534952178512471)
                      ·
                        rfl

theorem cell23_6648313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_6648313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648313 prefixEnd_6648313 := by exact prefixLift 6648313
  have htrace : WordTrace (prefixWord ++ tailWord_6648313) baseStart_6648313 baseEnd_6648313 := by
    simpa [prefixWord, tailWord_6648313, baseEnd_6648313] using wordTrace_append hprefix tailTrace_6648313
  have hstable : (prefixWord ++ tailWord_6648313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648313).length < 2 ^ (prefixWord ++ tailWord_6648313).sum := by decide
  have hdescent : baseEnd_6648313 < baseStart_6648313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648323 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 5, 3, 2]
def baseStart_6648323 : Nat := 118140960795 + 6648323 * 2 ^ 59
def prefixEnd_6648323 : Nat := 4983230072969 + 3 ^ 40 * 6648323 * 2
def baseEnd_6648323 : Nat := 3413785245341497139387425

theorem tailTrace_6648323 : CollatzResearch.WordTrace tailWord_6648323 prefixEnd_6648323 3413785245341497139387425 := by
  unfold tailWord_6648323
  simp only [CollatzResearch.WordTrace]
  refine ⟨242484260693268689016261623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161656173795512459344174415 242484260693268689016261623)
  ·
    refine ⟨363726391039903033524392435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242484260693268689016261623 363726391039903033524392435)
    ·
      refine ⟨545589586559854550286588653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363726391039903033524392435 545589586559854550286588653)
      ·
        refine ⟨204596094959945456357470745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545589586559854550286588653 204596094959945456357470745)
        ·
          refine ⟨153447071219959092268103059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204596094959945456357470745 153447071219959092268103059)
          ·
            refine ⟨230170606829938638402154589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153447071219959092268103059 230170606829938638402154589)
            ·
              refine ⟨86313977561226989400807971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230170606829938638402154589 86313977561226989400807971)
              ·
                refine ⟨129470966341840484101211957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86313977561226989400807971 129470966341840484101211957)
                ·
                  refine ⟨12137903094547545384488621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129470966341840484101211957 12137903094547545384488621)
                  ·
                    refine ⟨4551713660455329519183233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12137903094547545384488621 4551713660455329519183233)
                    ·
                      refine ⟨3413785245341497139387425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551713660455329519183233 3413785245341497139387425)
                      ·
                        rfl

theorem cell23_6648323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_6648323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648323 prefixEnd_6648323 := by exact prefixLift 6648323
  have htrace : WordTrace (prefixWord ++ tailWord_6648323) baseStart_6648323 baseEnd_6648323 := by
    simpa [prefixWord, tailWord_6648323, baseEnd_6648323] using wordTrace_append hprefix tailTrace_6648323
  have hstable : (prefixWord ++ tailWord_6648323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648323).length < 2 ^ (prefixWord ++ tailWord_6648323).sum := by decide
  have hdescent : baseEnd_6648323 < baseStart_6648323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648330 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_6648330 : Nat := 118140960795 + 6648330 * 2 ^ 59
def prefixEnd_6648330 : Nat := 4983230072969 + 3 ^ 40 * 6648330 * 2
def baseEnd_6648330 : Nat := 3413788839706078611999893

theorem tailTrace_6648330 : CollatzResearch.WordTrace tailWord_6648330 prefixEnd_6648330 3413788839706078611999893 := by
  unfold tailWord_6648330
  simp only [CollatzResearch.WordTrace]
  refine ⟨60621129001060832302941611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161656344002828886141177629 60621129001060832302941611)
  ·
    refine ⟨90931693501591248454412417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60621129001060832302941611 90931693501591248454412417)
    ·
      refine ⟨68198770126193436340809313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90931693501591248454412417 68198770126193436340809313)
      ·
        refine ⟨51149077594645077255606985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68198770126193436340809313 51149077594645077255606985)
        ·
          refine ⟨38361808195983807941705239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51149077594645077255606985 38361808195983807941705239)
          ·
            refine ⟨57542712293975711912557859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38361808195983807941705239 57542712293975711912557859)
            ·
              refine ⟨86314068440963567868836789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57542712293975711912557859 86314068440963567868836789)
              ·
                refine ⟨8091943916340334487703449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86314068440963567868836789 8091943916340334487703449)
                ·
                  refine ⟨6068957937255250865777587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091943916340334487703449 6068957937255250865777587)
                  ·
                    refine ⟨9103436905882876298666381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068957937255250865777587 9103436905882876298666381)
                    ·
                      refine ⟨3413788839706078611999893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103436905882876298666381 3413788839706078611999893)
                      ·
                        rfl

theorem cell23_6648330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_6648330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648330 prefixEnd_6648330 := by exact prefixLift 6648330
  have htrace : WordTrace (prefixWord ++ tailWord_6648330) baseStart_6648330 baseEnd_6648330 := by
    simpa [prefixWord, tailWord_6648330, baseEnd_6648330] using wordTrace_append hprefix tailTrace_6648330
  have hstable : (prefixWord ++ tailWord_6648330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648330).length < 2 ^ (prefixWord ++ tailWord_6648330).sum := by decide
  have hdescent : baseEnd_6648330 < baseStart_6648330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648357 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_6648357 : Nat := 118140960795 + 6648357 * 2 ^ 59
def prefixEnd_6648357 : Nat := 4983230072969 + 3 ^ 40 * 6648357 * 2
def baseEnd_6648357 : Nat := 3413802703683750006362269

theorem tailTrace_6648357 : CollatzResearch.WordTrace tailWord_6648357 prefixEnd_6648357 3413802703683750006362269 := by
  unfold tailWord_6648357
  simp only [CollatzResearch.WordTrace]
  refine ⟨242485500775145512822999325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161657000516763675215332883 242485500775145512822999325)
  ·
    refine ⟨90932062790679567308624747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242485500775145512822999325 90932062790679567308624747)
    ·
      refine ⟨136398094186019350962937121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90932062790679567308624747 136398094186019350962937121)
      ·
        refine ⟨102298570639514513222202841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136398094186019350962937121 102298570639514513222202841)
        ·
          refine ⟨76723927979635884916652131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102298570639514513222202841 76723927979635884916652131)
          ·
            refine ⟨115085891969453827374978197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76723927979635884916652131 115085891969453827374978197)
            ·
              refine ⟨5394651186068148158202103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115085891969453827374978197 5394651186068148158202103)
              ·
                refine ⟨8091976779102222237303155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394651186068148158202103 8091976779102222237303155)
                ·
                  refine ⟨12137965168653333355954733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091976779102222237303155 12137965168653333355954733)
                  ·
                    refine ⟨4551736938245000008483025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12137965168653333355954733 4551736938245000008483025)
                    ·
                      refine ⟨3413802703683750006362269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551736938245000008483025 3413802703683750006362269)
                      ·
                        rfl

theorem cell23_6648357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_6648357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648357 prefixEnd_6648357 := by exact prefixLift 6648357
  have htrace : WordTrace (prefixWord ++ tailWord_6648357) baseStart_6648357 baseEnd_6648357 := by
    simpa [prefixWord, tailWord_6648357, baseEnd_6648357] using wordTrace_append hprefix tailTrace_6648357
  have hstable : (prefixWord ++ tailWord_6648357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648357).length < 2 ^ (prefixWord ++ tailWord_6648357).sum := by decide
  have hdescent : baseEnd_6648357 < baseStart_6648357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648438 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6648438 : Nat := 118140960795 + 6648438 * 2 ^ 59
def prefixEnd_6648438 : Nat := 4983230072969 + 3 ^ 40 * 6648438 * 2
def baseEnd_6648438 : Nat := 3413844295616764189449397

theorem tailTrace_6648438 : CollatzResearch.WordTrace tailWord_6648438 prefixEnd_6648438 3413844295616764189449397 := by
  unfold tailWord_6648438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155528442990753978543623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161658970058568042437798645 15155528442990753978543623)
  ·
    refine ⟨22733292664486130967815435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15155528442990753978543623 22733292664486130967815435)
    ·
      refine ⟨34099938996729196451723153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22733292664486130967815435 34099938996729196451723153)
      ·
        refine ⟨25574954247546897338792365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34099938996729196451723153 25574954247546897338792365)
        ·
          refine ⟨9590607842830086502047137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25574954247546897338792365 9590607842830086502047137)
          ·
            refine ⟨7192955882122564876535353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9590607842830086502047137 7192955882122564876535353)
            ·
              refine ⟨5394716911591923657401515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192955882122564876535353 5394716911591923657401515)
              ·
                refine ⟨8092075367387885486102273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394716911591923657401515 8092075367387885486102273)
                ·
                  refine ⟨6069056525540914114576705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8092075367387885486102273 6069056525540914114576705)
                  ·
                    refine ⟨4551792394155685585932529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069056525540914114576705 4551792394155685585932529)
                    ·
                      refine ⟨3413844295616764189449397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551792394155685585932529 3413844295616764189449397)
                      ·
                        rfl

theorem cell23_6648438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6648438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648438 prefixEnd_6648438 := by exact prefixLift 6648438
  have htrace : WordTrace (prefixWord ++ tailWord_6648438) baseStart_6648438 baseEnd_6648438 := by
    simpa [prefixWord, tailWord_6648438, baseEnd_6648438] using wordTrace_append hprefix tailTrace_6648438
  have hstable : (prefixWord ++ tailWord_6648438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648438).length < 2 ^ (prefixWord ++ tailWord_6648438).sum := by decide
  have hdescent : baseEnd_6648438 < baseStart_6648438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_6648463 : Nat := 118140960795 + 6648463 * 2 ^ 59
def prefixEnd_6648463 : Nat := 4983230072969 + 3 ^ 40 * 6648463 * 2
def baseEnd_6648463 : Nat := 3413857132633126591636781

theorem tailTrace_6648463 : CollatzResearch.WordTrace tailWord_6648463 prefixEnd_6648463 3413857132633126591636781 := by
  unfold tailWord_6648463
  simp only [CollatzResearch.WordTrace]
  refine ⟨242489366912761492926358043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161659577941840995284238695 242489366912761492926358043)
  ·
    refine ⟨363734050369142239389537065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242489366912761492926358043 363734050369142239389537065)
    ·
      refine ⟨272800537776856679542152799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363734050369142239389537065 272800537776856679542152799)
      ·
        refine ⟨409200806665285019313229199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272800537776856679542152799 409200806665285019313229199)
        ·
          refine ⟨613801209997927528969843799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409200806665285019313229199 613801209997927528969843799)
          ·
            refine ⟨920701814996891293454765699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613801209997927528969843799 920701814996891293454765699)
            ·
              refine ⟨1381052722495336940182148549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920701814996891293454765699 1381052722495336940182148549)
              ·
                refine ⟨258947385467875676284152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1381052722495336940182148549 258947385467875676284152853)
                ·
                  refine ⟨12138158693806672325819665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258947385467875676284152853 12138158693806672325819665)
                  ·
                    refine ⟨9103619020355004244364749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12138158693806672325819665 9103619020355004244364749)
                    ·
                      refine ⟨3413857132633126591636781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103619020355004244364749 3413857132633126591636781)
                      ·
                        rfl

theorem cell23_6648463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_6648463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648463 prefixEnd_6648463 := by exact prefixLift 6648463
  have htrace : WordTrace (prefixWord ++ tailWord_6648463) baseStart_6648463 baseEnd_6648463 := by
    simpa [prefixWord, tailWord_6648463, baseEnd_6648463] using wordTrace_append hprefix tailTrace_6648463
  have hstable : (prefixWord ++ tailWord_6648463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648463).length < 2 ^ (prefixWord ++ tailWord_6648463).sum := by decide
  have hdescent : baseEnd_6648463 < baseStart_6648463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648494 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6648494 : Nat := 118140960795 + 6648494 * 2 ^ 59
def prefixEnd_6648494 : Nat := 4983230072969 + 3 ^ 40 * 6648494 * 2
def baseEnd_6648494 : Nat := 3413873050533415970349139

theorem tailTrace_6648494 : CollatzResearch.WordTrace tailWord_6648494 prefixEnd_6648494 3413873050533415970349139 := by
  unfold tailWord_6648494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30311312196956148152592067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161660331717099456813824357 30311312196956148152592067)
  ·
    refine ⟨45466968295434222228888101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30311312196956148152592067 45466968295434222228888101)
    ·
      refine ⟨8525056555393916667916519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45466968295434222228888101 8525056555393916667916519)
      ·
        refine ⟨12787584833090875001874779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8525056555393916667916519 12787584833090875001874779)
        ·
          refine ⟨19181377249636312502812169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12787584833090875001874779 19181377249636312502812169)
          ·
            refine ⟨14386032937227234377109127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19181377249636312502812169 14386032937227234377109127)
            ·
              refine ⟨21579049405840851565663691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386032937227234377109127 21579049405840851565663691)
              ·
                refine ⟨32368574108761277348495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21579049405840851565663691 32368574108761277348495537)
                ·
                  refine ⟨24276430581570958011371653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32368574108761277348495537 24276430581570958011371653)
                  ·
                    refine ⟨4551830734044554627132185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24276430581570958011371653 4551830734044554627132185)
                    ·
                      refine ⟨3413873050533415970349139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4551830734044554627132185 3413873050533415970349139)
                      ·
                        rfl

theorem cell23_6648494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6648494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648494 prefixEnd_6648494 := by exact prefixLift 6648494
  have htrace : WordTrace (prefixWord ++ tailWord_6648494) baseStart_6648494 baseEnd_6648494 := by
    simpa [prefixWord, tailWord_6648494, baseEnd_6648494] using wordTrace_append hprefix tailTrace_6648494
  have hstable : (prefixWord ++ tailWord_6648494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648494).length < 2 ^ (prefixWord ++ tailWord_6648494).sum := by decide
  have hdescent : baseEnd_6648494 < baseStart_6648494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648553 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_6648553 : Nat := 118140960795 + 6648553 * 2 ^ 59
def prefixEnd_6648553 : Nat := 4983230072969 + 3 ^ 40 * 6648553 * 2
def baseEnd_6648553 : Nat := 3413903345892031239511367

theorem tailTrace_6648553 : CollatzResearch.WordTrace tailWord_6648553 prefixEnd_6648553 3413903345892031239511367 := by
  unfold tailWord_6648553
  simp only [CollatzResearch.WordTrace]
  refine ⟨242492649482435438297134313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161661766321623625531422875 242492649482435438297134313)
  ·
    refine ⟨181869487111826578722850735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242492649482435438297134313 181869487111826578722850735)
    ·
      refine ⟨272804230667739868084276103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181869487111826578722850735 272804230667739868084276103)
      ·
        refine ⟨409206346001609802126414155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272804230667739868084276103 409206346001609802126414155)
        ·
          refine ⟨613809519002414703189621233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409206346001609802126414155 613809519002414703189621233)
          ·
            refine ⟨460357139251811027392215925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613809519002414703189621233 460357139251811027392215925)
            ·
              refine ⟨43158481804857283818020243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460357139251811027392215925 43158481804857283818020243)
              ·
                refine ⟨64737722707285925727030365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43158481804857283818020243 64737722707285925727030365)
                ·
                  refine ⟨24276646015232222147636387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64737722707285925727030365 24276646015232222147636387)
                  ·
                    refine ⟨36414969022848333221454581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24276646015232222147636387 36414969022848333221454581)
                    ·
                      refine ⟨3413903345892031239511367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36414969022848333221454581 3413903345892031239511367)
                      ·
                        rfl

theorem cell23_6648553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_6648553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648553 prefixEnd_6648553 := by exact prefixLift 6648553
  have htrace : WordTrace (prefixWord ++ tailWord_6648553) baseStart_6648553 baseEnd_6648553 := by
    simpa [prefixWord, tailWord_6648553, baseEnd_6648553] using wordTrace_append hprefix tailTrace_6648553
  have hstable : (prefixWord ++ tailWord_6648553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648553).length < 2 ^ (prefixWord ++ tailWord_6648553).sum := by decide
  have hdescent : baseEnd_6648553 < baseStart_6648553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648570 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_6648570 : Nat := 118140960795 + 6648570 * 2 ^ 59
def prefixEnd_6648570 : Nat := 4983230072969 + 3 ^ 40 * 6648570 * 2
def baseEnd_6648570 : Nat := 3413912075063157672998789

theorem tailTrace_6648570 : CollatzResearch.WordTrace tailWord_6648570 prefixEnd_6648570 3413912075063157672998789 := by
  unfold tailWord_6648570
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623317380843462550125791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161662179682249233467002109 60623317380843462550125791)
  ·
    refine ⟨90934976071265193825188687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623317380843462550125791 90934976071265193825188687)
    ·
      refine ⟨136402464106897790737783031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90934976071265193825188687 136402464106897790737783031)
      ·
        refine ⟨204603696160346686106674547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136402464106897790737783031 204603696160346686106674547)
        ·
          refine ⟨306905544240520029160011821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204603696160346686106674547 306905544240520029160011821)
          ·
            refine ⟨115089579090195010935004433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306905544240520029160011821 115089579090195010935004433)
            ·
              refine ⟨86317184317646258201253325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115089579090195010935004433 86317184317646258201253325)
              ·
                refine ⟨32368944119117346825469997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86317184317646258201253325 32368944119117346825469997)
                ·
                  refine ⟨12138354044669005059551249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32368944119117346825469997 12138354044669005059551249)
                  ·
                    refine ⟨9103765533501753794663437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12138354044669005059551249 9103765533501753794663437)
                    ·
                      refine ⟨3413912075063157672998789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103765533501753794663437 3413912075063157672998789)
                      ·
                        rfl

theorem cell23_6648570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_6648570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648570 prefixEnd_6648570 := by exact prefixLift 6648570
  have htrace : WordTrace (prefixWord ++ tailWord_6648570) baseStart_6648570 baseEnd_6648570 := by
    simpa [prefixWord, tailWord_6648570, baseEnd_6648570] using wordTrace_append hprefix tailTrace_6648570
  have hstable : (prefixWord ++ tailWord_6648570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648570).length < 2 ^ (prefixWord ++ tailWord_6648570).sum := by decide
  have hdescent : baseEnd_6648570 < baseStart_6648570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648573 : List Nat := [1, 4, 1, 1, 1, 1, 5, 9]
def baseStart_6648573 : Nat := 118140960795 + 6648573 * 2 ^ 59
def prefixEnd_6648573 : Nat := 4983230072969 + 3 ^ 40 * 6648573 * 2
def baseEnd_6648573 : Nat := 126441245018708191157825

theorem tailTrace_6648573 : CollatzResearch.WordTrace tailWord_6648573 prefixEnd_6648573 126441245018708191157825 := by
  unfold tailWord_6648573
  simp only [CollatzResearch.WordTrace]
  refine ⟨242493378942362981712862373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161662252628241987808574915 242493378942362981712862373)
  ·
    refine ⟨45467508551693059071161695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242493378942362981712862373 45467508551693059071161695)
    ·
      refine ⟨68201262827539588606742543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45467508551693059071161695 68201262827539588606742543)
      ·
        refine ⟨102301894241309382910113815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68201262827539588606742543 102301894241309382910113815)
        ·
          refine ⟨153452841361964074365170723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102301894241309382910113815 153452841361964074365170723)
          ·
            refine ⟨230179262042946111547756085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153452841361964074365170723 230179262042946111547756085)
            ·
              refine ⟨21579305816526197957602133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230179262042946111547756085 21579305816526197957602133)
              ·
                refine ⟨126441245018708191157825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21579305816526197957602133 126441245018708191157825)
                ·
                  rfl

theorem cell23_6648573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 9].length) (baseStart_6648573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648573 prefixEnd_6648573 := by exact prefixLift 6648573
  have htrace : WordTrace (prefixWord ++ tailWord_6648573) baseStart_6648573 baseEnd_6648573 := by
    simpa [prefixWord, tailWord_6648573, baseEnd_6648573] using wordTrace_append hprefix tailTrace_6648573
  have hstable : (prefixWord ++ tailWord_6648573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648573).length < 2 ^ (prefixWord ++ tailWord_6648573).sum := by decide
  have hdescent : baseEnd_6648573 < baseStart_6648573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648578 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_6648578 : Nat := 118140960795 + 6648578 * 2 ^ 59
def prefixEnd_6648578 : Nat := 4983230072969 + 3 ^ 40 * 6648578 * 2
def baseEnd_6648578 : Nat := 3413916182908393641698753

theorem tailTrace_6648578 : CollatzResearch.WordTrace tailWord_6648578 prefixEnd_6648578 3413916182908393641698753 := by
  unfold tailWord_6648578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623390326836216891698597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161662374204896578377862925 60623390326836216891698597)
  ·
    refine ⟨11366885686281790667193487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60623390326836216891698597 11366885686281790667193487)
    ·
      refine ⟨17050328529422686000790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11366885686281790667193487 17050328529422686000790231)
      ·
        refine ⟨25575492794134029001185347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17050328529422686000790231 25575492794134029001185347)
        ·
          refine ⟨38363239191201043501778021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25575492794134029001185347 38363239191201043501778021)
          ·
            refine ⟨7193107348350195656583379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38363239191201043501778021 7193107348350195656583379)
            ·
              refine ⟨10789661022525293484875069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193107348350195656583379 10789661022525293484875069)
              ·
                refine ⟨4046122883446985056828151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10789661022525293484875069 4046122883446985056828151)
                ·
                  refine ⟨6069184325170477585242227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046122883446985056828151 6069184325170477585242227)
                  ·
                    refine ⟨9103776487755716377863341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069184325170477585242227 9103776487755716377863341)
                    ·
                      refine ⟨3413916182908393641698753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103776487755716377863341 3413916182908393641698753)
                      ·
                        rfl

theorem cell23_6648578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_6648578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648578 prefixEnd_6648578 := by exact prefixLift 6648578
  have htrace : WordTrace (prefixWord ++ tailWord_6648578) baseStart_6648578 baseEnd_6648578 := by
    simpa [prefixWord, tailWord_6648578, baseEnd_6648578] using wordTrace_append hprefix tailTrace_6648578
  have hstable : (prefixWord ++ tailWord_6648578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648578).length < 2 ^ (prefixWord ++ tailWord_6648578).sum := by decide
  have hdescent : baseEnd_6648578 < baseStart_6648578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648580 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6648580 : Nat := 118140960795 + 6648580 * 2 ^ 59
def prefixEnd_6648580 : Nat := 4983230072969 + 3 ^ 40 * 6648580 * 2
def baseEnd_6648580 : Nat := 3413917209869702633873743

theorem tailTrace_6648580 : CollatzResearch.WordTrace tailWord_6648580 prefixEnd_6648580 3413917209869702633873743 := by
  unfold tailWord_6648580
  simp only [CollatzResearch.WordTrace]
  refine ⟨121246817126668810954183597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161662422835558414605578129 121246817126668810954183597)
  ·
    refine ⟨45467556422500804107818849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121246817126668810954183597 45467556422500804107818849)
    ·
      refine ⟨34100667316875603080864137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45467556422500804107818849 34100667316875603080864137)
      ·
        refine ⟨25575500487656702310648103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34100667316875603080864137 25575500487656702310648103)
        ·
          refine ⟨38363250731485053465972155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25575500487656702310648103 38363250731485053465972155)
          ·
            refine ⟨57544876097227580198958233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38363250731485053465972155 57544876097227580198958233)
            ·
              refine ⟨43158657072920685149218675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57544876097227580198958233 43158657072920685149218675)
              ·
                refine ⟨64737985609381027723828013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43158657072920685149218675 64737985609381027723828013)
                ·
                  refine ⟨24276744603517885396435505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64737985609381027723828013 24276744603517885396435505)
                  ·
                    refine ⟨18207558452638414047326629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24276744603517885396435505 18207558452638414047326629)
                    ·
                      refine ⟨3413917209869702633873743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18207558452638414047326629 3413917209869702633873743)
                      ·
                        rfl

theorem cell23_6648580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6648580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648580 prefixEnd_6648580 := by exact prefixLift 6648580
  have htrace : WordTrace (prefixWord ++ tailWord_6648580) baseStart_6648580 baseEnd_6648580 := by
    simpa [prefixWord, tailWord_6648580, baseEnd_6648580] using wordTrace_append hprefix tailTrace_6648580
  have hstable : (prefixWord ++ tailWord_6648580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648580).length < 2 ^ (prefixWord ++ tailWord_6648580).sum := by decide
  have hdescent : baseEnd_6648580 < baseStart_6648580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648617 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_6648617 : Nat := 118140960795 + 6648617 * 2 ^ 59
def prefixEnd_6648617 : Nat := 4983230072969 + 3 ^ 40 * 6648617 * 2
def baseEnd_6648617 : Nat := 3413936208653918989111073

theorem tailTrace_6648617 : CollatzResearch.WordTrace tailWord_6648617 prefixEnd_6648617 3413936208653918989111073 := by
  unfold tailWord_6648617
  simp only [CollatzResearch.WordTrace]
  refine ⟨242494983754203577227464105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161663322502802384818309403 242494983754203577227464105)
  ·
    refine ⟨181871237815652682920598079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242494983754203577227464105 181871237815652682920598079)
    ·
      refine ⟨272806856723479024380897119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181871237815652682920598079 272806856723479024380897119)
      ·
        refine ⟨409210285085218536571345679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272806856723479024380897119 409210285085218536571345679)
        ·
          refine ⟨613815427627827804857018519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409210285085218536571345679 613815427627827804857018519)
          ·
            refine ⟨920723141441741707285527779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613815427627827804857018519 920723141441741707285527779)
            ·
              refine ⟨1381084712162612560928291669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920723141441741707285527779 1381084712162612560928291669)
              ·
                refine ⟨8092293235327807974189209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1381084712162612560928291669 8092293235327807974189209)
                ·
                  refine ⟨6069219926495855980641907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8092293235327807974189209 6069219926495855980641907)
                  ·
                    refine ⟨9103829889743783970962861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069219926495855980641907 9103829889743783970962861)
                    ·
                      refine ⟨3413936208653918989111073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103829889743783970962861 3413936208653918989111073)
                      ·
                        rfl

theorem cell23_6648617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_6648617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648617 prefixEnd_6648617 := by exact prefixLift 6648617
  have htrace : WordTrace (prefixWord ++ tailWord_6648617) baseStart_6648617 baseEnd_6648617 := by
    simpa [prefixWord, tailWord_6648617, baseEnd_6648617] using wordTrace_append hprefix tailTrace_6648617
  have hstable : (prefixWord ++ tailWord_6648617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648617).length < 2 ^ (prefixWord ++ tailWord_6648617).sum := by decide
  have hdescent : baseEnd_6648617 < baseStart_6648617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648618 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6648618 : Nat := 118140960795 + 6648618 * 2 ^ 59
def prefixEnd_6648618 : Nat := 4983230072969 + 3 ^ 40 * 6648618 * 2
def baseEnd_6648618 : Nat := 3413936722134573485198569

theorem tailTrace_6648618 : CollatzResearch.WordTrace tailWord_6648618 prefixEnd_6648618 3413936722134573485198569 := by
  unfold tailWord_6648618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623755056799988599562627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161663346818133302932167005 60623755056799988599562627)
  ·
    refine ⟨90935632585199982899343941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623755056799988599562627 90935632585199982899343941)
    ·
      refine ⟨17050431109724996793626989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90935632585199982899343941 17050431109724996793626989)
      ·
        refine ⟨6393911666146873797610121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17050431109724996793626989 6393911666146873797610121)
        ·
          refine ⟨4795433749610155348207591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393911666146873797610121 4795433749610155348207591)
          ·
            refine ⟨7193150624415233022311387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795433749610155348207591 7193150624415233022311387)
            ·
              refine ⟨10789725936622849533467081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193150624415233022311387 10789725936622849533467081)
              ·
                refine ⟨8092294452467137150100311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10789725936622849533467081 8092294452467137150100311)
                ·
                  refine ⟨12138441678700705725150467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092294452467137150100311 12138441678700705725150467)
                  ·
                    refine ⟨18207662518051058587725701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12138441678700705725150467 18207662518051058587725701)
                    ·
                      refine ⟨3413936722134573485198569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18207662518051058587725701 3413936722134573485198569)
                      ·
                        rfl

theorem cell23_6648618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6648618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648618 prefixEnd_6648618 := by exact prefixLift 6648618
  have htrace : WordTrace (prefixWord ++ tailWord_6648618) baseStart_6648618 baseEnd_6648618 := by
    simpa [prefixWord, tailWord_6648618, baseEnd_6648618] using wordTrace_append hprefix tailTrace_6648618
  have hstable : (prefixWord ++ tailWord_6648618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648618).length < 2 ^ (prefixWord ++ tailWord_6648618).sum := by decide
  have hdescent : baseEnd_6648618 < baseStart_6648618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648621 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6648621 : Nat := 118140960795 + 6648621 * 2 ^ 59
def prefixEnd_6648621 : Nat := 4983230072969 + 3 ^ 40 * 6648621 * 2
def baseEnd_6648621 : Nat := 3413938262576536973461055

theorem tailTrace_6648621 : CollatzResearch.WordTrace tailWord_6648621 prefixEnd_6648621 3413938262576536973461055 := by
  unfold tailWord_6648621
  simp only [CollatzResearch.WordTrace]
  refine ⟨242495129646189085910609717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161663419764126057273739811 242495129646189085910609717)
  ·
    refine ⟨22733918404330226804119661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242495129646189085910609717 22733918404330226804119661)
    ·
      refine ⟨8525219401623835051544873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22733918404330226804119661 8525219401623835051544873)
      ·
        refine ⟨6393914551217876288658655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8525219401623835051544873 6393914551217876288658655)
        ·
          refine ⟨9590871826826814432987983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6393914551217876288658655 9590871826826814432987983)
          ·
            refine ⟨14386307740240221649481975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9590871826826814432987983 14386307740240221649481975)
            ·
              refine ⟨21579461610360332474222963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386307740240221649481975 21579461610360332474222963)
              ·
                refine ⟨32369192415540498711334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21579461610360332474222963 32369192415540498711334445)
                ·
                  refine ⟨12138447155827687016750417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32369192415540498711334445 12138447155827687016750417)
                  ·
                    refine ⟨9103835366870765262562813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12138447155827687016750417 9103835366870765262562813)
                    ·
                      refine ⟨3413938262576536973461055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9103835366870765262562813 3413938262576536973461055)
                      ·
                        rfl

theorem cell23_6648621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6648621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648621 prefixEnd_6648621 := by exact prefixLift 6648621
  have htrace : WordTrace (prefixWord ++ tailWord_6648621) baseStart_6648621 baseEnd_6648621 := by
    simpa [prefixWord, tailWord_6648621, baseEnd_6648621] using wordTrace_append hprefix tailTrace_6648621
  have hstable : (prefixWord ++ tailWord_6648621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648621).length < 2 ^ (prefixWord ++ tailWord_6648621).sum := by decide
  have hdescent : baseEnd_6648621 < baseStart_6648621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648680 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 9]
def baseStart_6648680 : Nat := 118140960795 + 6648680 * 2 ^ 59
def prefixEnd_6648680 : Nat := 4983230072969 + 3 ^ 40 * 6648680 * 2
def baseEnd_6648680 : Nat := 379329839770572471402587

theorem tailTrace_6648680 : CollatzResearch.WordTrace tailWord_6648680 prefixEnd_6648680 379329839770572471402587 := by
  unfold tailWord_6648680
  simp only [CollatzResearch.WordTrace]
  refine ⟨121248640776487669493503747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161664854368650225991338329 121248640776487669493503747)
  ·
    refine ⟨181872961164731504240255621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121248640776487669493503747 181872961164731504240255621)
    ·
      refine ⟨34101180218387157045047929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181872961164731504240255621 34101180218387157045047929)
      ·
        refine ⟨25575885163790367783785947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34101180218387157045047929 25575885163790367783785947)
        ·
          refine ⟨38363827745685551675678921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25575885163790367783785947 38363827745685551675678921)
          ·
            refine ⟨28772870809264163756759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38363827745685551675678921 28772870809264163756759191)
            ·
              refine ⟨43159306213896245635138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28772870809264163756759191 43159306213896245635138787)
              ·
                refine ⟨64738959320844368452708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43159306213896245635138787 64738959320844368452708181)
                ·
                  refine ⟨379329839770572471402587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64738959320844368452708181 379329839770572471402587)
                  ·
                    rfl

theorem cell23_6648680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_6648680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648680 prefixEnd_6648680 := by exact prefixLift 6648680
  have htrace : WordTrace (prefixWord ++ tailWord_6648680) baseStart_6648680 baseEnd_6648680 := by
    simpa [prefixWord, tailWord_6648680, baseEnd_6648680] using wordTrace_append hprefix tailTrace_6648680
  have hstable : (prefixWord ++ tailWord_6648680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648680).length < 2 ^ (prefixWord ++ tailWord_6648680).sum := by decide
  have hdescent : baseEnd_6648680 < baseStart_6648680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648697 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 5]
def baseStart_6648697 : Nat := 118140960795 + 6648697 * 2 ^ 59
def prefixEnd_6648697 : Nat := 4983230072969 + 3 ^ 40 * 6648697 * 2
def baseEnd_6648697 : Nat := 379330809678475408456745

theorem tailTrace_6648697 : CollatzResearch.WordTrace tailWord_6648697 prefixEnd_6648697 379330809678475408456745 := by
  unfold tailWord_6648697
  simp only [CollatzResearch.WordTrace]
  refine ⟨242497901593913750890376345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161665267729275833926917563 242497901593913750890376345)
  ·
    refine ⟨181873426195435313167782259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242497901593913750890376345 181873426195435313167782259)
    ·
      refine ⟨272810139293152969751673389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181873426195435313167782259 272810139293152969751673389)
      ·
        refine ⟨102303802234932363656877521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272810139293152969751673389 102303802234932363656877521)
        ·
          refine ⟨76727851676199272742658141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102303802234932363656877521 76727851676199272742658141)
          ·
            refine ⟨28772944378574727278496803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76727851676199272742658141 28772944378574727278496803)
            ·
              refine ⟨43159416567862090917745205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28772944378574727278496803 43159416567862090917745205)
              ·
                refine ⟨4046195303237071023538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43159416567862090917745205 4046195303237071023538613)
                ·
                  refine ⟨379330809678475408456745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4046195303237071023538613 379330809678475408456745)
                  ·
                    rfl

theorem cell23_6648697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 5].length) (baseStart_6648697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648697 prefixEnd_6648697 := by exact prefixLift 6648697
  have htrace : WordTrace (prefixWord ++ tailWord_6648697) baseStart_6648697 baseEnd_6648697 := by
    simpa [prefixWord, tailWord_6648697, baseEnd_6648697] using wordTrace_append hprefix tailTrace_6648697
  have hstable : (prefixWord ++ tailWord_6648697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648697).length < 2 ^ (prefixWord ++ tailWord_6648697).sum := by decide
  have hdescent : baseEnd_6648697 < baseStart_6648697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648714 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_6648714 : Nat := 118140960795 + 6648714 * 2 ^ 59
def prefixEnd_6648714 : Nat := 4983230072969 + 3 ^ 40 * 6648714 * 2
def baseEnd_6648714 : Nat := 379331779586378345510903

theorem tailTrace_6648714 : CollatzResearch.WordTrace tailWord_6648714 prefixEnd_6648714 379331779586378345510903 := by
  unfold tailWord_6648714
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624630408713040698436299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161665681089901441862496797 60624630408713040698436299)
  ·
    refine ⟨90936945613069561047654449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60624630408713040698436299 90936945613069561047654449)
    ·
      refine ⟨68202709209802170785740837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90936945613069561047654449 68202709209802170785740837)
      ·
        refine ⟨12788007976837907022326407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68202709209802170785740837 12788007976837907022326407)
        ·
          refine ⟨19182011965256860533489611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788007976837907022326407 19182011965256860533489611)
          ·
            refine ⟨28773017947885290800234417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19182011965256860533489611 28773017947885290800234417)
            ·
              refine ⟨21579763460913968100175813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28773017947885290800234417 21579763460913968100175813)
              ·
                refine ⟨4046205648921369018782965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21579763460913968100175813 4046205648921369018782965)
                ·
                  refine ⟨379331779586378345510903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4046205648921369018782965 379331779586378345510903)
                  ·
                    rfl

theorem cell23_6648714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_6648714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648714 prefixEnd_6648714 := by exact prefixLift 6648714
  have htrace : WordTrace (prefixWord ++ tailWord_6648714) baseStart_6648714 baseEnd_6648714 := by
    simpa [prefixWord, tailWord_6648714, baseEnd_6648714] using wordTrace_append hprefix tailTrace_6648714
  have hstable : (prefixWord ++ tailWord_6648714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648714).length < 2 ^ (prefixWord ++ tailWord_6648714).sum := by decide
  have hdescent : baseEnd_6648714 < baseStart_6648714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648740 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_6648740 : Nat := 118140960795 + 6648740 * 2 ^ 59
def prefixEnd_6648740 : Nat := 4983230072969 + 3 ^ 40 * 6648740 * 2
def baseEnd_6648740 : Nat := 1137999788924807335957669

theorem tailTrace_6648740 : CollatzResearch.WordTrace tailWord_6648740 prefixEnd_6648740 1137999788924807335957669 := by
  unfold tailWord_6648740
  simp only [CollatzResearch.WordTrace]
  refine ⟨121249734966378984617095837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161666313288505312822794449 121249734966378984617095837)
  ·
    refine ⟨45468650612392119231410939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121249734966378984617095837 45468650612392119231410939)
    ·
      refine ⟨68202975918588178847116409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45468650612392119231410939 68202975918588178847116409)
      ·
        refine ⟨51152231938941134135337307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68202975918588178847116409 51152231938941134135337307)
        ·
          refine ⟨76728347908411701203005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51152231938941134135337307 76728347908411701203005961)
          ·
            refine ⟨57546260931308775902254471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76728347908411701203005961 57546260931308775902254471)
            ·
              refine ⟨86319391396963163853381707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57546260931308775902254471 86319391396963163853381707)
              ·
                refine ⟨129479087095444745780072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86319391396963163853381707 129479087095444745780072561)
                ·
                  refine ⟨97109315321583559335054421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129479087095444745780072561 97109315321583559335054421)
                  ·
                    refine ⟨1137999788924807335957669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97109315321583559335054421 1137999788924807335957669)
                    ·
                      rfl

theorem cell23_6648740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_6648740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648740 prefixEnd_6648740 := by exact prefixLift 6648740
  have htrace : WordTrace (prefixWord ++ tailWord_6648740) baseStart_6648740 baseEnd_6648740 := by
    simpa [prefixWord, tailWord_6648740, baseEnd_6648740] using wordTrace_append hprefix tailTrace_6648740
  have hstable : (prefixWord ++ tailWord_6648740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648740).length < 2 ^ (prefixWord ++ tailWord_6648740).sum := by decide
  have hdescent : baseEnd_6648740 < baseStart_6648740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648837 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_6648837 : Nat := 118140960795 + 6648837 * 2 ^ 59
def prefixEnd_6648837 : Nat := 4983230072969 + 3 ^ 40 * 6648837 * 2
def baseEnd_6648837 : Nat := 3414049174397908128360061

theorem tailTrace_6648837 : CollatzResearch.WordTrace tailWord_6648837 prefixEnd_6648837 3414049174397908128360061 := by
  unfold tailWord_6648837
  simp only [CollatzResearch.WordTrace]
  refine ⟨242503007813406554800472765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161668671875604369866981843 242503007813406554800472765)
  ·
    refine ⟨90938627930027458050177287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242503007813406554800472765 90938627930027458050177287)
    ·
      refine ⟨136407941895041187075265931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90938627930027458050177287 136407941895041187075265931)
      ·
        refine ⟨204611912842561780612898897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136407941895041187075265931 204611912842561780612898897)
        ·
          refine ⟨153458934631921335459674173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204611912842561780612898897 153458934631921335459674173)
          ·
            refine ⟨57547100486970500797377815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153458934631921335459674173 57547100486970500797377815)
            ·
              refine ⟨86320650730455751196066723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57547100486970500797377815 86320650730455751196066723)
              ·
                refine ⟨129480976095683626794100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86320650730455751196066723 129480976095683626794100085)
                ·
                  refine ⟨12138841508970340011946883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129480976095683626794100085 12138841508970340011946883)
                  ·
                    refine ⟨18208262263455510017920325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12138841508970340011946883 18208262263455510017920325)
                    ·
                      refine ⟨3414049174397908128360061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18208262263455510017920325 3414049174397908128360061)
                      ·
                        rfl

theorem cell23_6648837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_6648837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648837 prefixEnd_6648837 := by exact prefixLift 6648837
  have htrace : WordTrace (prefixWord ++ tailWord_6648837) baseStart_6648837 baseEnd_6648837 := by
    simpa [prefixWord, tailWord_6648837, baseEnd_6648837] using wordTrace_append hprefix tailTrace_6648837
  have hstable : (prefixWord ++ tailWord_6648837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648837).length < 2 ^ (prefixWord ++ tailWord_6648837).sum := by decide
  have hdescent : baseEnd_6648837 < baseStart_6648837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648868 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_6648868 : Nat := 118140960795 + 6648868 * 2 ^ 59
def prefixEnd_6648868 : Nat := 4983230072969 + 3 ^ 40 * 6648868 * 2
def baseEnd_6648868 : Nat := 1138021697432732502357473

theorem tailTrace_6648868 : CollatzResearch.WordTrace tailWord_6648868 prefixEnd_6648868 1138021697432732502357473 := by
  unfold tailWord_6648868
  simp only [CollatzResearch.WordTrace]
  refine ⟨121252069238147123547425629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161669425650862831396567505 121252069238147123547425629)
  ·
    refine ⟨45469525964305171330284611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121252069238147123547425629 45469525964305171330284611)
    ·
      refine ⟨68204288946457756995426917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45469525964305171330284611 68204288946457756995426917)
      ·
        refine ⟨12788304177460829436642547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68204288946457756995426917 12788304177460829436642547)
        ·
          refine ⟨19182456266191244154963821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788304177460829436642547 19182456266191244154963821)
          ·
            refine ⟨7193421099821716558111433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19182456266191244154963821 7193421099821716558111433)
            ·
              refine ⟨5395065824866287418583575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193421099821716558111433 5395065824866287418583575)
              ·
                refine ⟨8092598737299431127875363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395065824866287418583575 8092598737299431127875363)
                ·
                  refine ⟨12138898105949146691813045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092598737299431127875363 12138898105949146691813045)
                  ·
                    refine ⟨1138021697432732502357473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12138898105949146691813045 1138021697432732502357473)
                    ·
                      rfl

theorem cell23_6648868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_6648868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648868 prefixEnd_6648868 := by exact prefixLift 6648868
  have htrace : WordTrace (prefixWord ++ tailWord_6648868) baseStart_6648868 baseEnd_6648868 := by
    simpa [prefixWord, tailWord_6648868, baseEnd_6648868] using wordTrace_append hprefix tailTrace_6648868
  have hstable : (prefixWord ++ tailWord_6648868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648868).length < 2 ^ (prefixWord ++ tailWord_6648868).sum := by decide
  have hdescent : baseEnd_6648868 < baseStart_6648868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648888 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_6648888 : Nat := 118140960795 + 6648888 * 2 ^ 59
def prefixEnd_6648888 : Nat := 4983230072969 + 3 ^ 40 * 6648888 * 2
def baseEnd_6648888 : Nat := 3414075361911287428822327

theorem tailTrace_6648888 : CollatzResearch.WordTrace tailWord_6648888 prefixEnd_6648888 3414075361911287428822327 := by
  unfold tailWord_6648888
  simp only [CollatzResearch.WordTrace]
  refine ⟨121252433968110895255289659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161669911957481193673719545 121252433968110895255289659)
  ·
    refine ⟨181878650952166342882934489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121252433968110895255289659 181878650952166342882934489)
    ·
      refine ⟨136408988214124757162200867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181878650952166342882934489 136408988214124757162200867)
      ·
        refine ⟨204613482321187135743301301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136408988214124757162200867 204613482321187135743301301)
        ·
          refine ⟨19182513967611293975934497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204613482321187135743301301 19182513967611293975934497)
          ·
            refine ⟨14386885475708470481950873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19182513967611293975934497 14386885475708470481950873)
            ·
              refine ⟨10790164106781352861463155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14386885475708470481950873 10790164106781352861463155)
              ·
                refine ⟨16185246160172029292194733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790164106781352861463155 16185246160172029292194733)
                ·
                  refine ⟨6069467310064510984573025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16185246160172029292194733 6069467310064510984573025)
                  ·
                    refine ⟨4552100482548383238429769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069467310064510984573025 4552100482548383238429769)
                    ·
                      refine ⟨3414075361911287428822327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552100482548383238429769 3414075361911287428822327)
                      ·
                        rfl

theorem cell23_6648888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_6648888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648888 prefixEnd_6648888 := by exact prefixLift 6648888
  have htrace : WordTrace (prefixWord ++ tailWord_6648888) baseStart_6648888 baseEnd_6648888 := by
    simpa [prefixWord, tailWord_6648888, baseEnd_6648888] using wordTrace_append hprefix tailTrace_6648888
  have hstable : (prefixWord ++ tailWord_6648888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648888).length < 2 ^ (prefixWord ++ tailWord_6648888).sum := by decide
  have hdescent : baseEnd_6648888 < baseStart_6648888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648917 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6648917 : Nat := 118140960795 + 6648917 * 2 ^ 59
def prefixEnd_6648917 : Nat := 4983230072969 + 3 ^ 40 * 6648917 * 2
def baseEnd_6648917 : Nat := 3414090252850267815359693

theorem tailTrace_6648917 : CollatzResearch.WordTrace tailWord_6648917 prefixEnd_6648917 3414090252850267815359693 := by
  unfold tailWord_6648917
  simp only [CollatzResearch.WordTrace]
  refine ⟨242505925653116728463385005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161670617102077818975590003 242505925653116728463385005)
  ·
    refine ⟨90939722119918773173769377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242505925653116728463385005 90939722119918773173769377)
    ·
      refine ⟨68204791589939079880327033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90939722119918773173769377 68204791589939079880327033)
      ·
        refine ⟨51153593692454309910245275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68204791589939079880327033 51153593692454309910245275)
        ·
          refine ⟨76730390538681464865367913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51153593692454309910245275 76730390538681464865367913)
          ·
            refine ⟨57547792904011098649025935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76730390538681464865367913 57547792904011098649025935)
            ·
              refine ⟨86321689356016647973538903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57547792904011098649025935 86321689356016647973538903)
              ·
                refine ⟨129482534034024971960308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86321689356016647973538903 129482534034024971960308355)
                ·
                  refine ⟨194223801051037457940462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129482534034024971960308355 194223801051037457940462533)
                  ·
                    refine ⟨36416962697069523363836725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194223801051037457940462533 36416962697069523363836725)
                    ·
                      refine ⟨3414090252850267815359693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36416962697069523363836725 3414090252850267815359693)
                      ·
                        rfl

theorem cell23_6648917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6648917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648917 prefixEnd_6648917 := by exact prefixLift 6648917
  have htrace : WordTrace (prefixWord ++ tailWord_6648917) baseStart_6648917 baseEnd_6648917 := by
    simpa [prefixWord, tailWord_6648917, baseEnd_6648917] using wordTrace_append hprefix tailTrace_6648917
  have hstable : (prefixWord ++ tailWord_6648917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648917).length < 2 ^ (prefixWord ++ tailWord_6648917).sum := by decide
  have hdescent : baseEnd_6648917 < baseStart_6648917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648964 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6648964 : Nat := 118140960795 + 6648964 * 2 ^ 59
def prefixEnd_6648964 : Nat := 4983230072969 + 3 ^ 40 * 6648964 * 2
def baseEnd_6648964 : Nat := 3414114386441029131471977

theorem tailTrace_6648964 : CollatzResearch.WordTrace tailWord_6648964 prefixEnd_6648964 3414114386441029131471977 := by
  unfold tailWord_6648964
  simp only [CollatzResearch.WordTrace]
  refine ⟨121253819941973227745172973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161671759922630970326897297 121253819941973227745172973)
  ·
    refine ⟨45470182478239960404439865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121253819941973227745172973 45470182478239960404439865)
    ·
      refine ⟨34102636858679970303329899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45470182478239960404439865 34102636858679970303329899)
      ·
        refine ⟨51153955288019955454994849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34102636858679970303329899 51153955288019955454994849)
        ·
          refine ⟨38365466466014966591246137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51153955288019955454994849 38365466466014966591246137)
          ·
            refine ⟨28774099849511224943434603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38365466466014966591246137 28774099849511224943434603)
            ·
              refine ⟨43161149774266837415151905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28774099849511224943434603 43161149774266837415151905)
              ·
                refine ⟨32370862330700128061363929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43161149774266837415151905 32370862330700128061363929)
                ·
                  refine ⟨24278146748025096046022947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32370862330700128061363929 24278146748025096046022947)
                  ·
                    refine ⟨36417220122037644069034421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24278146748025096046022947 36417220122037644069034421)
                    ·
                      refine ⟨3414114386441029131471977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36417220122037644069034421 3414114386441029131471977)
                      ·
                        rfl

theorem cell23_6648964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6648964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648964 prefixEnd_6648964 := by exact prefixLift 6648964
  have htrace : WordTrace (prefixWord ++ tailWord_6648964) baseStart_6648964 baseEnd_6648964 := by
    simpa [prefixWord, tailWord_6648964, baseEnd_6648964] using wordTrace_append hprefix tailTrace_6648964
  have hstable : (prefixWord ++ tailWord_6648964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648964).length < 2 ^ (prefixWord ++ tailWord_6648964).sum := by decide
  have hdescent : baseEnd_6648964 < baseStart_6648964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648965 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_6648965 : Nat := 118140960795 + 6648965 * 2 ^ 59
def prefixEnd_6648965 : Nat := 4983230072969 + 3 ^ 40 * 6648965 * 2
def baseEnd_6648965 : Nat := 3414114899921683627559473

theorem tailTrace_6648965 : CollatzResearch.WordTrace tailWord_6648965 prefixEnd_6648965 3414114899921683627559473 := by
  unfold tailWord_6648965
  simp only [CollatzResearch.WordTrace]
  refine ⟨242507676356942832661132349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161671784237961888440754899 242507676356942832661132349)
  ·
    refine ⟨90940378633853562247924631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242507676356942832661132349 90940378633853562247924631)
    ·
      refine ⟨136410567950780343371886947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90940378633853562247924631 136410567950780343371886947)
      ·
        refine ⟨204615851926170515057830421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136410567950780343371886947 204615851926170515057830421)
        ·
          refine ⟨9591368059039242893335801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204615851926170515057830421 9591368059039242893335801)
          ·
            refine ⟨7193526044279432170001851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9591368059039242893335801 7193526044279432170001851)
            ·
              refine ⟨10790289066419148255002777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193526044279432170001851 10790289066419148255002777)
              ·
                refine ⟨8092716799814361191252083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790289066419148255002777 8092716799814361191252083)
                ·
                  refine ⟨12139075199721541786878125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092716799814361191252083 12139075199721541786878125)
                  ·
                    refine ⟨4552153199895578170079297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12139075199721541786878125 4552153199895578170079297)
                    ·
                      refine ⟨3414114899921683627559473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552153199895578170079297 3414114899921683627559473)
                      ·
                        rfl

theorem cell23_6648965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_6648965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648965 prefixEnd_6648965 := by exact prefixLift 6648965
  have htrace : WordTrace (prefixWord ++ tailWord_6648965) baseStart_6648965 baseEnd_6648965 := by
    simpa [prefixWord, tailWord_6648965, baseEnd_6648965] using wordTrace_append hprefix tailTrace_6648965
  have hstable : (prefixWord ++ tailWord_6648965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648965).length < 2 ^ (prefixWord ++ tailWord_6648965).sum := by decide
  have hdescent : baseEnd_6648965 < baseStart_6648965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648967 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 9]
def baseStart_6648967 : Nat := 118140960795 + 6648967 * 2 ^ 59
def prefixEnd_6648967 : Nat := 4983230072969 + 3 ^ 40 * 6648967 * 2
def baseEnd_6648967 : Nat := 379346214098110291081607

theorem tailTrace_6648967 : CollatzResearch.WordTrace tailWord_6648967 prefixEnd_6648967 379346214098110291081607 := by
  unfold tailWord_6648967
  simp only [CollatzResearch.WordTrace]
  refine ⟨242507749302935587002705155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161671832868623724668470103 242507749302935587002705155)
  ·
    refine ⟨363761623954403380504057733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242507749302935587002705155 363761623954403380504057733)
    ·
      refine ⟨68205304491450633844510825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363761623954403380504057733 68205304491450633844510825)
      ·
        refine ⟨51153978368587975383383119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68205304491450633844510825 51153978368587975383383119)
        ·
          refine ⟨76730967552881963075074679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51153978368587975383383119 76730967552881963075074679)
          ·
            refine ⟨115096451329322944612612019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76730967552881963075074679 115096451329322944612612019)
            ·
              refine ⟨172644676993984416918918029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115096451329322944612612019 172644676993984416918918029)
              ·
                refine ⟨64741753872744156344594261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172644676993984416918918029 64741753872744156344594261)
                ·
                  refine ⟨379346214098110291081607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64741753872744156344594261 379346214098110291081607)
                  ·
                    rfl

theorem cell23_6648967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 9].length) (baseStart_6648967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648967 prefixEnd_6648967 := by exact prefixLift 6648967
  have htrace : WordTrace (prefixWord ++ tailWord_6648967) baseStart_6648967 baseEnd_6648967 := by
    simpa [prefixWord, tailWord_6648967, baseEnd_6648967] using wordTrace_append hprefix tailTrace_6648967
  have hstable : (prefixWord ++ tailWord_6648967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648967).length < 2 ^ (prefixWord ++ tailWord_6648967).sum := by decide
  have hdescent : baseEnd_6648967 < baseStart_6648967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6648978 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6648978 : Nat := 118140960795 + 6648978 * 2 ^ 59
def prefixEnd_6648978 : Nat := 4983230072969 + 3 ^ 40 * 6648978 * 2
def baseEnd_6648978 : Nat := 3414121575170192076696913

theorem tailTrace_6648978 : CollatzResearch.WordTrace tailWord_6648978 prefixEnd_6648978 3414121575170192076696913 := by
  unfold tailWord_6648978
  simp only [CollatzResearch.WordTrace]
  refine ⟨60627037626473933970338897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161672100337263823920903725 60627037626473933970338897)
  ·
    refine ⟨45470278219855450477754173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60627037626473933970338897 45470278219855450477754173)
    ·
      refine ⟨17051354332445793929157815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45470278219855450477754173 17051354332445793929157815)
      ·
        refine ⟨25577031498668690893736723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17051354332445793929157815 25577031498668690893736723)
        ·
          refine ⟨38365547248003036340605085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25577031498668690893736723 38365547248003036340605085)
          ·
            refine ⟨14387080218001138627726907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38365547248003036340605085 14387080218001138627726907)
            ·
              refine ⟨21580620327001707941590361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387080218001138627726907 21580620327001707941590361)
              ·
                refine ⟨16185465245251280956192771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21580620327001707941590361 16185465245251280956192771)
                ·
                  refine ⟨24278197867876921434289157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16185465245251280956192771 24278197867876921434289157)
                  ·
                    refine ⟨4552162100226922768929217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24278197867876921434289157 4552162100226922768929217)
                    ·
                      refine ⟨3414121575170192076696913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552162100226922768929217 3414121575170192076696913)
                      ·
                        rfl

theorem cell23_6648978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6648978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6648978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6648978 prefixEnd_6648978 := by exact prefixLift 6648978
  have htrace : WordTrace (prefixWord ++ tailWord_6648978) baseStart_6648978 baseEnd_6648978 := by
    simpa [prefixWord, tailWord_6648978, baseEnd_6648978] using wordTrace_append hprefix tailTrace_6648978
  have hstable : (prefixWord ++ tailWord_6648978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6648978).length < 2 ^ (prefixWord ++ tailWord_6648978).sum := by decide
  have hdescent : baseEnd_6648978 < baseStart_6648978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6648978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649027 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 10]
def baseStart_6649027 : Nat := 118140960795 + 6649027 * 2 ^ 59
def prefixEnd_6649027 : Nat := 4983230072969 + 3 ^ 40 * 6649027 * 2
def baseEnd_6649027 : Nat := 1138048911907420794994729

theorem tailTrace_6649027 : CollatzResearch.WordTrace tailWord_6649027 prefixEnd_6649027 1138048911907420794994729 := by
  unfold tailWord_6649027
  simp only [CollatzResearch.WordTrace]
  refine ⟨242509937682718217249889335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161673291788478811499926223 242509937682718217249889335)
  ·
    refine ⟨363764906524077325874834003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242509937682718217249889335 363764906524077325874834003)
    ·
      refine ⟨545647359786115988812251005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363764906524077325874834003 545647359786115988812251005)
      ·
        refine ⟨204617759919793495804594127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545647359786115988812251005 204617759919793495804594127)
        ·
          refine ⟨306926639879690243706891191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204617759919793495804594127 306926639879690243706891191)
          ·
            refine ⟨460389959819535365560336787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306926639879690243706891191 460389959819535365560336787)
            ·
              refine ⟨690584939729303048340505181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460389959819535365560336787 690584939729303048340505181)
              ·
                refine ⟨258969352398488643127689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 690584939729303048340505181 258969352398488643127689443)
                ·
                  refine ⟨388454028597732964691534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258969352398488643127689443 388454028597732964691534165)
                  ·
                    refine ⟨1138048911907420794994729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 388454028597732964691534165 1138048911907420794994729)
                    ·
                      rfl

theorem cell23_6649027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_6649027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649027 prefixEnd_6649027 := by exact prefixLift 6649027
  have htrace : WordTrace (prefixWord ++ tailWord_6649027) baseStart_6649027 baseEnd_6649027 := by
    simpa [prefixWord, tailWord_6649027, baseEnd_6649027] using wordTrace_append hprefix tailTrace_6649027
  have hstable : (prefixWord ++ tailWord_6649027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649027).length < 2 ^ (prefixWord ++ tailWord_6649027).sum := by decide
  have hdescent : baseEnd_6649027 < baseStart_6649027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649046 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6649046 : Nat := 118140960795 + 6649046 * 2 ^ 59
def prefixEnd_6649046 : Nat := 4983230072969 + 3 ^ 40 * 6649046 * 2
def baseEnd_6649046 : Nat := 3414156491854697810646601

theorem tailTrace_6649046 : CollatzResearch.WordTrace tailWord_6649046 prefixEnd_6649046 3414156491854697810646601 := by
  unfold tailWord_6649046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156914416853086468426937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161673753779766255663220661 15156914416853086468426937)
  ·
    refine ⟨11367685812639814851320203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15156914416853086468426937 11367685812639814851320203)
    ·
      refine ⟨17051528718959722276980305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367685812639814851320203 17051528718959722276980305)
      ·
        refine ⟨12788646539219791707735229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17051528718959722276980305 12788646539219791707735229)
        ·
          refine ⟨4795742452207421890400711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12788646539219791707735229 4795742452207421890400711)
          ·
            refine ⟨7193613678311132835601067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795742452207421890400711 7193613678311132835601067)
            ·
              refine ⟨10790420517466699253401601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193613678311132835601067 10790420517466699253401601)
              ·
                refine ⟨8092815388100024440051201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790420517466699253401601 8092815388100024440051201)
                ·
                  refine ⟨6069611541075018330038401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8092815388100024440051201 6069611541075018330038401)
                  ·
                    refine ⟨4552208655806263747528801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069611541075018330038401 4552208655806263747528801)
                    ·
                      refine ⟨3414156491854697810646601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552208655806263747528801 3414156491854697810646601)
                      ·
                        rfl

theorem cell23_6649046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6649046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649046 prefixEnd_6649046 := by exact prefixLift 6649046
  have htrace : WordTrace (prefixWord ++ tailWord_6649046) baseStart_6649046 baseEnd_6649046 := by
    simpa [prefixWord, tailWord_6649046, baseEnd_6649046] using wordTrace_append hprefix tailTrace_6649046
  have hstable : (prefixWord ++ tailWord_6649046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649046).length < 2 ^ (prefixWord ++ tailWord_6649046).sum := by decide
  have hdescent : baseEnd_6649046 < baseStart_6649046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649064 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6649064 : Nat := 118140960795 + 6649064 * 2 ^ 59
def prefixEnd_6649064 : Nat := 4983230072969 + 3 ^ 40 * 6649064 * 2
def baseEnd_6649064 : Nat := 3414165734506478740221517

theorem tailTrace_6649064 : CollatzResearch.WordTrace tailWord_6649064 prefixEnd_6649064 3414165734506478740221517 := by
  unfold tailWord_6649064
  simp only [CollatzResearch.WordTrace]
  refine ⟨121255643591792086284493123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161674191455722781712657497 121255643591792086284493123)
  ·
    refine ⟨181883465387688129426739685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121255643591792086284493123 181883465387688129426739685)
    ·
      refine ⟨34103149760191524267513691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181883465387688129426739685 34103149760191524267513691)
      ·
        refine ⟨51154724640287286401270537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34103149760191524267513691 51154724640287286401270537)
        ·
          refine ⟨38366043480215464800952903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51154724640287286401270537 38366043480215464800952903)
          ·
            refine ⟨57549065220323197201429355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38366043480215464800952903 57549065220323197201429355)
            ·
              refine ⟨86323597830484795802144033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57549065220323197201429355 86323597830484795802144033)
              ·
                refine ⟨64742698372863596851608025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86323597830484795802144033 64742698372863596851608025)
                ·
                  refine ⟨48557023779647697638706019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64742698372863596851608025 48557023779647697638706019)
                  ·
                    refine ⟨72835535669471546458059029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48557023779647697638706019 72835535669471546458059029)
                    ·
                      refine ⟨3414165734506478740221517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72835535669471546458059029 3414165734506478740221517)
                      ·
                        rfl

theorem cell23_6649064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6649064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649064 prefixEnd_6649064 := by exact prefixLift 6649064
  have htrace : WordTrace (prefixWord ++ tailWord_6649064) baseStart_6649064 baseEnd_6649064 := by
    simpa [prefixWord, tailWord_6649064, baseEnd_6649064] using wordTrace_append hprefix tailTrace_6649064
  have hstable : (prefixWord ++ tailWord_6649064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649064).length < 2 ^ (prefixWord ++ tailWord_6649064).sum := by decide
  have hdescent : baseEnd_6649064 < baseStart_6649064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649138 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_6649138 : Nat := 118140960795 + 6649138 * 2 ^ 59
def prefixEnd_6649138 : Nat := 4983230072969 + 3 ^ 40 * 6649138 * 2
def baseEnd_6649138 : Nat := 1138067910691637150232059

theorem tailTrace_6649138 : CollatzResearch.WordTrace tailWord_6649138 prefixEnd_6649138 1138067910691637150232059 := by
  unfold tailWord_6649138
  simp only [CollatzResearch.WordTrace]
  refine ⟨60628496546329020801795017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161675990790210722138120045 60628496546329020801795017)
  ·
    refine ⟨45471372409746765601346263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60628496546329020801795017 45471372409746765601346263)
    ·
      refine ⟨68207058614620148402019395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45471372409746765601346263 68207058614620148402019395)
      ·
        refine ⟨102310587921930222603029093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68207058614620148402019395 102310587921930222603029093)
        ·
          refine ⟨19183235235361916738067955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102310587921930222603029093 19183235235361916738067955)
          ·
            refine ⟨28774852853042875107101933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19183235235361916738067955 28774852853042875107101933)
            ·
              refine ⟨10790569819891078165163225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28774852853042875107101933 10790569819891078165163225)
              ·
                refine ⟨8092927364918308623872419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790569819891078165163225 8092927364918308623872419)
                ·
                  refine ⟨12139391047377462935808629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092927364918308623872419 12139391047377462935808629)
                  ·
                    refine ⟨1138067910691637150232059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12139391047377462935808629 1138067910691637150232059)
                    ·
                      rfl

theorem cell23_6649138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_6649138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649138 prefixEnd_6649138 := by exact prefixLift 6649138
  have htrace : WordTrace (prefixWord ++ tailWord_6649138) baseStart_6649138 baseEnd_6649138 := by
    simpa [prefixWord, tailWord_6649138, baseEnd_6649138] using wordTrace_append hprefix tailTrace_6649138
  have hstable : (prefixWord ++ tailWord_6649138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649138).length < 2 ^ (prefixWord ++ tailWord_6649138).sum := by decide
  have hdescent : baseEnd_6649138 < baseStart_6649138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649151 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 6]
def baseStart_6649151 : Nat := 118140960795 + 6649151 * 2 ^ 59
def prefixEnd_6649151 : Nat := 4983230072969 + 3 ^ 40 * 6649151 * 2
def baseEnd_6649151 : Nat := 1138070135774473299944539

theorem tailTrace_6649151 : CollatzResearch.WordTrace tailWord_6649151 prefixEnd_6649151 1138070135774473299944539 := by
  unfold tailWord_6649151
  simp only [CollatzResearch.WordTrace]
  refine ⟨242514460334268986427403307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161676306889512657618268871 242514460334268986427403307)
  ·
    refine ⟨363771690501403479641104961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242514460334268986427403307 363771690501403479641104961)
    ·
      refine ⟨272828767876052609730828721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363771690501403479641104961 272828767876052609730828721)
      ·
        refine ⟨204621575907039457298121541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272828767876052609730828721 204621575907039457298121541)
        ·
          refine ⟨38366545482569898243397789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204621575907039457298121541 38366545482569898243397789)
          ·
            refine ⟨14387454555963711841274171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38366545482569898243397789 14387454555963711841274171)
            ·
              refine ⟨21581181833945567761911257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387454555963711841274171 21581181833945567761911257)
              ·
                refine ⟨16185886375459175821433443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21581181833945567761911257 16185886375459175821433443)
                ·
                  refine ⟨24278829563188763732150165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16185886375459175821433443 24278829563188763732150165)
                  ·
                    refine ⟨1138070135774473299944539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24278829563188763732150165 1138070135774473299944539)
                    ·
                      rfl

theorem cell23_6649151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_6649151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649151 prefixEnd_6649151 := by exact prefixLift 6649151
  have htrace : WordTrace (prefixWord ++ tailWord_6649151) baseStart_6649151 baseEnd_6649151 := by
    simpa [prefixWord, tailWord_6649151, baseEnd_6649151] using wordTrace_append hprefix tailTrace_6649151
  have hstable : (prefixWord ++ tailWord_6649151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649151).length < 2 ^ (prefixWord ++ tailWord_6649151).sum := by decide
  have hdescent : baseEnd_6649151 < baseStart_6649151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649161 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_6649161 : Nat := 118140960795 + 6649161 * 2 ^ 59
def prefixEnd_6649161 : Nat := 4983230072969 + 3 ^ 40 * 6649161 * 2
def baseEnd_6649161 : Nat := 3414215542129964860708571

theorem tailTrace_6649161 : CollatzResearch.WordTrace tailWord_6649161 prefixEnd_6649161 3414215542129964860708571 := by
  unfold tailWord_6649161
  simp only [CollatzResearch.WordTrace]
  refine ⟨242514825064232758135267337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161676550042821838756844891 242514825064232758135267337)
  ·
    refine ⟨181886118798174568601450503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242514825064232758135267337 181886118798174568601450503)
    ·
      refine ⟨272829178197261852902175755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181886118798174568601450503 272829178197261852902175755)
      ·
        refine ⟨409243767295892779353263633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272829178197261852902175755 409243767295892779353263633)
        ·
          refine ⟨306932825471919584514947725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409243767295892779353263633 306932825471919584514947725)
          ·
            refine ⟨115099809551969844193105397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306932825471919584514947725 115099809551969844193105397)
            ·
              refine ⟨10790607145497172893103631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115099809551969844193105397 10790607145497172893103631)
              ·
                refine ⟨16185910718245759339655447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790607145497172893103631 16185910718245759339655447)
                ·
                  refine ⟨24278866077368639009483171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16185910718245759339655447 24278866077368639009483171)
                  ·
                    refine ⟨36418299116052958514224757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24278866077368639009483171 36418299116052958514224757)
                    ·
                      refine ⟨3414215542129964860708571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36418299116052958514224757 3414215542129964860708571)
                      ·
                        rfl

theorem cell23_6649161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_6649161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649161 prefixEnd_6649161 := by exact prefixLift 6649161
  have htrace : WordTrace (prefixWord ++ tailWord_6649161) baseStart_6649161 baseEnd_6649161 := by
    simpa [prefixWord, tailWord_6649161, baseEnd_6649161] using wordTrace_append hprefix tailTrace_6649161
  have hstable : (prefixWord ++ tailWord_6649161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649161).length < 2 ^ (prefixWord ++ tailWord_6649161).sum := by decide
  have hdescent : baseEnd_6649161 < baseStart_6649161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649164 : List Nat := [2, 2, 1, 3, 2, 13]
def baseStart_6649164 : Nat := 118140960795 + 6649164 * 2 ^ 59
def prefixEnd_6649164 : Nat := 4983230072969 + 3 ^ 40 * 6649164 * 2
def baseEnd_6649164 : Nat := 14050276059966783329099

theorem tailTrace_6649164 : CollatzResearch.WordTrace tailWord_6649164 prefixEnd_6649164 14050276059966783329099 := by
  unfold tailWord_6649164
  simp only [CollatzResearch.WordTrace]
  refine ⟨121257467241610944823813273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161676622988814593098417697 121257467241610944823813273)
  ·
    refine ⟨90943100431208208617859955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121257467241610944823813273 90943100431208208617859955)
    ·
      refine ⟨136414650646812312926789933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90943100431208208617859955 136414650646812312926789933)
      ·
        refine ⟨51155493992554617347546225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136414650646812312926789933 51155493992554617347546225)
        ·
          refine ⟨38366620494415963010659669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51155493992554617347546225 38366620494415963010659669)
          ·
            refine ⟨14050276059966783329099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38366620494415963010659669 14050276059966783329099)
            ·
              rfl

theorem cell23_6649164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 13].length) (baseStart_6649164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649164 prefixEnd_6649164 := by exact prefixLift 6649164
  have htrace : WordTrace (prefixWord ++ tailWord_6649164) baseStart_6649164 baseEnd_6649164 := by
    simpa [prefixWord, tailWord_6649164, baseEnd_6649164] using wordTrace_append hprefix tailTrace_6649164
  have hstable : (prefixWord ++ tailWord_6649164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649164).length < 2 ^ (prefixWord ++ tailWord_6649164).sum := by decide
  have hdescent : baseEnd_6649164 < baseStart_6649164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649168 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_6649168 : Nat := 118140960795 + 6649168 * 2 ^ 59
def prefixEnd_6649168 : Nat := 4983230072969 + 3 ^ 40 * 6649168 * 2
def baseEnd_6649168 : Nat := 1138073045498182111107013

theorem tailTrace_6649168 : CollatzResearch.WordTrace tailWord_6649168 prefixEnd_6649168 1138073045498182111107013 := by
  unfold tailWord_6649168
  simp only [CollatzResearch.WordTrace]
  refine ⟨121257540187603699165386079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161676720250138265553848105 121257540187603699165386079)
  ·
    refine ⟨181886310281405548748079119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121257540187603699165386079 181886310281405548748079119)
    ·
      refine ⟨272829465422108323122118679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181886310281405548748079119 272829465422108323122118679)
      ·
        refine ⟨409244198133162484683178019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272829465422108323122118679 409244198133162484683178019)
        ·
          refine ⟨613866297199743727024767029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409244198133162484683178019 613866297199743727024767029)
          ·
            refine ⟨57549965362475974408571909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613866297199743727024767029 57549965362475974408571909)
            ·
              refine ⟨10790618505464245201607233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57549965362475974408571909 10790618505464245201607233)
              ·
                refine ⟨8092963879098183901205425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790618505464245201607233 8092963879098183901205425)
                ·
                  refine ⟨6069722909323637925904069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8092963879098183901205425 6069722909323637925904069)
                  ·
                    refine ⟨1138073045498182111107013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069722909323637925904069 1138073045498182111107013)
                    ·
                      rfl

theorem cell23_6649168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_6649168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649168 prefixEnd_6649168 := by exact prefixLift 6649168
  have htrace : WordTrace (prefixWord ++ tailWord_6649168) baseStart_6649168 baseEnd_6649168 := by
    simpa [prefixWord, tailWord_6649168, baseEnd_6649168] using wordTrace_append hprefix tailTrace_6649168
  have hstable : (prefixWord ++ tailWord_6649168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649168).length < 2 ^ (prefixWord ++ tailWord_6649168).sum := by decide
  have hdescent : baseEnd_6649168 < baseStart_6649168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649188 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_6649188 : Nat := 118140960795 + 6649188 * 2 ^ 59
def prefixEnd_6649188 : Nat := 4983230072969 + 3 ^ 40 * 6649188 * 2
def baseEnd_6649188 : Nat := 3414229406107636255070947

theorem tailTrace_6649188 : CollatzResearch.WordTrace tailWord_6649188 prefixEnd_6649188 3414229406107636255070947 := by
  unfold tailWord_6649188
  simp only [CollatzResearch.WordTrace]
  refine ⟨121257904917567470873250109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161677206556756627831000145 121257904917567470873250109)
  ·
    refine ⟨45471714344087801577468791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121257904917567470873250109 45471714344087801577468791)
    ·
      refine ⟨68207571516131702366203187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45471714344087801577468791 68207571516131702366203187)
      ·
        refine ⟨102311357274197553549304781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68207571516131702366203187 102311357274197553549304781)
        ·
          refine ⟨38366758977824082580989293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102311357274197553549304781 38366758977824082580989293)
          ·
            refine ⟨14387534616684030967870985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38366758977824082580989293 14387534616684030967870985)
            ·
              refine ⟨10790650962513023225903239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14387534616684030967870985 10790650962513023225903239)
              ·
                refine ⟨16185976443769534838854859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790650962513023225903239 16185976443769534838854859)
                ·
                  refine ⟨24278964665654302258282289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16185976443769534838854859 24278964665654302258282289)
                  ·
                    refine ⟨18209223499240726693711717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24278964665654302258282289 18209223499240726693711717)
                    ·
                      refine ⟨3414229406107636255070947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18209223499240726693711717 3414229406107636255070947)
                      ·
                        rfl

theorem cell23_6649188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_6649188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649188 prefixEnd_6649188 := by exact prefixLift 6649188
  have htrace : WordTrace (prefixWord ++ tailWord_6649188) baseStart_6649188 baseEnd_6649188 := by
    simpa [prefixWord, tailWord_6649188, baseEnd_6649188] using wordTrace_append hprefix tailTrace_6649188
  have hstable : (prefixWord ++ tailWord_6649188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649188).length < 2 ^ (prefixWord ++ tailWord_6649188).sum := by decide
  have hdescent : baseEnd_6649188 < baseStart_6649188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649192 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6649192 : Nat := 118140960795 + 6649192 * 2 ^ 59
def prefixEnd_6649192 : Nat := 4983230072969 + 3 ^ 40 * 6649192 * 2
def baseEnd_6649192 : Nat := 3414231460030254239420929

theorem tailTrace_6649192 : CollatzResearch.WordTrace tailWord_6649192 prefixEnd_6649192 3414231460030254239420929 := by
  unfold tailWord_6649192
  simp only [CollatzResearch.WordTrace]
  refine ⟨121257977863560225214822915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161677303818080300286430553 121257977863560225214822915)
  ·
    refine ⟨181886966795340337822234373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121257977863560225214822915 181886966795340337822234373)
    ·
      refine ⟨34103806274126313341668945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181886966795340337822234373 34103806274126313341668945)
      ·
        refine ⟨25577854705594735006251709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34103806274126313341668945 25577854705594735006251709)
        ·
          refine ⟨9591695514598025627344391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25577854705594735006251709 9591695514598025627344391)
          ·
            refine ⟨14387543271897038441016587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591695514598025627344391 14387543271897038441016587)
            ·
              refine ⟨21581314907845557661524881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387543271897038441016587 21581314907845557661524881)
              ·
                refine ⟨16185986180884168246143661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21581314907845557661524881 16185986180884168246143661)
                ·
                  refine ⟨6069744817831563092303873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16185986180884168246143661 6069744817831563092303873)
                  ·
                    refine ⟨4552308613373672319227905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069744817831563092303873 4552308613373672319227905)
                    ·
                      refine ⟨3414231460030254239420929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552308613373672319227905 3414231460030254239420929)
                      ·
                        rfl

theorem cell23_6649192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6649192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649192 prefixEnd_6649192 := by exact prefixLift 6649192
  have htrace : WordTrace (prefixWord ++ tailWord_6649192) baseStart_6649192 baseEnd_6649192 := by
    simpa [prefixWord, tailWord_6649192, baseEnd_6649192] using wordTrace_append hprefix tailTrace_6649192
  have hstable : (prefixWord ++ tailWord_6649192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649192).length < 2 ^ (prefixWord ++ tailWord_6649192).sum := by decide
  have hdescent : baseEnd_6649192 < baseStart_6649192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649225 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_6649225 : Nat := 118140960795 + 6649225 * 2 ^ 59
def prefixEnd_6649225 : Nat := 4983230072969 + 3 ^ 40 * 6649225 * 2
def baseEnd_6649225 : Nat := 3414248404891852610308277

theorem tailTrace_6649225 : CollatzResearch.WordTrace tailWord_6649225 prefixEnd_6649225 3414248404891852610308277 := by
  unfold tailWord_6649225
  simp only [CollatzResearch.WordTrace]
  refine ⟨242517159336000897065597129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161678106224000598043731419 242517159336000897065597129)
  ·
    refine ⟨181887869502000672799197847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242517159336000897065597129 181887869502000672799197847)
    ·
      refine ⟨272831804253001009198796771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181887869502000672799197847 272831804253001009198796771)
      ·
        refine ⟨409247706379501513798195157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272831804253001009198796771 409247706379501513798195157)
        ·
          refine ⟨9591743118269566729645199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 409247706379501513798195157 9591743118269566729645199)
          ·
            refine ⟨14387614677404350094467799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591743118269566729645199 14387614677404350094467799)
            ·
              refine ⟨21581422016106525141701699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387614677404350094467799 21581422016106525141701699)
              ·
                refine ⟨32372133024159787712552549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21581422016106525141701699 32372133024159787712552549)
                ·
                  refine ⟨6069774942029960196103603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32372133024159787712552549 6069774942029960196103603)
                  ·
                    refine ⟨9104662413044940294155405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069774942029960196103603 9104662413044940294155405)
                    ·
                      refine ⟨3414248404891852610308277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9104662413044940294155405 3414248404891852610308277)
                      ·
                        rfl

theorem cell23_6649225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_6649225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649225 prefixEnd_6649225 := by exact prefixLift 6649225
  have htrace : WordTrace (prefixWord ++ tailWord_6649225) baseStart_6649225 baseEnd_6649225 := by
    simpa [prefixWord, tailWord_6649225, baseEnd_6649225] using wordTrace_append hprefix tailTrace_6649225
  have hstable : (prefixWord ++ tailWord_6649225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649225).length < 2 ^ (prefixWord ++ tailWord_6649225).sum := by decide
  have hdescent : baseEnd_6649225 < baseStart_6649225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649241 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_6649241 : Nat := 118140960795 + 6649241 * 2 ^ 59
def prefixEnd_6649241 : Nat := 4983230072969 + 3 ^ 40 * 6649241 * 2
def baseEnd_6649241 : Nat := 1138085540194108182569401

theorem tailTrace_6649241 : CollatzResearch.WordTrace tailWord_6649241 prefixEnd_6649241 1138085540194108182569401 := by
  unfold tailWord_6649241
  simp only [CollatzResearch.WordTrace]
  refine ⟨242517742903942931798179577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161678495269295287865453051 242517742903942931798179577)
  ·
    refine ⟨181888307177957198848634683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242517742903942931798179577 181888307177957198848634683)
    ·
      refine ⟨272832460766935798272952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181888307177957198848634683 272832460766935798272952025)
      ·
        refine ⟨204624345575201848704714019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272832460766935798272952025 204624345575201848704714019)
        ·
          refine ⟨306936518362802773057071029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204624345575201848704714019 306936518362802773057071029)
          ·
            refine ⟨28775298596512759974100409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306936518362802773057071029 28775298596512759974100409)
            ·
              refine ⟨21581473947384569980575307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28775298596512759974100409 21581473947384569980575307)
              ·
                refine ⟨32372210921076854970862961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21581473947384569980575307 32372210921076854970862961)
                ·
                  refine ⟨24279158190807641228147221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32372210921076854970862961 24279158190807641228147221)
                  ·
                    refine ⟨1138085540194108182569401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24279158190807641228147221 1138085540194108182569401)
                    ·
                      rfl

theorem cell23_6649241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_6649241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649241 prefixEnd_6649241 := by exact prefixLift 6649241
  have htrace : WordTrace (prefixWord ++ tailWord_6649241) baseStart_6649241 baseEnd_6649241 := by
    simpa [prefixWord, tailWord_6649241, baseEnd_6649241] using wordTrace_append hprefix tailTrace_6649241
  have hstable : (prefixWord ++ tailWord_6649241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649241).length < 2 ^ (prefixWord ++ tailWord_6649241).sum := by decide
  have hdescent : baseEnd_6649241 < baseStart_6649241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649242 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6649242 : Nat := 118140960795 + 6649242 * 2 ^ 59
def prefixEnd_6649242 : Nat := 4983230072969 + 3 ^ 40 * 6649242 * 2
def baseEnd_6649242 : Nat := 3414257134062979043795699

theorem tailTrace_6649242 : CollatzResearch.WordTrace tailWord_6649242 prefixEnd_6649242 3414257134062979043795699 := by
  unfold tailWord_6649242
  simp only [CollatzResearch.WordTrace]
  refine ⟨60629444844234827242241495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161678519584626205979310653 60629444844234827242241495)
  ·
    refine ⟨90944167266352240863362243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60629444844234827242241495 90944167266352240863362243)
    ·
      refine ⟨136416250899528361295043365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90944167266352240863362243 136416250899528361295043365)
      ·
        refine ⟨25578047043661567742820631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136416250899528361295043365 25578047043661567742820631)
        ·
          refine ⟨38367070565492351614230947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25578047043661567742820631 38367070565492351614230947)
          ·
            refine ⟨57550605848238527421346421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38367070565492351614230947 57550605848238527421346421)
            ·
              refine ⟨5395369298272361945751227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57550605848238527421346421 5395369298272361945751227)
              ·
                refine ⟨8093053947408542918626841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395369298272361945751227 8093053947408542918626841)
                ·
                  refine ⟨6069790460556407188970131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8093053947408542918626841 6069790460556407188970131)
                  ·
                    refine ⟨9104685690834610783455197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069790460556407188970131 9104685690834610783455197)
                    ·
                      refine ⟨3414257134062979043795699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9104685690834610783455197 3414257134062979043795699)
                      ·
                        rfl

theorem cell23_6649242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6649242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649242 prefixEnd_6649242 := by exact prefixLift 6649242
  have htrace : WordTrace (prefixWord ++ tailWord_6649242) baseStart_6649242 baseEnd_6649242 := by
    simpa [prefixWord, tailWord_6649242, baseEnd_6649242] using wordTrace_append hprefix tailTrace_6649242
  have hstable : (prefixWord ++ tailWord_6649242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649242).length < 2 ^ (prefixWord ++ tailWord_6649242).sum := by decide
  have hdescent : baseEnd_6649242 < baseStart_6649242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649251 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_6649251 : Nat := 118140960795 + 6649251 * 2 ^ 59
def prefixEnd_6649251 : Nat := 4983230072969 + 3 ^ 40 * 6649251 * 2
def baseEnd_6649251 : Nat := 3414261755388869508583157

theorem tailTrace_6649251 : CollatzResearch.WordTrace tailWord_6649251 prefixEnd_6649251 3414261755388869508583157 := by
  unfold tailWord_6649251
  simp only [CollatzResearch.WordTrace]
  refine ⟨242518107633906703506043607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161678738422604469004029071 242518107633906703506043607)
  ·
    refine ⟨363777161450860055259065411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242518107633906703506043607 363777161450860055259065411)
    ·
      refine ⟨545665742176290082888598117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363777161450860055259065411 545665742176290082888598117)
      ·
        refine ⟨102312326658054390541612147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545665742176290082888598117 102312326658054390541612147)
        ·
          refine ⟨153468489987081585812418221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102312326658054390541612147 153468489987081585812418221)
          ·
            refine ⟨57550683745155594679656833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153468489987081585812418221 57550683745155594679656833)
            ·
              refine ⟨43163012808866696009742625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57550683745155594679656833 43163012808866696009742625)
              ·
                refine ⟨32372259606650022007306969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43163012808866696009742625 32372259606650022007306969)
                ·
                  refine ⟨24279194704987516505480227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32372259606650022007306969 24279194704987516505480227)
                  ·
                    refine ⟨36418792057481274758220341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24279194704987516505480227 36418792057481274758220341)
                    ·
                      refine ⟨3414261755388869508583157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36418792057481274758220341 3414261755388869508583157)
                      ·
                        rfl

theorem cell23_6649251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_6649251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649251 prefixEnd_6649251 := by exact prefixLift 6649251
  have htrace : WordTrace (prefixWord ++ tailWord_6649251) baseStart_6649251 baseEnd_6649251 := by
    simpa [prefixWord, tailWord_6649251, baseEnd_6649251] using wordTrace_append hprefix tailTrace_6649251
  have hstable : (prefixWord ++ tailWord_6649251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649251).length < 2 ^ (prefixWord ++ tailWord_6649251).sum := by decide
  have hdescent : baseEnd_6649251 < baseStart_6649251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649265 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6649265 : Nat := 118140960795 + 6649265 * 2 ^ 59
def prefixEnd_6649265 : Nat := 4983230072969 + 3 ^ 40 * 6649265 * 2
def baseEnd_6649265 : Nat := 3414268944118032453808093

theorem tailTrace_6649265 : CollatzResearch.WordTrace tailWord_6649265 prefixEnd_6649265 3414268944118032453808093 := by
  unfold tailWord_6649265
  simp only [CollatzResearch.WordTrace]
  refine ⟨242518618255855983897053249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161679078837237322598035499 242518618255855983897053249)
  ·
    refine ⟨181888963691891987922789937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242518618255855983897053249 181888963691891987922789937)
    ·
      refine ⟨136416722768918990942092453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181888963691891987922789937 136416722768918990942092453)
      ·
        refine ⟨25578135519172310801642335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136416722768918990942092453 25578135519172310801642335)
        ·
          refine ⟨38367203278758466202463503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25578135519172310801642335 38367203278758466202463503)
          ·
            refine ⟨57550804918137699303695255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38367203278758466202463503 57550804918137699303695255)
            ·
              refine ⟨86326207377206548955542883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57550804918137699303695255 86326207377206548955542883)
              ·
                refine ⟨129489311065809823433314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86326207377206548955542883 129489311065809823433314325)
                ·
                  refine ⟨6069811456209835473436609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129489311065809823433314325 6069811456209835473436609)
                  ·
                    refine ⟨4552358592157376605077457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069811456209835473436609 4552358592157376605077457)
                    ·
                      refine ⟨3414268944118032453808093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552358592157376605077457 3414268944118032453808093)
                      ·
                        rfl

theorem cell23_6649265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6649265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649265 prefixEnd_6649265 := by exact prefixLift 6649265
  have htrace : WordTrace (prefixWord ++ tailWord_6649265) baseStart_6649265 baseEnd_6649265 := by
    simpa [prefixWord, tailWord_6649265, baseEnd_6649265] using wordTrace_append hprefix tailTrace_6649265
  have hstable : (prefixWord ++ tailWord_6649265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649265).length < 2 ^ (prefixWord ++ tailWord_6649265).sum := by decide
  have hdescent : baseEnd_6649265 < baseStart_6649265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649311 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_6649311 : Nat := 118140960795 + 6649311 * 2 ^ 59
def prefixEnd_6649311 : Nat := 4983230072969 + 3 ^ 40 * 6649311 * 2
def baseEnd_6649311 : Nat := 3414292564228139273832881

theorem tailTrace_6649311 : CollatzResearch.WordTrace tailWord_6649311 prefixEnd_6649311 3414292564228139273832881 := by
  unfold tailWord_6649311
  simp only [CollatzResearch.WordTrace]
  refine ⟨242520296013689333753227787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161680197342459555835485191 242520296013689333753227787)
  ·
    refine ⟨363780444020534000629841681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242520296013689333753227787 363780444020534000629841681)
    ·
      refine ⟨272835333015400500472381261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363780444020534000629841681 272835333015400500472381261)
      ·
        refine ⟨102313249880775187677142973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272835333015400500472381261 102313249880775187677142973)
        ·
          refine ⟨38367468705290695378928615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102313249880775187677142973 38367468705290695378928615)
          ·
            refine ⟨57551203057936043068392923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38367468705290695378928615 57551203057936043068392923)
            ·
              refine ⟨86326804586904064602589385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57551203057936043068392923 86326804586904064602589385)
              ·
                refine ⟨64745103440178048451942039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86326804586904064602589385 64745103440178048451942039)
                ·
                  refine ⟨97117655160267072677913059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64745103440178048451942039 97117655160267072677913059)
                  ·
                    refine ⟨145676482740400609016869589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97117655160267072677913059 145676482740400609016869589)
                    ·
                      refine ⟨3414292564228139273832881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145676482740400609016869589 3414292564228139273832881)
                      ·
                        rfl

theorem cell23_6649311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_6649311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649311 prefixEnd_6649311 := by exact prefixLift 6649311
  have htrace : WordTrace (prefixWord ++ tailWord_6649311) baseStart_6649311 baseEnd_6649311 := by
    simpa [prefixWord, tailWord_6649311, baseEnd_6649311] using wordTrace_append hprefix tailTrace_6649311
  have hstable : (prefixWord ++ tailWord_6649311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649311).length < 2 ^ (prefixWord ++ tailWord_6649311).sum := by decide
  have hdescent : baseEnd_6649311 < baseStart_6649311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649321 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_6649321 : Nat := 118140960795 + 6649321 * 2 ^ 59
def prefixEnd_6649321 : Nat := 4983230072969 + 3 ^ 40 * 6649321 * 2
def baseEnd_6649321 : Nat := 3414297699034684234707835

theorem tailTrace_6649321 : CollatzResearch.WordTrace tailWord_6649321 prefixEnd_6649321 3414297699034684234707835 := by
  unfold tailWord_6649321
  simp only [CollatzResearch.WordTrace]
  refine ⟨242520660743653105461091817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161680440495768736974061211 242520660743653105461091817)
  ·
    refine ⟨181890495557739829095818863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242520660743653105461091817 181890495557739829095818863)
    ·
      refine ⟨272835743336609743643728295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181890495557739829095818863 272835743336609743643728295)
      ·
        refine ⟨409253615004914615465592443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272835743336609743643728295 409253615004914615465592443)
        ·
          refine ⟨613880422507371923198388665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409253615004914615465592443 613880422507371923198388665)
          ·
            refine ⟨460410316880528942398791499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613880422507371923198388665 460410316880528942398791499)
            ·
              refine ⟨690615475320793413598187249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460410316880528942398791499 690615475320793413598187249)
              ·
                refine ⟨517961606490595060198640437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690615475320793413598187249 517961606490595060198640437)
                ·
                  refine ⟨48558900608493286893622541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517961606490595060198640437 48558900608493286893622541)
                  ·
                    refine ⟨18209587728184982585108453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48558900608493286893622541 18209587728184982585108453)
                    ·
                      refine ⟨3414297699034684234707835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18209587728184982585108453 3414297699034684234707835)
                      ·
                        rfl

theorem cell23_6649321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_6649321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649321 prefixEnd_6649321 := by exact prefixLift 6649321
  have htrace : WordTrace (prefixWord ++ tailWord_6649321) baseStart_6649321 baseEnd_6649321 := by
    simpa [prefixWord, tailWord_6649321, baseEnd_6649321] using wordTrace_append hprefix tailTrace_6649321
  have hstable : (prefixWord ++ tailWord_6649321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649321).length < 2 ^ (prefixWord ++ tailWord_6649321).sum := by decide
  have hdescent : baseEnd_6649321 < baseStart_6649321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649338 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_6649338 : Nat := 118140960795 + 6649338 * 2 ^ 59
def prefixEnd_6649338 : Nat := 4983230072969 + 3 ^ 40 * 6649338 * 2
def baseEnd_6649338 : Nat := 3414306428205810668195257

theorem tailTrace_6649338 : CollatzResearch.WordTrace tailWord_6649338 prefixEnd_6649338 3414306428205810668195257 := by
  unfold tailWord_6649338
  simp only [CollatzResearch.WordTrace]
  refine ⟨60630320196147879341115167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161680853856394344909640445 60630320196147879341115167)
  ·
    refine ⟨90945480294221819011672751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60630320196147879341115167 90945480294221819011672751)
    ·
      refine ⟨136418220441332728517509127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90945480294221819011672751 136418220441332728517509127)
      ·
        refine ⟨204627330661999092776263691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136418220441332728517509127 204627330661999092776263691)
        ·
          refine ⟨306940995992998639164395537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204627330661999092776263691 306940995992998639164395537)
          ·
            refine ⟨230205746994748979373296653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306940995992998639164395537 230205746994748979373296653)
            ·
              refine ⟨86327155123030867264986245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230205746994748979373296653 86327155123030867264986245)
              ·
                refine ⟨16186341585568287612184921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86327155123030867264986245 16186341585568287612184921)
                ·
                  refine ⟨12139756189176215709138691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16186341585568287612184921 12139756189176215709138691)
                  ·
                    refine ⟨18209634283764323563708037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12139756189176215709138691 18209634283764323563708037)
                    ·
                      refine ⟨3414306428205810668195257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18209634283764323563708037 3414306428205810668195257)
                      ·
                        rfl

theorem cell23_6649338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_6649338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649338 prefixEnd_6649338 := by exact prefixLift 6649338
  have htrace : WordTrace (prefixWord ++ tailWord_6649338) baseStart_6649338 baseEnd_6649338 := by
    simpa [prefixWord, tailWord_6649338, baseEnd_6649338] using wordTrace_append hprefix tailTrace_6649338
  have hstable : (prefixWord ++ tailWord_6649338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649338).length < 2 ^ (prefixWord ++ tailWord_6649338).sum := by decide
  have hdescent : baseEnd_6649338 < baseStart_6649338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649365 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_6649365 : Nat := 118140960795 + 6649365 * 2 ^ 59
def prefixEnd_6649365 : Nat := 4983230072969 + 3 ^ 40 * 6649365 * 2
def baseEnd_6649365 : Nat := 1138106764061160687519211

theorem tailTrace_6649365 : CollatzResearch.WordTrace tailWord_6649365 prefixEnd_6649365 1138106764061160687519211 := by
  unfold tailWord_6649365
  simp only [CollatzResearch.WordTrace]
  refine ⟨242522265555493700975693549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161681510370329133983795699 242522265555493700975693549)
  ·
    refine ⟨90945849583310137865885081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242522265555493700975693549 90945849583310137865885081)
    ·
      refine ⟨68209387187482603399413811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90945849583310137865885081 68209387187482603399413811)
      ·
        refine ⟨102314080781223905099120717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68209387187482603399413811 102314080781223905099120717)
        ·
          refine ⟨38367780292958964412170269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102314080781223905099120717 38367780292958964412170269)
          ·
            refine ⟨14387917609859611654563851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38367780292958964412170269 14387917609859611654563851)
            ·
              refine ⟨21581876414789417481845777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387917609859611654563851 21581876414789417481845777)
              ·
                refine ⟨16186407311092063111384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21581876414789417481845777 16186407311092063111384333)
                ·
                  refine ⟨6069902741659523666769125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16186407311092063111384333 6069902741659523666769125)
                  ·
                    refine ⟨1138106764061160687519211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069902741659523666769125 1138106764061160687519211)
                    ·
                      rfl

theorem cell23_6649365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_6649365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649365 prefixEnd_6649365 := by exact prefixLift 6649365
  have htrace : WordTrace (prefixWord ++ tailWord_6649365) baseStart_6649365 baseEnd_6649365 := by
    simpa [prefixWord, tailWord_6649365, baseEnd_6649365] using wordTrace_append hprefix tailTrace_6649365
  have hstable : (prefixWord ++ tailWord_6649365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649365).length < 2 ^ (prefixWord ++ tailWord_6649365).sum := by decide
  have hdescent : baseEnd_6649365 < baseStart_6649365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649375 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_6649375 : Nat := 118140960795 + 6649375 * 2 ^ 59
def prefixEnd_6649375 : Nat := 4983230072969 + 3 ^ 40 * 6649375 * 2
def baseEnd_6649375 : Nat := 3414325426990027023432587

theorem tailTrace_6649375 : CollatzResearch.WordTrace tailWord_6649375 prefixEnd_6649375 3414325426990027023432587 := by
  unfold tailWord_6649375
  simp only [CollatzResearch.WordTrace]
  refine ⟨242522630285457472683557579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161681753523638315122371719 242522630285457472683557579)
  ·
    refine ⟨363783945428186209025336369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242522630285457472683557579 363783945428186209025336369)
    ·
      refine ⟨272837959071139656769002277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363783945428186209025336369 272837959071139656769002277)
      ·
        refine ⟨51157117325838685644187927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272837959071139656769002277 51157117325838685644187927)
        ·
          refine ⟨76735675988758028466281891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51157117325838685644187927 76735675988758028466281891)
          ·
            refine ⟨115103513983137042699422837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76735675988758028466281891 115103513983137042699422837)
            ·
              refine ⟨10790954435919097753070891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115103513983137042699422837 10790954435919097753070891)
              ·
                refine ⟨16186431653878646629606337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790954435919097753070891 16186431653878646629606337)
                ·
                  refine ⟨12139823740408984972204753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16186431653878646629606337 12139823740408984972204753)
                  ·
                    refine ⟨9104867805306738729153565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12139823740408984972204753 9104867805306738729153565)
                    ·
                      refine ⟨3414325426990027023432587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9104867805306738729153565 3414325426990027023432587)
                      ·
                        rfl

theorem cell23_6649375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_6649375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649375 prefixEnd_6649375 := by exact prefixLift 6649375
  have htrace : WordTrace (prefixWord ++ tailWord_6649375) baseStart_6649375 baseEnd_6649375 := by
    simpa [prefixWord, tailWord_6649375, baseEnd_6649375] using wordTrace_append hprefix tailTrace_6649375
  have hstable : (prefixWord ++ tailWord_6649375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649375).length < 2 ^ (prefixWord ++ tailWord_6649375).sum := by decide
  have hdescent : baseEnd_6649375 < baseStart_6649375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649395 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 6]
def baseStart_6649395 : Nat := 118140960795 + 6649395 * 2 ^ 59
def prefixEnd_6649395 : Nat := 4983230072969 + 3 ^ 40 * 6649395 * 2
def baseEnd_6649395 : Nat := 379370632955901882798055

theorem tailTrace_6649395 : CollatzResearch.WordTrace tailWord_6649395 prefixEnd_6649395 379370632955901882798055 := by
  unfold tailWord_6649395
  simp only [CollatzResearch.WordTrace]
  refine ⟨242523359745385016099285639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161682239830256677399523759 242523359745385016099285639)
  ·
    refine ⟨363785039618077524148928459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242523359745385016099285639 363785039618077524148928459)
    ·
      refine ⟨545677559427116286223392689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363785039618077524148928459 545677559427116286223392689)
      ·
        refine ⟨409258169570337214667544517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545677559427116286223392689 409258169570337214667544517)
        ·
          refine ⟨76735906794438227750164597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409258169570337214667544517 76735906794438227750164597)
          ·
            refine ⟨7193991261978583851577931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76735906794438227750164597 7193991261978583851577931)
            ·
              refine ⟨10790986892967875777366897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193991261978583851577931 10790986892967875777366897)
              ·
                refine ⟨8093240169725906833025173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790986892967875777366897 8093240169725906833025173)
                ·
                  refine ⟨379370632955901882798055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093240169725906833025173 379370632955901882798055)
                  ·
                    rfl

theorem cell23_6649395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 6].length) (baseStart_6649395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649395 prefixEnd_6649395 := by exact prefixLift 6649395
  have htrace : WordTrace (prefixWord ++ tailWord_6649395) baseStart_6649395 baseEnd_6649395 := by
    simpa [prefixWord, tailWord_6649395, baseEnd_6649395] using wordTrace_append hprefix tailTrace_6649395
  have hstable : (prefixWord ++ tailWord_6649395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649395).length < 2 ^ (prefixWord ++ tailWord_6649395).sum := by decide
  have hdescent : baseEnd_6649395 < baseStart_6649395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649425 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_6649425 : Nat := 118140960795 + 6649425 * 2 ^ 59
def prefixEnd_6649425 : Nat := 4983230072969 + 3 ^ 40 * 6649425 * 2
def baseEnd_6649425 : Nat := 1138117033674250609269119

theorem tailTrace_6649425 : CollatzResearch.WordTrace tailWord_6649425 prefixEnd_6649425 1138117033674250609269119 := by
  unfold tailWord_6649425
  simp only [CollatzResearch.WordTrace]
  refine ⟨242524453935276331222877729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161682969290184220815251819 242524453935276331222877729)
  ·
    refine ⟨181893340451457248417158297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242524453935276331222877729 181893340451457248417158297)
    ·
      refine ⟨136420005338592936312868723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181893340451457248417158297 136420005338592936312868723)
      ·
        refine ⟨204630008007889404469303085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136420005338592936312868723 204630008007889404469303085)
        ·
          refine ⟨76736253002958526675988657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204630008007889404469303085 76736253002958526675988657)
          ·
            refine ⟨57552189752218895006991493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76736253002958526675988657 57552189752218895006991493)
            ·
              refine ⟨10791035578541042813810905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57552189752218895006991493 10791035578541042813810905)
              ·
                refine ⟨8093276683905782110358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10791035578541042813810905 8093276683905782110358179)
                ·
                  refine ⟨12139915025858673165537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8093276683905782110358179 12139915025858673165537269)
                  ·
                    refine ⟨1138117033674250609269119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12139915025858673165537269 1138117033674250609269119)
                    ·
                      rfl

theorem cell23_6649425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_6649425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649425 prefixEnd_6649425 := by exact prefixLift 6649425
  have htrace : WordTrace (prefixWord ++ tailWord_6649425) baseStart_6649425 baseEnd_6649425 := by
    simpa [prefixWord, tailWord_6649425, baseEnd_6649425] using wordTrace_append hprefix tailTrace_6649425
  have hstable : (prefixWord ++ tailWord_6649425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649425).length < 2 ^ (prefixWord ++ tailWord_6649425).sum := by decide
  have hdescent : baseEnd_6649425 < baseStart_6649425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649455 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 2, 4]
def baseStart_6649455 : Nat := 118140960795 + 6649455 * 2 ^ 59
def prefixEnd_6649455 : Nat := 4983230072969 + 3 ^ 40 * 6649455 * 2
def baseEnd_6649455 : Nat := 1138122168480795570144073

theorem tailTrace_6649455 : CollatzResearch.WordTrace tailWord_6649455 prefixEnd_6649455 1138122168480795570144073 := by
  unfold tailWord_6649455
  simp only [CollatzResearch.WordTrace]
  refine ⟨242525548125167646346469819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161683698750111764230979879 242525548125167646346469819)
  ·
    refine ⟨363788322187751469519704729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242525548125167646346469819 363788322187751469519704729)
    ·
      refine ⟨272841241640813602139778547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363788322187751469519704729 272841241640813602139778547)
      ·
        refine ⟨409261862461220403209667821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272841241640813602139778547 409261862461220403209667821)
        ·
          refine ⟨153473198422957651203625433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409261862461220403209667821 153473198422957651203625433)
          ·
            refine ⟨115104898817218238402719075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153473198422957651203625433 115104898817218238402719075)
            ·
              refine ⟨172657348225827357604078613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115104898817218238402719075 172657348225827357604078613)
              ·
                refine ⟨8093313198085657387691185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172657348225827357604078613 8093313198085657387691185)
                ·
                  refine ⟨6069984898564243040768389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8093313198085657387691185 6069984898564243040768389)
                  ·
                    refine ⟨1138122168480795570144073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069984898564243040768389 1138122168480795570144073)
                    ·
                      rfl

theorem cell23_6649455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_6649455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649455 prefixEnd_6649455 := by exact prefixLift 6649455
  have htrace : WordTrace (prefixWord ++ tailWord_6649455) baseStart_6649455 baseEnd_6649455 := by
    simpa [prefixWord, tailWord_6649455, baseEnd_6649455] using wordTrace_append hprefix tailTrace_6649455
  have hstable : (prefixWord ++ tailWord_6649455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649455).length < 2 ^ (prefixWord ++ tailWord_6649455).sum := by decide
  have hdescent : baseEnd_6649455 < baseStart_6649455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649456 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 1, 1, 3]
def baseStart_6649456 : Nat := 118140960795 + 6649456 * 2 ^ 59
def prefixEnd_6649456 : Nat := 4983230072969 + 3 ^ 40 * 6649456 * 2
def baseEnd_6649456 : Nat := 3414367018923041206519715

theorem tailTrace_6649456 : CollatzResearch.WordTrace tailWord_6649456 prefixEnd_6649456 3414367018923041206519715 := by
  unfold tailWord_6649456
  simp only [CollatzResearch.WordTrace]
  refine ⟨121262792299082011758628111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161683723065442682344837481 121262792299082011758628111)
  ·
    refine ⟨181894188448623017637942167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121262792299082011758628111 181894188448623017637942167)
    ·
      refine ⟨272841282672934526456913251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181894188448623017637942167 272841282672934526456913251)
      ·
        refine ⟨409261924009401789685369877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272841282672934526456913251 409261924009401789685369877)
        ·
          refine ⟨19184152687940708891501713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 409261924009401789685369877 19184152687940708891501713)
          ·
            refine ⟨14388114515955531668626285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19184152687940708891501713 14388114515955531668626285)
            ·
              refine ⟨5395542943483324375734857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14388114515955531668626285 5395542943483324375734857)
              ·
                refine ⟨4046657207612493281801143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395542943483324375734857 4046657207612493281801143)
                ·
                  refine ⟨6069985811418739922701715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046657207612493281801143 6069985811418739922701715)
                  ·
                    refine ⟨9104978717128109884052573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069985811418739922701715 9104978717128109884052573)
                    ·
                      refine ⟨3414367018923041206519715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9104978717128109884052573 3414367018923041206519715)
                      ·
                        rfl

theorem cell23_6649456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 1, 3].length) (baseStart_6649456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649456 prefixEnd_6649456 := by exact prefixLift 6649456
  have htrace : WordTrace (prefixWord ++ tailWord_6649456) baseStart_6649456 baseEnd_6649456 := by
    simpa [prefixWord, tailWord_6649456, baseEnd_6649456] using wordTrace_append hprefix tailTrace_6649456
  have hstable : (prefixWord ++ tailWord_6649456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649456).length < 2 ^ (prefixWord ++ tailWord_6649456).sum := by decide
  have hdescent : baseEnd_6649456 < baseStart_6649456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649465 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_6649465 : Nat := 118140960795 + 6649465 * 2 ^ 59
def prefixEnd_6649465 : Nat := 4983230072969 + 3 ^ 40 * 6649465 * 2
def baseEnd_6649465 : Nat := 3414371640248931671307173

theorem tailTrace_6649465 : CollatzResearch.WordTrace tailWord_6649465 prefixEnd_6649465 3414371640248931671307173 := by
  unfold tailWord_6649465
  simp only [CollatzResearch.WordTrace]
  refine ⟨242525912855131418054333849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161683941903420945369555899 242525912855131418054333849)
  ·
    refine ⟨181894434641348563540750387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242525912855131418054333849 181894434641348563540750387)
    ·
      refine ⟨272841651962022845311125581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181894434641348563540750387 272841651962022845311125581)
      ·
        refine ⟨102315619485758566991672093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272841651962022845311125581 102315619485758566991672093)
        ·
          refine ⟨38368357307159462621877035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102315619485758566991672093 38368357307159462621877035)
          ·
            refine ⟨57552535960739193932815553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38368357307159462621877035 57552535960739193932815553)
            ·
              refine ⟨43164401970554395449611665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57552535960739193932815553 43164401970554395449611665)
              ·
                refine ⟨32373301477915796587208749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43164401970554395449611665 32373301477915796587208749)
                ·
                  refine ⟨12139988054218423720203281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32373301477915796587208749 12139988054218423720203281)
                  ·
                    refine ⟨9104991040663817790152461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12139988054218423720203281 9104991040663817790152461)
                    ·
                      refine ⟨3414371640248931671307173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9104991040663817790152461 3414371640248931671307173)
                      ·
                        rfl

theorem cell23_6649465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_6649465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649465 prefixEnd_6649465 := by exact prefixLift 6649465
  have htrace : WordTrace (prefixWord ++ tailWord_6649465) baseStart_6649465 baseEnd_6649465 := by
    simpa [prefixWord, tailWord_6649465, baseEnd_6649465] using wordTrace_append hprefix tailTrace_6649465
  have hstable : (prefixWord ++ tailWord_6649465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649465).length < 2 ^ (prefixWord ++ tailWord_6649465).sum := by decide
  have hdescent : baseEnd_6649465 < baseStart_6649465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649482 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_6649482 : Nat := 118140960795 + 6649482 * 2 ^ 59
def prefixEnd_6649482 : Nat := 4983230072969 + 3 ^ 40 * 6649482 * 2
def baseEnd_6649482 : Nat := 3414380369420058104794595

theorem tailTrace_6649482 : CollatzResearch.WordTrace tailWord_6649482 prefixEnd_6649482 3414380369420058104794595 := by
  unfold tailWord_6649482
  simp only [CollatzResearch.WordTrace]
  refine ⟨60631633224017457489425675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161684355264046553305135133 60631633224017457489425675)
  ·
    refine ⟨90947449836026186234138513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60631633224017457489425675 90947449836026186234138513)
    ·
      refine ⟨68210587377019639675603885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90947449836026186234138513 68210587377019639675603885)
      ·
        refine ⟨25578970266382364878351457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68210587377019639675603885 25578970266382364878351457)
        ·
          refine ⟨19184227699786773658763593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25578970266382364878351457 19184227699786773658763593)
          ·
            refine ⟨14388170774840080244072695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19184227699786773658763593 14388170774840080244072695)
            ·
              refine ⟨21582256162260120366109043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14388170774840080244072695 21582256162260120366109043)
              ·
                refine ⟨32373384243390180549163565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21582256162260120366109043 32373384243390180549163565)
                ·
                  refine ⟨12140019091271317705936337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32373384243390180549163565 12140019091271317705936337)
                  ·
                    refine ⟨9105014318453488279452253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12140019091271317705936337 9105014318453488279452253)
                    ·
                      refine ⟨3414380369420058104794595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105014318453488279452253 3414380369420058104794595)
                      ·
                        rfl

theorem cell23_6649482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_6649482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649482 prefixEnd_6649482 := by exact prefixLift 6649482
  have htrace : WordTrace (prefixWord ++ tailWord_6649482) baseStart_6649482 baseEnd_6649482 := by
    simpa [prefixWord, tailWord_6649482, baseEnd_6649482] using wordTrace_append hprefix tailTrace_6649482
  have hstable : (prefixWord ++ tailWord_6649482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649482).length < 2 ^ (prefixWord ++ tailWord_6649482).sum := by decide
  have hdescent : baseEnd_6649482 < baseStart_6649482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649495 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_6649495 : Nat := 118140960795 + 6649495 * 2 ^ 59
def prefixEnd_6649495 : Nat := 4983230072969 + 3 ^ 40 * 6649495 * 2
def baseEnd_6649495 : Nat := 3414387044668566553932035

theorem tailTrace_6649495 : CollatzResearch.WordTrace tailWord_6649495 prefixEnd_6649495 3414387044668566553932035 := by
  unfold tailWord_6649495
  simp only [CollatzResearch.WordTrace]
  refine ⟨242527007045022733177925939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161684671363348488785283959 242527007045022733177925939)
  ·
    refine ⟨363790510567534099766888909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242527007045022733177925939 363790510567534099766888909)
    ·
      refine ⟨136421441462825287412583341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363790510567534099766888909 136421441462825287412583341)
      ·
        refine ⟨51158040548559482779718753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136421441462825287412583341 51158040548559482779718753)
        ·
          refine ⟨38368530411419612084789065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51158040548559482779718753 38368530411419612084789065)
          ·
            refine ⟨28776397808564709063591799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38368530411419612084789065 28776397808564709063591799)
            ·
              refine ⟨43164596712847063595387699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28776397808564709063591799 43164596712847063595387699)
              ·
                refine ⟨64746895069270595393081549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43164596712847063595387699 64746895069270595393081549)
                ·
                  refine ⟨24280085650976473272405581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64746895069270595393081549 24280085650976473272405581)
                  ·
                    refine ⟨9105032119116177477152093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24280085650976473272405581 9105032119116177477152093)
                    ·
                      refine ⟨3414387044668566553932035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105032119116177477152093 3414387044668566553932035)
                      ·
                        rfl

theorem cell23_6649495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_6649495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649495 prefixEnd_6649495 := by exact prefixLift 6649495
  have htrace : WordTrace (prefixWord ++ tailWord_6649495) baseStart_6649495 baseEnd_6649495 := by
    simpa [prefixWord, tailWord_6649495, baseEnd_6649495] using wordTrace_append hprefix tailTrace_6649495
  have hstable : (prefixWord ++ tailWord_6649495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649495).length < 2 ^ (prefixWord ++ tailWord_6649495).sum := by decide
  have hdescent : baseEnd_6649495 < baseStart_6649495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649506 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_6649506 : Nat := 118140960795 + 6649506 * 2 ^ 59
def prefixEnd_6649506 : Nat := 4983230072969 + 3 ^ 40 * 6649506 * 2
def baseEnd_6649506 : Nat := 1138130897651922003631495

theorem tailTrace_6649506 : CollatzResearch.WordTrace tailWord_6649506 prefixEnd_6649506 1138130897651922003631495 := by
  unfold tailWord_6649506
  simp only [CollatzResearch.WordTrace]
  refine ⟨60631852061995720514144093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161684938831988588037717581 60631852061995720514144093)
  ·
    refine ⟨22736944523248395192804035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60631852061995720514144093 22736944523248395192804035)
    ·
      refine ⟨34105416784872592789206053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22736944523248395192804035 34105416784872592789206053)
      ·
        refine ⟨6394765647163611147976135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34105416784872592789206053 6394765647163611147976135)
        ·
          refine ⟨9592148470745416721964203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394765647163611147976135 9592148470745416721964203)
          ·
            refine ⟨14388222706118125082946305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592148470745416721964203 14388222706118125082946305)
            ·
              refine ⟨10791167029588593812209729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14388222706118125082946305 10791167029588593812209729)
              ·
                refine ⟨8093375272191445359157297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10791167029588593812209729 8093375272191445359157297)
                ·
                  refine ⟨6070031454143584019367973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8093375272191445359157297 6070031454143584019367973)
                  ·
                    refine ⟨1138130897651922003631495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070031454143584019367973 1138130897651922003631495)
                    ·
                      rfl

theorem cell23_6649506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_6649506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649506 prefixEnd_6649506 := by exact prefixLift 6649506
  have htrace : WordTrace (prefixWord ++ tailWord_6649506) baseStart_6649506 baseEnd_6649506 := by
    simpa [prefixWord, tailWord_6649506, baseEnd_6649506] using wordTrace_append hprefix tailTrace_6649506
  have hstable : (prefixWord ++ tailWord_6649506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649506).length < 2 ^ (prefixWord ++ tailWord_6649506).sum := by decide
  have hdescent : baseEnd_6649506 < baseStart_6649506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649522 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_6649522 : Nat := 118140960795 + 6649522 * 2 ^ 59
def prefixEnd_6649522 : Nat := 4983230072969 + 3 ^ 40 * 6649522 * 2
def baseEnd_6649522 : Nat := 3414400908646237948294411

theorem tailTrace_6649522 : CollatzResearch.WordTrace tailWord_6649522 prefixEnd_6649522 3414400908646237948294411 := by
  unfold tailWord_6649522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60631997953981229197289705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161685327877283277859439213 60631997953981229197289705)
  ·
    refine ⟨45473998465485921897967279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60631997953981229197289705 45473998465485921897967279)
    ·
      refine ⟨68210997698228882846950919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45473998465485921897967279 68210997698228882846950919)
      ·
        refine ⟨102316496547343324270426379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68210997698228882846950919 102316496547343324270426379)
        ·
          refine ⟨153474744821014986405639569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102316496547343324270426379 153474744821014986405639569)
          ·
            refine ⟨115106058615761239804229677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153474744821014986405639569 115106058615761239804229677)
            ·
              refine ⟨43164771980910464926586129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115106058615761239804229677 43164771980910464926586129)
              ·
                refine ⟨32373578985682848694939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43164771980910464926586129 32373578985682848694939597)
                ·
                  refine ⟨12140092119631068260602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32373578985682848694939597 12140092119631068260602349)
                  ·
                    refine ⟨4552534544861650597725881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12140092119631068260602349 4552534544861650597725881)
                    ·
                      refine ⟨3414400908646237948294411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552534544861650597725881 3414400908646237948294411)
                      ·
                        rfl

theorem cell23_6649522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_6649522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649522 prefixEnd_6649522 := by exact prefixLift 6649522
  have htrace : WordTrace (prefixWord ++ tailWord_6649522) baseStart_6649522 baseEnd_6649522 := by
    simpa [prefixWord, tailWord_6649522, baseEnd_6649522] using wordTrace_append hprefix tailTrace_6649522
  have hstable : (prefixWord ++ tailWord_6649522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649522).length < 2 ^ (prefixWord ++ tailWord_6649522).sum := by decide
  have hdescent : baseEnd_6649522 < baseStart_6649522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649556 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6649556 : Nat := 118140960795 + 6649556 * 2 ^ 59
def prefixEnd_6649556 : Nat := 4983230072969 + 3 ^ 40 * 6649556 * 2
def baseEnd_6649556 : Nat := 3414418366988490815269255

theorem tailTrace_6649556 : CollatzResearch.WordTrace tailWord_6649556 prefixEnd_6649556 3414418366988490815269255 := by
  unfold tailWord_6649556
  simp only [CollatzResearch.WordTrace]
  refine ⟨121264615948900870297948261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161686154598534493730597681 121264615948900870297948261)
  ·
    refine ⟨22737115490418913180865299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121264615948900870297948261 22737115490418913180865299)
    ·
      refine ⟨34105673235628369771297949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22737115490418913180865299 34105673235628369771297949)
      ·
        refine ⟨12789627463360638664236731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34105673235628369771297949 12789627463360638664236731)
        ·
          refine ⟨19184441195040957996355097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12789627463360638664236731 19184441195040957996355097)
          ·
            refine ⟨14388330896280718497266323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19184441195040957996355097 14388330896280718497266323)
            ·
              refine ⟨21582496344421077745899485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14388330896280718497266323 21582496344421077745899485)
              ·
                refine ⟨8093436129157904154712307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21582496344421077745899485 8093436129157904154712307)
                ·
                  refine ⟨12140154193736856232068461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8093436129157904154712307 12140154193736856232068461)
                  ·
                    refine ⟨4552557822651321087025673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12140154193736856232068461 4552557822651321087025673)
                    ·
                      refine ⟨3414418366988490815269255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552557822651321087025673 3414418366988490815269255)
                      ·
                        rfl

theorem cell23_6649556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6649556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649556 prefixEnd_6649556 := by exact prefixLift 6649556
  have htrace : WordTrace (prefixWord ++ tailWord_6649556) baseStart_6649556 baseEnd_6649556 := by
    simpa [prefixWord, tailWord_6649556, baseEnd_6649556] using wordTrace_append hprefix tailTrace_6649556
  have hstable : (prefixWord ++ tailWord_6649556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649556).length < 2 ^ (prefixWord ++ tailWord_6649556).sum := by decide
  have hdescent : baseEnd_6649556 < baseStart_6649556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649669 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_6649669 : Nat := 118140960795 + 6649669 * 2 ^ 59
def prefixEnd_6649669 : Nat := 4983230072969 + 3 ^ 40 * 6649669 * 2
def baseEnd_6649669 : Nat := 1138158796767482957718745

theorem tailTrace_6649669 : CollatzResearch.WordTrace tailWord_6649669 prefixEnd_6649669 1138158796767482957718745 := by
  unfold tailWord_6649669
  simp only [CollatzResearch.WordTrace]
  refine ⟨242533353346392360894760061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161688902230928240596506707 242533353346392360894760061)
  ·
    refine ⟨90950007504897135335535023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242533353346392360894760061 90950007504897135335535023)
    ·
      refine ⟨136425011257345703003302535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90950007504897135335535023 136425011257345703003302535)
      ·
        refine ⟨204637516886018554504953803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136425011257345703003302535 204637516886018554504953803)
        ·
          refine ⟨306956275329027831757430705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204637516886018554504953803 306956275329027831757430705)
          ·
            refine ⟨230217206496770873818073029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306956275329027831757430705 230217206496770873818073029)
            ·
              refine ⟨43165726218144538840888693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230217206496770873818073029 43165726218144538840888693)
              ·
                refine ⟨4046786832951050516333315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43165726218144538840888693 4046786832951050516333315)
                ·
                  refine ⟨6070180249426575774499973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046786832951050516333315 6070180249426575774499973)
                  ·
                    refine ⟨1138158796767482957718745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070180249426575774499973 1138158796767482957718745)
                    ·
                      rfl

theorem cell23_6649669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_6649669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649669 prefixEnd_6649669 := by exact prefixLift 6649669
  have htrace : WordTrace (prefixWord ++ tailWord_6649669) baseStart_6649669 baseEnd_6649669 := by
    simpa [prefixWord, tailWord_6649669, baseEnd_6649669] using wordTrace_append hprefix tailTrace_6649669
  have hstable : (prefixWord ++ tailWord_6649669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649669).length < 2 ^ (prefixWord ++ tailWord_6649669).sum := by decide
  have hdescent : baseEnd_6649669 < baseStart_6649669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649682 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_6649682 : Nat := 118140960795 + 6649682 * 2 ^ 59
def prefixEnd_6649682 : Nat := 4983230072969 + 3 ^ 40 * 6649682 * 2
def baseEnd_6649682 : Nat := 379387007283439702477075

theorem tailTrace_6649682 : CollatzResearch.WordTrace tailWord_6649682 prefixEnd_6649682 379387007283439702477075 := by
  unfold tailWord_6649682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633456873836316028745825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161689218330230176076655533 60633456873836316028745825)
  ·
    refine ⟨45475092655377237021559369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60633456873836316028745825 45475092655377237021559369)
    ·
      refine ⟨34106319491532927766169527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45475092655377237021559369 34106319491532927766169527)
      ·
        refine ⟨51159479237299391649254291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34106319491532927766169527 51159479237299391649254291)
        ·
          refine ⟨76739218855949087473881437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51159479237299391649254291 76739218855949087473881437)
          ·
            refine ⟨28777207070980907802705539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76739218855949087473881437 28777207070980907802705539)
            ·
              refine ⟨43165810606471361704058309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28777207070980907802705539 43165810606471361704058309)
              ·
                refine ⟨8093589488713380319510933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43165810606471361704058309 8093589488713380319510933)
                ·
                  refine ⟨379387007283439702477075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093589488713380319510933 379387007283439702477075)
                  ·
                    rfl

theorem cell23_6649682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_6649682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649682 prefixEnd_6649682 := by exact prefixLift 6649682
  have htrace : WordTrace (prefixWord ++ tailWord_6649682) baseStart_6649682 baseEnd_6649682 := by
    simpa [prefixWord, tailWord_6649682, baseEnd_6649682] using wordTrace_append hprefix tailTrace_6649682
  have hstable : (prefixWord ++ tailWord_6649682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649682).length < 2 ^ (prefixWord ++ tailWord_6649682).sum := by decide
  have hdescent : baseEnd_6649682 < baseStart_6649682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649709 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6649709 : Nat := 118140960795 + 6649709 * 2 ^ 59
def prefixEnd_6649709 : Nat := 4983230072969 + 3 ^ 40 * 6649709 * 2
def baseEnd_6649709 : Nat := 3414496929528628716656051

theorem tailTrace_6649709 : CollatzResearch.WordTrace tailWord_6649709 prefixEnd_6649709 3414496929528628716656051 := by
  unfold tailWord_6649709
  simp only [CollatzResearch.WordTrace]
  refine ⟨242534812266247447726216181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161689874844164965150810787 242534812266247447726216181)
  ·
    refine ⟨22737638649960698224332767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242534812266247447726216181 22737638649960698224332767)
    ·
      refine ⟨34106457974941047336499151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22737638649960698224332767 34106457974941047336499151)
      ·
        refine ⟨51159686962411571004748727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34106457974941047336499151 51159686962411571004748727)
        ·
          refine ⟨76739530443617356507123091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51159686962411571004748727 76739530443617356507123091)
          ·
            refine ⟨115109295665426034760684637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76739530443617356507123091 115109295665426034760684637)
            ·
              refine ⟨43165985874534763035256739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115109295665426034760684637 43165985874534763035256739)
              ·
                refine ⟨64748978811802144552885109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43165985874534763035256739 64748978811802144552885109)
                ·
                  refine ⟨6070216763606451051832979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64748978811802144552885109 6070216763606451051832979)
                  ·
                    refine ⟨9105325145409676577749469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6070216763606451051832979 9105325145409676577749469)
                    ·
                      refine ⟨3414496929528628716656051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105325145409676577749469 3414496929528628716656051)
                      ·
                        rfl

theorem cell23_6649709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6649709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649709 prefixEnd_6649709 := by exact prefixLift 6649709
  have htrace : WordTrace (prefixWord ++ tailWord_6649709) baseStart_6649709 baseEnd_6649709 := by
    simpa [prefixWord, tailWord_6649709, baseEnd_6649709] using wordTrace_append hprefix tailTrace_6649709
  have hstable : (prefixWord ++ tailWord_6649709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649709).length < 2 ^ (prefixWord ++ tailWord_6649709).sum := by decide
  have hdescent : baseEnd_6649709 < baseStart_6649709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649712 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_6649712 : Nat := 118140960795 + 6649712 * 2 ^ 59
def prefixEnd_6649712 : Nat := 4983230072969 + 3 ^ 40 * 6649712 * 2
def baseEnd_6649712 : Nat := 1138166156656864068306179

theorem tailTrace_6649712 : CollatzResearch.WordTrace tailWord_6649712 prefixEnd_6649712 1138166156656864068306179 := by
  unfold tailWord_6649712
  simp only [CollatzResearch.WordTrace]
  refine ⟨121267460842618289619287695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161689947790157719492383593 121267460842618289619287695)
  ·
    refine ⟨181901191263927434428931543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121267460842618289619287695 181901191263927434428931543)
    ·
      refine ⟨272851786895891151643397315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181901191263927434428931543 272851786895891151643397315)
      ·
        refine ⟨409277680343836727465095973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272851786895891151643397315 409277680343836727465095973)
        ·
          refine ⟨76739565064469386399705495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409277680343836727465095973 76739565064469386399705495)
          ·
            refine ⟨115109347596704079599558243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76739565064469386399705495 115109347596704079599558243)
            ·
              refine ⟨172664021395056119399337365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115109347596704079599558243 172664021395056119399337365)
              ·
                refine ⟨8093626002893255596843939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172664021395056119399337365 8093626002893255596843939)
                ·
                  refine ⟨12140439004339883395265909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8093626002893255596843939 12140439004339883395265909)
                  ·
                    refine ⟨1138166156656864068306179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12140439004339883395265909 1138166156656864068306179)
                    ·
                      rfl

theorem cell23_6649712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_6649712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649712 prefixEnd_6649712 := by exact prefixLift 6649712
  have htrace : WordTrace (prefixWord ++ tailWord_6649712) baseStart_6649712 baseEnd_6649712 := by
    simpa [prefixWord, tailWord_6649712, baseEnd_6649712] using wordTrace_append hprefix tailTrace_6649712
  have hstable : (prefixWord ++ tailWord_6649712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649712).length < 2 ^ (prefixWord ++ tailWord_6649712).sum := by decide
  have hdescent : baseEnd_6649712 < baseStart_6649712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649750 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6649750 : Nat := 118140960795 + 6649750 * 2 ^ 59
def prefixEnd_6649750 : Nat := 4983230072969 + 3 ^ 40 * 6649750 * 2
def baseEnd_6649750 : Nat := 379390886915051450693707

theorem tailTrace_6649750 : CollatzResearch.WordTrace tailWord_6649750 prefixEnd_6649750 379390886915051450693707 := by
  unfold tailWord_6649750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158519228693681983028669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161690871772732607818972469 15158519228693681983028669)
  ·
    refine ⟨5684444710760130743635751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15158519228693681983028669 5684444710760130743635751)
    ·
      refine ⟨8526667066140196115453627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684444710760130743635751 8526667066140196115453627)
      ·
        refine ⟨12790000599210294173180441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8526667066140196115453627 12790000599210294173180441)
        ·
          refine ⟨9592500449407720629885331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790000599210294173180441 9592500449407720629885331)
          ·
            refine ⟨14388750674111580944827997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592500449407720629885331 14388750674111580944827997)
            ·
              refine ⟨5395781502791842854310499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14388750674111580944827997 5395781502791842854310499)
              ·
                refine ⟨8093672254187764281465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395781502791842854310499 8093672254187764281465749)
                ·
                  refine ⟨379390886915051450693707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093672254187764281465749 379390886915051450693707)
                  ·
                    rfl

theorem cell23_6649750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6649750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649750 prefixEnd_6649750 := by exact prefixLift 6649750
  have htrace : WordTrace (prefixWord ++ tailWord_6649750) baseStart_6649750 baseEnd_6649750 := by
    simpa [prefixWord, tailWord_6649750, baseEnd_6649750] using wordTrace_append hprefix tailTrace_6649750
  have hstable : (prefixWord ++ tailWord_6649750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649750).length < 2 ^ (prefixWord ++ tailWord_6649750).sum := by decide
  have hdescent : baseEnd_6649750 < baseStart_6649750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649810 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_6649810 : Nat := 118140960795 + 6649810 * 2 ^ 59
def prefixEnd_6649810 : Nat := 4983230072969 + 3 ^ 40 * 6649810 * 2
def baseEnd_6649810 : Nat := 1138182930358244273831029

theorem tailTrace_6649810 : CollatzResearch.WordTrace tailWord_6649810 prefixEnd_6649810 1138182930358244273831029 := by
  unfold tailWord_6649810
  simp only [CollatzResearch.WordTrace]
  refine ⟨60634624009720385493910721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161692330692587694650428589 60634624009720385493910721)
  ·
    refine ⟨45475968007290289120433041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60634624009720385493910721 45475968007290289120433041)
    ·
      refine ⟨34106976005467716840324781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45475968007290289120433041 34106976005467716840324781)
      ·
        refine ⟨12790116002050393815121793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34106976005467716840324781 12790116002050393815121793)
        ·
          refine ⟨9592587001537795361341345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790116002050393815121793 9592587001537795361341345)
          ·
            refine ⟨7194440251153346521006009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9592587001537795361341345 7194440251153346521006009)
            ·
              refine ⟨5395830188365009890754507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194440251153346521006009 5395830188365009890754507)
              ·
                refine ⟨8093745282547514836131761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395830188365009890754507 8093745282547514836131761)
                ·
                  refine ⟨6070308961910636127098821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8093745282547514836131761 6070308961910636127098821)
                  ·
                    refine ⟨1138182930358244273831029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070308961910636127098821 1138182930358244273831029)
                    ·
                      rfl

theorem cell23_6649810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_6649810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649810 prefixEnd_6649810 := by exact prefixLift 6649810
  have htrace : WordTrace (prefixWord ++ tailWord_6649810) baseStart_6649810 baseEnd_6649810 := by
    simpa [prefixWord, tailWord_6649810, baseEnd_6649810] using wordTrace_append hprefix tailTrace_6649810
  have hstable : (prefixWord ++ tailWord_6649810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649810).length < 2 ^ (prefixWord ++ tailWord_6649810).sum := by decide
  have hdescent : baseEnd_6649810 < baseStart_6649810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649816 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_6649816 : Nat := 118140960795 + 6649816 * 2 ^ 59
def prefixEnd_6649816 : Nat := 4983230072969 + 3 ^ 40 * 6649816 * 2
def baseEnd_6649816 : Nat := 3414551871958659798018059

theorem tailTrace_6649816 : CollatzResearch.WordTrace tailWord_6649816 prefixEnd_6649816 3414551871958659798018059 := by
  unfold tailWord_6649816
  simp only [CollatzResearch.WordTrace]
  refine ⟨121269357438429902500180651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161692476584573203333574201 121269357438429902500180651)
  ·
    refine ⟨181904036157644853750270977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121269357438429902500180651 181904036157644853750270977)
    ·
      refine ⟨136428027118233640312703233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181904036157644853750270977 136428027118233640312703233)
      ·
        refine ⟨102321020338675230234527425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136428027118233640312703233 102321020338675230234527425)
        ·
          refine ⟨76740765254006422675895569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102321020338675230234527425 76740765254006422675895569)
          ·
            refine ⟨57555573940504817006921677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76740765254006422675895569 57555573940504817006921677)
            ·
              refine ⟨21583340227689306377595629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57555573940504817006921677 21583340227689306377595629)
              ·
                refine ⟨8093752585383489891598361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21583340227689306377595629 8093752585383489891598361)
                ·
                  refine ⟨6070314439037617418698771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8093752585383489891598361 6070314439037617418698771)
                  ·
                    refine ⟨9105471658556426128048157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6070314439037617418698771 9105471658556426128048157)
                    ·
                      refine ⟨3414551871958659798018059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105471658556426128048157 3414551871958659798018059)
                      ·
                        rfl

theorem cell23_6649816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_6649816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649816 prefixEnd_6649816 := by exact prefixLift 6649816
  have htrace : WordTrace (prefixWord ++ tailWord_6649816) baseStart_6649816 baseEnd_6649816 := by
    simpa [prefixWord, tailWord_6649816, baseEnd_6649816] using wordTrace_append hprefix tailTrace_6649816
  have hstable : (prefixWord ++ tailWord_6649816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649816).length < 2 ^ (prefixWord ++ tailWord_6649816).sum := by decide
  have hdescent : baseEnd_6649816 < baseStart_6649816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649820 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6649820 : Nat := 118140960795 + 6649820 * 2 ^ 59
def prefixEnd_6649820 : Nat := 4983230072969 + 3 ^ 40 * 6649820 * 2
def baseEnd_6649820 : Nat := 3414553925881277782368041

theorem tailTrace_6649820 : CollatzResearch.WordTrace tailWord_6649820 prefixEnd_6649820 3414553925881277782368041 := by
  unfold tailWord_6649820
  simp only [CollatzResearch.WordTrace]
  refine ⟨121269430384422656841753457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161692573845896875789004609 121269430384422656841753457)
  ·
    refine ⟨90952072788316992631315093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121269430384422656841753457 90952072788316992631315093)
    ·
      refine ⟨4263378411952359029592895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90952072788316992631315093 4263378411952359029592895)
      ·
        refine ⟨6395067617928538544389343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263378411952359029592895 6395067617928538544389343)
        ·
          refine ⟨9592601426892807816584015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395067617928538544389343 9592601426892807816584015)
          ·
            refine ⟨14388902140339211724876023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592601426892807816584015 14388902140339211724876023)
            ·
              refine ⟨21583353210508817587314035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14388902140339211724876023 21583353210508817587314035)
              ·
                refine ⟨32375029815763226380971053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21583353210508817587314035 32375029815763226380971053)
                ·
                  refine ⟨12140636180911209892864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32375029815763226380971053 12140636180911209892864145)
                  ·
                    refine ⟨9105477135683407419648109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12140636180911209892864145 9105477135683407419648109)
                    ·
                      refine ⟨3414553925881277782368041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105477135683407419648109 3414553925881277782368041)
                      ·
                        rfl

theorem cell23_6649820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6649820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649820 prefixEnd_6649820 := by exact prefixLift 6649820
  have htrace : WordTrace (prefixWord ++ tailWord_6649820) baseStart_6649820 baseEnd_6649820 := by
    simpa [prefixWord, tailWord_6649820, baseEnd_6649820] using wordTrace_append hprefix tailTrace_6649820
  have hstable : (prefixWord ++ tailWord_6649820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649820).length < 2 ^ (prefixWord ++ tailWord_6649820).sum := by decide
  have hdescent : baseEnd_6649820 < baseStart_6649820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649832 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6649832 : Nat := 118140960795 + 6649832 * 2 ^ 59
def prefixEnd_6649832 : Nat := 4983230072969 + 3 ^ 40 * 6649832 * 2
def baseEnd_6649832 : Nat := 1138186695883043911805995

theorem tailTrace_6649832 : CollatzResearch.WordTrace tailWord_6649832 prefixEnd_6649832 1138186695883043911805995 := by
  unfold tailWord_6649832
  simp only [CollatzResearch.WordTrace]
  refine ⟨121269649222400919866471875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161692865629867893155295833 121269649222400919866471875)
  ·
    refine ⟨181904473833601379799707813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121269649222400919866471875 181904473833601379799707813)
    ·
      refine ⟨34107088843800258712445215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181904473833601379799707813 34107088843800258712445215)
      ·
        refine ⟨51160633265700388068667823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34107088843800258712445215 51160633265700388068667823)
        ·
          refine ⟨76740949898550582103001735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51160633265700388068667823 76740949898550582103001735)
          ·
            refine ⟨115111424847825873154502603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76740949898550582103001735 115111424847825873154502603)
            ·
              refine ⟨172667137271738809731753905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115111424847825873154502603 172667137271738809731753905)
              ·
                refine ⟨129500352953804107298815429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172667137271738809731753905 129500352953804107298815429)
                ·
                  refine ⟨24281316178838270118527893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129500352953804107298815429 24281316178838270118527893)
                  ·
                    refine ⟨1138186695883043911805995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24281316178838270118527893 1138186695883043911805995)
                    ·
                      rfl

theorem cell23_6649832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6649832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649832 prefixEnd_6649832 := by exact prefixLift 6649832
  have htrace : WordTrace (prefixWord ++ tailWord_6649832) baseStart_6649832 baseEnd_6649832 := by
    simpa [prefixWord, tailWord_6649832, baseEnd_6649832] using wordTrace_append hprefix tailTrace_6649832
  have hstable : (prefixWord ++ tailWord_6649832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649832).length < 2 ^ (prefixWord ++ tailWord_6649832).sum := by decide
  have hdescent : baseEnd_6649832 < baseStart_6649832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649899 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 7, 2]
def baseStart_6649899 : Nat := 118140960795 + 6649899 * 2 ^ 59
def prefixEnd_6649899 : Nat := 4983230072969 + 3 ^ 40 * 6649899 * 2
def baseEnd_6649899 : Nat := 3414594490852982973280177

theorem tailTrace_6649899 : CollatzResearch.WordTrace tailWord_6649899 prefixEnd_6649899 3414594490852982973280177 := by
  unfold tailWord_6649899
  simp only [CollatzResearch.WordTrace]
  refine ⟨242541742135559110175632751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161694494757039406783755167 242541742135559110175632751)
  ·
    refine ⟨363812613203338665263449127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242541742135559110175632751 363812613203338665263449127)
    ·
      refine ⟨545718919805007997895173691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363812613203338665263449127 545718919805007997895173691)
      ·
        refine ⟨818578379707511996842760537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545718919805007997895173691 818578379707511996842760537)
        ·
          refine ⟨613933784780633997632070403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818578379707511996842760537 613933784780633997632070403)
          ·
            refine ⟨920900677170950996448105605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613933784780633997632070403 920900677170950996448105605)
            ·
              refine ⟨172668876969553311834019801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 920900677170950996448105605 172668876969553311834019801)
              ·
                refine ⟨129501657727164983875514851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172668876969553311834019801 129501657727164983875514851)
                ·
                  refine ⟨194252486590747475813272277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129501657727164983875514851 194252486590747475813272277)
                  ·
                    refine ⟨4552792654470643964373569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 194252486590747475813272277 4552792654470643964373569)
                    ·
                      refine ⟨3414594490852982973280177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552792654470643964373569 3414594490852982973280177)
                      ·
                        rfl

theorem cell23_6649899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7, 2].length) (baseStart_6649899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649899 prefixEnd_6649899 := by exact prefixLift 6649899
  have htrace : WordTrace (prefixWord ++ tailWord_6649899) baseStart_6649899 baseEnd_6649899 := by
    simpa [prefixWord, tailWord_6649899, baseEnd_6649899] using wordTrace_append hprefix tailTrace_6649899
  have hstable : (prefixWord ++ tailWord_6649899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649899).length < 2 ^ (prefixWord ++ tailWord_6649899).sum := by decide
  have hdescent : baseEnd_6649899 < baseStart_6649899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649909 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6649909 : Nat := 118140960795 + 6649909 * 2 ^ 59
def prefixEnd_6649909 : Nat := 4983230072969 + 3 ^ 40 * 6649909 * 2
def baseEnd_6649909 : Nat := 1138199875219842644718377

theorem tailTrace_6649909 : CollatzResearch.WordTrace tailWord_6649909 prefixEnd_6649909 1138199875219842644718377 := by
  unfold tailWord_6649909
  simp only [CollatzResearch.WordTrace]
  refine ⟨242542106865522881883496781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161694737910348587922331187 242542106865522881883496781)
  ·
    refine ⟨90953290074571080706311293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242542106865522881883496781 90953290074571080706311293)
    ·
      refine ⟨34107483777964155264866735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90953290074571080706311293 34107483777964155264866735)
      ·
        refine ⟨51161225666946232897300103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34107483777964155264866735 51161225666946232897300103)
        ·
          refine ⟨76741838500419349345950155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51161225666946232897300103 76741838500419349345950155)
          ·
            refine ⟨115112757750629024018925233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76741838500419349345950155 115112757750629024018925233)
            ·
              refine ⟨86334568312971768014193925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115112757750629024018925233 86334568312971768014193925)
              ·
                refine ⟨16187731558682206502661361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86334568312971768014193925 16187731558682206502661361)
                ·
                  refine ⟨12140798669011654876996021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16187731558682206502661361 12140798669011654876996021)
                  ·
                    refine ⟨1138199875219842644718377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12140798669011654876996021 1138199875219842644718377)
                    ·
                      rfl

theorem cell23_6649909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6649909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649909 prefixEnd_6649909 := by exact prefixLift 6649909
  have htrace : WordTrace (prefixWord ++ tailWord_6649909) baseStart_6649909 baseEnd_6649909 := by
    simpa [prefixWord, tailWord_6649909, baseEnd_6649909] using wordTrace_append hprefix tailTrace_6649909
  have hstable : (prefixWord ++ tailWord_6649909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649909).length < 2 ^ (prefixWord ++ tailWord_6649909).sum := by decide
  have hdescent : baseEnd_6649909 < baseStart_6649909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649926 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6649926 : Nat := 118140960795 + 6649926 * 2 ^ 59
def prefixEnd_6649926 : Nat := 4983230072969 + 3 ^ 40 * 6649926 * 2
def baseEnd_6649926 : Nat := 1138202784943551455880851

theorem tailTrace_6649926 : CollatzResearch.WordTrace tailWord_6649926 prefixEnd_6649926 1138202784943551455880851 := by
  unfold tailWord_6649926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579460215826915430839551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161695151270974195857910421 7579460215826915430839551)
  ·
    refine ⟨11369190323740373146259327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7579460215826915430839551 11369190323740373146259327)
    ·
      refine ⟨17053785485610559719388991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369190323740373146259327 17053785485610559719388991)
      ·
        refine ⟨25580678228415839579083487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17053785485610559719388991 25580678228415839579083487)
        ·
          refine ⟨38371017342623759368625231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25580678228415839579083487 38371017342623759368625231)
          ·
            refine ⟨57556526013935639052937847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38371017342623759368625231 57556526013935639052937847)
            ·
              refine ⟨86334789020903458579406771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57556526013935639052937847 86334789020903458579406771)
              ·
                refine ⟨129502183531355187869110157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86334789020903458579406771 129502183531355187869110157)
                ·
                  refine ⟨48563318824258195450916309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129502183531355187869110157 48563318824258195450916309)
                  ·
                    refine ⟨1138202784943551455880851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48563318824258195450916309 1138202784943551455880851)
                    ·
                      rfl

theorem cell23_6649926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6649926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649926 prefixEnd_6649926 := by exact prefixLift 6649926
  have htrace : WordTrace (prefixWord ++ tailWord_6649926) baseStart_6649926 baseEnd_6649926 := by
    simpa [prefixWord, tailWord_6649926, baseEnd_6649926] using wordTrace_append hprefix tailTrace_6649926
  have hstable : (prefixWord ++ tailWord_6649926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649926).length < 2 ^ (prefixWord ++ tailWord_6649926).sum := by decide
  have hdescent : baseEnd_6649926 < baseStart_6649926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649969 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 6]
def baseStart_6649969 : Nat := 118140960795 + 6649969 * 2 ^ 59
def prefixEnd_6649969 : Nat := 4983230072969 + 3 ^ 40 * 6649969 * 2
def baseEnd_6649969 : Nat := 379403381610977522156095

theorem tailTrace_6649969 : CollatzResearch.WordTrace tailWord_6649969 prefixEnd_6649969 379403381610977522156095 := by
  unfold tailWord_6649969
  simp only [CollatzResearch.WordTrace]
  refine ⟨242544295245305512130680961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161696196830203674753787307 242544295245305512130680961)
  ·
    refine ⟨181908221433979134098010721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242544295245305512130680961 181908221433979134098010721)
    ·
      refine ⟨136431166075484350573508041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181908221433979134098010721 136431166075484350573508041)
      ·
        refine ⟨102323374556613262930131031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136431166075484350573508041 102323374556613262930131031)
        ·
          refine ⟨153485061834919894395196547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102323374556613262930131031 153485061834919894395196547)
          ·
            refine ⟨230227592752379841592794821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153485061834919894395196547 230227592752379841592794821)
            ·
              refine ⟨43167673641071220298649029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230227592752379841592794821 43167673641071220298649029)
              ·
                refine ⟨8093938807700853805996693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43167673641071220298649029 8093938807700853805996693)
                ·
                  refine ⟨379403381610977522156095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093938807700853805996693 379403381610977522156095)
                  ·
                    rfl

theorem cell23_6649969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_6649969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6649969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6649969 prefixEnd_6649969 := by exact prefixLift 6649969
  have htrace : WordTrace (prefixWord ++ tailWord_6649969) baseStart_6649969 baseEnd_6649969 := by
    simpa [prefixWord, tailWord_6649969, baseEnd_6649969] using wordTrace_append hprefix tailTrace_6649969
  have hstable : (prefixWord ++ tailWord_6649969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649969).length < 2 ^ (prefixWord ++ tailWord_6649969).sum := by decide
  have hdescent : baseEnd_6649969 < baseStart_6649969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650050 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6650050 : Nat := 118140960795 + 6650050 * 2 ^ 59
def prefixEnd_6650050 : Nat := 4983230072969 + 3 ^ 40 * 6650050 * 2
def baseEnd_6650050 : Nat := 1138224008810603960830661

theorem tailTrace_6650050 : CollatzResearch.WordTrace tailWord_6650050 prefixEnd_6650050 1138224008810603960830661 := by
  unfold tailWord_6650050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60636812389503015741094901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161698166372008041976253069 60636812389503015741094901)
  ·
    refine ⟨5684701161515907725727647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60636812389503015741094901 5684701161515907725727647)
    ·
      refine ⟨8527051742273861588591471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684701161515907725727647 8527051742273861588591471)
      ·
        refine ⟨12790577613410792382887207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527051742273861588591471 12790577613410792382887207)
        ·
          refine ⟨19185866420116188574330811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790577613410792382887207 19185866420116188574330811)
          ·
            refine ⟨28778799630174282861496217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19185866420116188574330811 28778799630174282861496217)
            ·
              refine ⟨21584099722630712146122163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28778799630174282861496217 21584099722630712146122163)
              ·
                refine ⟨32376149583946068219183245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21584099722630712146122163 32376149583946068219183245)
                ·
                  refine ⟨12141056093979775582193717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32376149583946068219183245 12141056093979775582193717)
                  ·
                    refine ⟨1138224008810603960830661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12141056093979775582193717 1138224008810603960830661)
                    ·
                      rfl

theorem cell23_6650050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6650050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650050 prefixEnd_6650050 := by exact prefixLift 6650050
  have htrace : WordTrace (prefixWord ++ tailWord_6650050) baseStart_6650050 baseEnd_6650050 := by
    simpa [prefixWord, tailWord_6650050, baseEnd_6650050] using wordTrace_append hprefix tailTrace_6650050
  have hstable : (prefixWord ++ tailWord_6650050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650050).length < 2 ^ (prefixWord ++ tailWord_6650050).sum := by decide
  have hdescent : baseEnd_6650050 < baseStart_6650050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650053 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_6650053 : Nat := 118140960795 + 6650053 * 2 ^ 59
def prefixEnd_6650053 : Nat := 4983230072969 + 3 ^ 40 * 6650053 * 2
def baseEnd_6650053 : Nat := 3414673566873775370754469

theorem tailTrace_6650053 : CollatzResearch.WordTrace tailWord_6650053 prefixEnd_6650053 3414673566873775370754469 := by
  unfold tailWord_6650053
  simp only [CollatzResearch.WordTrace]
  refine ⟨242547358977001194476738813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161698239318000796317825875 242547358977001194476738813)
  ·
    refine ⟨90955259616375447928777055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242547358977001194476738813 90955259616375447928777055)
    ·
      refine ⟨136432889424563171893165583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90955259616375447928777055 136432889424563171893165583)
      ·
        refine ⟨204649334136844757839748375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136432889424563171893165583 204649334136844757839748375)
        ·
          refine ⟨306974001205267136759622563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204649334136844757839748375 306974001205267136759622563)
          ·
            refine ⟨460461001807900705139433845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306974001205267136759622563 460461001807900705139433845)
            ·
              refine ⟨43168218919490691106821923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460461001807900705139433845 43168218919490691106821923)
              ·
                refine ⟨64752328379236036660232885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43168218919490691106821923 64752328379236036660232885)
                ·
                  refine ⟨6070530785553378436896833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64752328379236036660232885 6070530785553378436896833)
                  ·
                    refine ⟨4552898089165033827672625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6070530785553378436896833 4552898089165033827672625)
                    ·
                      refine ⟨3414673566873775370754469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552898089165033827672625 3414673566873775370754469)
                      ·
                        rfl

theorem cell23_6650053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_6650053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650053 prefixEnd_6650053 := by exact prefixLift 6650053
  have htrace : WordTrace (prefixWord ++ tailWord_6650053) baseStart_6650053 baseEnd_6650053 := by
    simpa [prefixWord, tailWord_6650053, baseEnd_6650053] using wordTrace_append hprefix tailTrace_6650053
  have hstable : (prefixWord ++ tailWord_6650053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650053).length < 2 ^ (prefixWord ++ tailWord_6650053).sum := by decide
  have hdescent : baseEnd_6650053 < baseStart_6650053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650079 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_6650079 : Nat := 118140960795 + 6650079 * 2 ^ 59
def prefixEnd_6650079 : Nat := 4983230072969 + 3 ^ 40 * 6650079 * 2
def baseEnd_6650079 : Nat := 3414686917370792269029349

theorem tailTrace_6650079 : CollatzResearch.WordTrace tailWord_6650079 prefixEnd_6650079 3414686917370792269029349 := by
  unfold tailWord_6650079
  simp only [CollatzResearch.WordTrace]
  refine ⟨242548307274907000917185291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161698871516604667278123527 242548307274907000917185291)
  ·
    refine ⟨363822460912360501375777937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242548307274907000917185291 363822460912360501375777937)
    ·
      refine ⟨272866845684270376031833453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363822460912360501375777937 272866845684270376031833453)
      ·
        refine ⟨102325067131601391011937545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272866845684270376031833453 102325067131601391011937545)
        ·
          refine ⟨76743800348701043258953159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102325067131601391011937545 76743800348701043258953159)
          ·
            refine ⟨115115700523051564888429739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76743800348701043258953159 115115700523051564888429739)
            ·
              refine ⟨172673550784577347332644609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115115700523051564888429739 172673550784577347332644609)
              ·
                refine ⟨129505163088433010499483457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172673550784577347332644609 129505163088433010499483457)
                ·
                  refine ⟨97128872316324757874612593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129505163088433010499483457 97128872316324757874612593)
                  ·
                    refine ⟨72846654237243568405959445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97128872316324757874612593 72846654237243568405959445)
                    ·
                      refine ⟨3414686917370792269029349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72846654237243568405959445 3414686917370792269029349)
                      ·
                        rfl

theorem cell23_6650079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_6650079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650079 prefixEnd_6650079 := by exact prefixLift 6650079
  have htrace : WordTrace (prefixWord ++ tailWord_6650079) baseStart_6650079 baseEnd_6650079 := by
    simpa [prefixWord, tailWord_6650079, baseEnd_6650079] using wordTrace_append hprefix tailTrace_6650079
  have hstable : (prefixWord ++ tailWord_6650079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650079).length < 2 ^ (prefixWord ++ tailWord_6650079).sum := by decide
  have hdescent : baseEnd_6650079 < baseStart_6650079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650087 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6650087 : Nat := 118140960795 + 6650087 * 2 ^ 59
def prefixEnd_6650087 : Nat := 4983230072969 + 3 ^ 40 * 6650087 * 2
def baseEnd_6650087 : Nat := 3414691025216028237729313

theorem tailTrace_6650087 : CollatzResearch.WordTrace tailWord_6650087 prefixEnd_6650087 3414691025216028237729313 := by
  unfold tailWord_6650087
  simp only [CollatzResearch.WordTrace]
  refine ⟨242548599058878018283476515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161699066039252012188984343 242548599058878018283476515)
  ·
    refine ⟨363822898588317027425214773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242548599058878018283476515 363822898588317027425214773)
    ·
      refine ⟨34108396742654721321113885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363822898588317027425214773 34108396742654721321113885)
      ·
        refine ⟨12790648778495520495417707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34108396742654721321113885 12790648778495520495417707)
        ·
          refine ⟨19185973167743280743126561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790648778495520495417707 19185973167743280743126561)
          ·
            refine ⟨14389479875807460557344921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19185973167743280743126561 14389479875807460557344921)
            ·
              refine ⟨10792109906855595418008691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14389479875807460557344921 10792109906855595418008691)
              ·
                refine ⟨16188164860283393127013037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792109906855595418008691 16188164860283393127013037)
                ·
                  refine ⟨6070561822606272422629889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16188164860283393127013037 6070561822606272422629889)
                  ·
                    refine ⟨4552921366954704316972417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6070561822606272422629889 4552921366954704316972417)
                    ·
                      refine ⟨3414691025216028237729313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552921366954704316972417 3414691025216028237729313)
                      ·
                        rfl

theorem cell23_6650087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6650087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650087 prefixEnd_6650087 := by exact prefixLift 6650087
  have htrace : WordTrace (prefixWord ++ tailWord_6650087) baseStart_6650087 baseEnd_6650087 := by
    simpa [prefixWord, tailWord_6650087, baseEnd_6650087] using wordTrace_append hprefix tailTrace_6650087
  have hstable : (prefixWord ++ tailWord_6650087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650087).length < 2 ^ (prefixWord ++ tailWord_6650087).sum := by decide
  have hdescent : baseEnd_6650087 < baseStart_6650087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650156 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_6650156 : Nat := 118140960795 + 6650156 * 2 ^ 59
def prefixEnd_6650156 : Nat := 4983230072969 + 3 ^ 40 * 6650156 * 2
def baseEnd_6650156 : Nat := 3414726455381188467766495

theorem tailTrace_6650156 : CollatzResearch.WordTrace tailWord_6650156 prefixEnd_6650156 3414726455381188467766495 := by
  unfold tailWord_6650156
  simp only [CollatzResearch.WordTrace]
  refine ⟨121275557847814021533869161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161700743797085362045158881 121275557847814021533869161)
  ·
    refine ⟨90956668385860516150401871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121275557847814021533869161 90956668385860516150401871)
    ·
      refine ⟨136435002578790774225602807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90956668385860516150401871 136435002578790774225602807)
      ·
        refine ⟨204652503868186161338404211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136435002578790774225602807 204652503868186161338404211)
        ·
          refine ⟨306978755802279242007606317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204652503868186161338404211 306978755802279242007606317)
          ·
            refine ⟨115117033425854715752852369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306978755802279242007606317 115117033425854715752852369)
            ·
              refine ⟨86337775069391036814639277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115117033425854715752852369 86337775069391036814639277)
              ·
                refine ⟨32376665651021638805489729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86337775069391036814639277 32376665651021638805489729)
                ·
                  refine ⟨24282499238266229104117297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32376665651021638805489729 24282499238266229104117297)
                  ·
                    refine ⟨18211874428699671828087973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24282499238266229104117297 18211874428699671828087973)
                    ·
                      refine ⟨3414726455381188467766495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18211874428699671828087973 3414726455381188467766495)
                      ·
                        rfl

theorem cell23_6650156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_6650156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650156 prefixEnd_6650156 := by exact prefixLift 6650156
  have htrace : WordTrace (prefixWord ++ tailWord_6650156) baseStart_6650156 baseEnd_6650156 := by
    simpa [prefixWord, tailWord_6650156, baseEnd_6650156] using wordTrace_append hprefix tailTrace_6650156
  have hstable : (prefixWord ++ tailWord_6650156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650156).length < 2 ^ (prefixWord ++ tailWord_6650156).sum := by decide
  have hdescent : baseEnd_6650156 < baseStart_6650156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650164 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6650164 : Nat := 118140960795 + 6650164 * 2 ^ 59
def prefixEnd_6650164 : Nat := 4983230072969 + 3 ^ 40 * 6650164 * 2
def baseEnd_6650164 : Nat := 3414730563226424436466459

theorem tailTrace_6650164 : CollatzResearch.WordTrace tailWord_6650164 prefixEnd_6650164 3414730563226424436466459 := by
  unfold tailWord_6650164
  simp only [CollatzResearch.WordTrace]
  refine ⟨121275703739799530217014773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161700938319732706956019697 121275703739799530217014773)
  ·
    refine ⟨11369597225606205957845135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121275703739799530217014773 11369597225606205957845135)
    ·
      refine ⟨17054395838409308936767703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369597225606205957845135 17054395838409308936767703)
      ·
        refine ⟨25581593757613963405151555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17054395838409308936767703 25581593757613963405151555)
        ·
          refine ⟨38372390636420945107727333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25581593757613963405151555 38372390636420945107727333)
          ·
            refine ⟨7194823244328927207698875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38372390636420945107727333 7194823244328927207698875)
            ·
              refine ⟨10792234866493390811548313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7194823244328927207698875 10792234866493390811548313)
              ·
                refine ⟨8094176149870043108661235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10792234866493390811548313 8094176149870043108661235)
                ·
                  refine ⟨12141264224805064662991853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8094176149870043108661235 12141264224805064662991853)
                  ·
                    refine ⟨4552974084301899248621945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12141264224805064662991853 4552974084301899248621945)
                    ·
                      refine ⟨3414730563226424436466459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552974084301899248621945 3414730563226424436466459)
                      ·
                        rfl

theorem cell23_6650164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6650164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650164 prefixEnd_6650164 := by exact prefixLift 6650164
  have htrace : WordTrace (prefixWord ++ tailWord_6650164) baseStart_6650164 baseEnd_6650164 := by
    simpa [prefixWord, tailWord_6650164, baseEnd_6650164] using wordTrace_append hprefix tailTrace_6650164
  have hstable : (prefixWord ++ tailWord_6650164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650164).length < 2 ^ (prefixWord ++ tailWord_6650164).sum := by decide
  have hdescent : baseEnd_6650164 < baseStart_6650164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650176 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_6650176 : Nat := 118140960795 + 6650176 * 2 ^ 59
def prefixEnd_6650176 : Nat := 4983230072969 + 3 ^ 40 * 6650176 * 2
def baseEnd_6650176 : Nat := 3414736724994278389516403

theorem tailTrace_6650176 : CollatzResearch.WordTrace tailWord_6650176 prefixEnd_6650176 3414736724994278389516403 := by
  unfold tailWord_6650176
  simp only [CollatzResearch.WordTrace]
  refine ⟨121275922577777793241733191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161701230103703724322310921 121275922577777793241733191)
  ·
    refine ⟨181913883866666689862599787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121275922577777793241733191 181913883866666689862599787)
    ·
      refine ⟨272870825800000034793899681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181913883866666689862599787 272870825800000034793899681)
      ·
        refine ⟨204653119350000026095424761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272870825800000034793899681 204653119350000026095424761)
        ·
          refine ⟨153489839512500019571568571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204653119350000026095424761 153489839512500019571568571)
          ·
            refine ⟨230234759268750029357352857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153489839512500019571568571 230234759268750029357352857)
            ·
              refine ⟨172676069451562522018014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230234759268750029357352857 172676069451562522018014643)
              ·
                refine ⟨259014104177343783027021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172676069451562522018014643 259014104177343783027021965)
                ·
                  refine ⟨97130289066503918635133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259014104177343783027021965 97130289066503918635133237)
                  ·
                    refine ⟨9105964599984742372043741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97130289066503918635133237 9105964599984742372043741)
                    ·
                      refine ⟨3414736724994278389516403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105964599984742372043741 3414736724994278389516403)
                      ·
                        rfl

theorem cell23_6650176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_6650176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650176 prefixEnd_6650176 := by exact prefixLift 6650176
  have htrace : WordTrace (prefixWord ++ tailWord_6650176) baseStart_6650176 baseEnd_6650176 := by
    simpa [prefixWord, tailWord_6650176, baseEnd_6650176] using wordTrace_append hprefix tailTrace_6650176
  have hstable : (prefixWord ++ tailWord_6650176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650176).length < 2 ^ (prefixWord ++ tailWord_6650176).sum := by decide
  have hdescent : baseEnd_6650176 < baseStart_6650176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650177 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6650177 : Nat := 118140960795 + 6650177 * 2 ^ 59
def prefixEnd_6650177 : Nat := 4983230072969 + 3 ^ 40 * 6650177 * 2
def baseEnd_6650177 : Nat := 3414737238474932885603899

theorem tailTrace_6650177 : CollatzResearch.WordTrace tailWord_6650177 prefixEnd_6650177 3414737238474932885603899 := by
  unfold tailWord_6650177
  simp only [CollatzResearch.WordTrace]
  refine ⟨242551881628551963654252785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161701254419034642436168523 242551881628551963654252785)
  ·
    refine ⟨181913911221413972740689589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242551881628551963654252785 181913911221413972740689589)
    ·
      refine ⟨17054429177007559944439649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181913911221413972740689589 17054429177007559944439649)
      ·
        refine ⟨12790821882755669958329737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17054429177007559944439649 12790821882755669958329737)
        ·
          refine ⟨9593116412066752468747303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790821882755669958329737 9593116412066752468747303)
          ·
            refine ⟨14389674618100128703120955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593116412066752468747303 14389674618100128703120955)
            ·
              refine ⟨21584511927150193054681433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389674618100128703120955 21584511927150193054681433)
              ·
                refine ⟨16188383945362644791011075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21584511927150193054681433 16188383945362644791011075)
                ·
                  refine ⟨24282575918043967186516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16188383945362644791011075 24282575918043967186516613)
                  ·
                    refine ⟨4552982984633243847471865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24282575918043967186516613 4552982984633243847471865)
                    ·
                      refine ⟨3414737238474932885603899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4552982984633243847471865 3414737238474932885603899)
                      ·
                        rfl

theorem cell23_6650177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6650177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650177 prefixEnd_6650177 := by exact prefixLift 6650177
  have htrace : WordTrace (prefixWord ++ tailWord_6650177) baseStart_6650177 baseEnd_6650177 := by
    simpa [prefixWord, tailWord_6650177, baseEnd_6650177] using wordTrace_append hprefix tailTrace_6650177
  have hstable : (prefixWord ++ tailWord_6650177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650177).length < 2 ^ (prefixWord ++ tailWord_6650177).sum := by decide
  have hdescent : baseEnd_6650177 < baseStart_6650177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650183 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 5]
def baseStart_6650183 : Nat := 118140960795 + 6650183 * 2 ^ 59
def prefixEnd_6650183 : Nat := 4983230072969 + 3 ^ 40 * 6650183 * 2
def baseEnd_6650183 : Nat := 379415591039873318014319

theorem tailTrace_6650183 : CollatzResearch.WordTrace tailWord_6650183 prefixEnd_6650183 379415591039873318014319 := by
  unfold tailWord_6650183
  simp only [CollatzResearch.WordTrace]
  refine ⟨242552100466530226678971203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161701400311020151119314135 242552100466530226678971203)
  ·
    refine ⟨363828150699795340018456805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242552100466530226678971203 363828150699795340018456805)
    ·
      refine ⟨68217778256211626253460651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363828150699795340018456805 68217778256211626253460651)
      ·
        refine ⟨102326667384317439380190977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68217778256211626253460651 102326667384317439380190977)
        ·
          refine ⟨76745000538238079535143233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102326667384317439380190977 76745000538238079535143233)
          ·
            refine ⟨57558750403678559651357425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76745000538238079535143233 57558750403678559651357425)
            ·
              refine ⟨43169062802758919738518069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57558750403678559651357425 43169062802758919738518069)
              ·
                refine ⟨4047099637758648725486069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43169062802758919738518069 4047099637758648725486069)
                ·
                  refine ⟨379415591039873318014319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047099637758648725486069 379415591039873318014319)
                  ·
                    rfl

theorem cell23_6650183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 5].length) (baseStart_6650183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650183 prefixEnd_6650183 := by exact prefixLift 6650183
  have htrace : WordTrace (prefixWord ++ tailWord_6650183) baseStart_6650183 baseEnd_6650183 := by
    simpa [prefixWord, tailWord_6650183, baseEnd_6650183] using wordTrace_append hprefix tailTrace_6650183
  have hstable : (prefixWord ++ tailWord_6650183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650183).length < 2 ^ (prefixWord ++ tailWord_6650183).sum := by decide
  have hdescent : baseEnd_6650183 < baseStart_6650183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650210 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6650210 : Nat := 118140960795 + 6650210 * 2 ^ 59
def prefixEnd_6650210 : Nat := 4983230072969 + 3 ^ 40 * 6650210 * 2
def baseEnd_6650210 : Nat := 3414754183336531256491247

theorem tailTrace_6650210 : CollatzResearch.WordTrace tailWord_6650210 prefixEnd_6650210 3414754183336531256491247 := by
  unfold tailWord_6650210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60638271309358102572551021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161702056824954940193469389 60638271309358102572551021)
  ·
    refine ⟨22739351741009288464706633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60638271309358102572551021 22739351741009288464706633)
    ·
      refine ⟨17054513805756966348529975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22739351741009288464706633 17054513805756966348529975)
      ·
        refine ⟨25581770708635449522794963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17054513805756966348529975 25581770708635449522794963)
        ·
          refine ⟨38372656062953174284192445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25581770708635449522794963 38372656062953174284192445)
          ·
            refine ⟨14389746023607440356572167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38372656062953174284192445 14389746023607440356572167)
            ·
              refine ⟨21584619035411160534858251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389746023607440356572167 21584619035411160534858251)
              ·
                refine ⟨32376928553116740802287377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21584619035411160534858251 32376928553116740802287377)
                ·
                  refine ⟨24282696414837555601715533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32376928553116740802287377 24282696414837555601715533)
                  ·
                    refine ⟨9106011155564083350643325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24282696414837555601715533 9106011155564083350643325)
                    ·
                      refine ⟨3414754183336531256491247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106011155564083350643325 3414754183336531256491247)
                      ·
                        rfl

theorem cell23_6650210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6650210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650210 prefixEnd_6650210 := by exact prefixLift 6650210
  have htrace : WordTrace (prefixWord ++ tailWord_6650210) baseStart_6650210 baseEnd_6650210 := by
    simpa [prefixWord, tailWord_6650210, baseEnd_6650210] using wordTrace_append hprefix tailTrace_6650210
  have hstable : (prefixWord ++ tailWord_6650210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650210).length < 2 ^ (prefixWord ++ tailWord_6650210).sum := by decide
  have hdescent : baseEnd_6650210 < baseStart_6650210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650233 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 6, 2]
def baseStart_6650233 : Nat := 118140960795 + 6650233 * 2 ^ 59
def prefixEnd_6650233 : Nat := 4983230072969 + 3 ^ 40 * 6650233 * 2
def baseEnd_6650233 : Nat := 3414765993391584666503641

theorem tailTrace_6650233 : CollatzResearch.WordTrace tailWord_6650233 prefixEnd_6650233 3414765993391584666503641 := by
  unfold tailWord_6650233
  simp only [CollatzResearch.WordTrace]
  refine ⟨242553924116349085218291353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161702616077566056812194235 242553924116349085218291353)
  ·
    refine ⟨181915443087261813913718515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242553924116349085218291353 181915443087261813913718515)
    ·
      refine ⟨272873164630892720870577773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181915443087261813913718515 272873164630892720870577773)
      ·
        refine ⟨102327436736584770326466665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272873164630892720870577773 102327436736584770326466665)
        ·
          refine ⟨76745577552438577744849999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102327436736584770326466665 76745577552438577744849999)
          ·
            refine ⟨115118366328657866617274999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76745577552438577744849999 115118366328657866617274999)
            ·
              refine ⟨172677549492986799925912499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115118366328657866617274999 172677549492986799925912499)
              ·
                refine ⟨259016324239480199888868749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172677549492986799925912499 259016324239480199888868749)
                ·
                  refine ⟨97131121589805074958325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259016324239480199888868749 97131121589805074958325781)
                  ·
                    refine ⟨4553021324522112888671521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97131121589805074958325781 4553021324522112888671521)
                    ·
                      refine ⟨3414765993391584666503641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553021324522112888671521 3414765993391584666503641)
                      ·
                        rfl

theorem cell23_6650233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_6650233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650233 prefixEnd_6650233 := by exact prefixLift 6650233
  have htrace : WordTrace (prefixWord ++ tailWord_6650233) baseStart_6650233 baseEnd_6650233 := by
    simpa [prefixWord, tailWord_6650233, baseEnd_6650233] using wordTrace_append hprefix tailTrace_6650233
  have hstable : (prefixWord ++ tailWord_6650233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650233).length < 2 ^ (prefixWord ++ tailWord_6650233).sum := by decide
  have hdescent : baseEnd_6650233 < baseStart_6650233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650236 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_6650236 : Nat := 118140960795 + 6650236 * 2 ^ 59
def prefixEnd_6650236 : Nat := 4983230072969 + 3 ^ 40 * 6650236 * 2
def baseEnd_6650236 : Nat := 3414767533833548154766127

theorem tailTrace_6650236 : CollatzResearch.WordTrace tailWord_6650236 prefixEnd_6650236 3414767533833548154766127 := by
  unfold tailWord_6650236
  simp only [CollatzResearch.WordTrace]
  refine ⟨121277016767669108365325281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161702689023558811153767041 121277016767669108365325281)
  ·
    refine ⟨90957762575751831273993961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121277016767669108365325281 90957762575751831273993961)
    ·
      refine ⟨68218321931813873455495471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90957762575751831273993961 68218321931813873455495471)
      ·
        refine ⟨102327482897720810183243207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68218321931813873455495471 102327482897720810183243207)
        ·
          refine ⟨153491224346581215274864811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102327482897720810183243207 153491224346581215274864811)
          ·
            refine ⟨230236836519871822912297217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153491224346581215274864811 230236836519871822912297217)
            ·
              refine ⟨172677627389903867184222913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230236836519871822912297217 172677627389903867184222913)
              ·
                refine ⟨129508220542427900388167185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172677627389903867184222913 129508220542427900388167185)
                ·
                  refine ⟨97131165406820925291125389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129508220542427900388167185 97131165406820925291125389)
                  ·
                    refine ⟨36424187027557846984172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97131165406820925291125389 36424187027557846984172021)
                    ·
                      refine ⟨3414767533833548154766127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36424187027557846984172021 3414767533833548154766127)
                      ·
                        rfl

theorem cell23_6650236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_6650236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650236 prefixEnd_6650236 := by exact prefixLift 6650236
  have htrace : WordTrace (prefixWord ++ tailWord_6650236) baseStart_6650236 baseEnd_6650236 := by
    simpa [prefixWord, tailWord_6650236, baseEnd_6650236] using wordTrace_append hprefix tailTrace_6650236
  have hstable : (prefixWord ++ tailWord_6650236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650236).length < 2 ^ (prefixWord ++ tailWord_6650236).sum := by decide
  have hdescent : baseEnd_6650236 < baseStart_6650236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650350 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6650350 : Nat := 118140960795 + 6650350 * 2 ^ 59
def prefixEnd_6650350 : Nat := 4983230072969 + 3 ^ 40 * 6650350 * 2
def baseEnd_6650350 : Nat := 1138275356876053569580201

theorem tailTrace_6650350 : CollatzResearch.WordTrace tailWord_6650350 prefixEnd_6650350 1138275356876053569580201 := by
  unfold tailWord_6650350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30319773932115651775037563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161705460971283476133533669 30319773932115651775037563)
  ·
    refine ⟨45479660898173477662556345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30319773932115651775037563 45479660898173477662556345)
    ·
      refine ⟨34109745673630108246917259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45479660898173477662556345 34109745673630108246917259)
      ·
        refine ⟨51164618510445162370375889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34109745673630108246917259 51164618510445162370375889)
        ·
          refine ⟨38373463882833871777781917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51164618510445162370375889 38373463882833871777781917)
          ·
            refine ⟨14390048956062701916668219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38373463882833871777781917 14390048956062701916668219)
            ·
              refine ⟨21585073434094052875002329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390048956062701916668219 21585073434094052875002329)
              ·
                refine ⟨16188805075570539656251747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21585073434094052875002329 16188805075570539656251747)
                ·
                  refine ⟨24283207613355809484377621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16188805075570539656251747 24283207613355809484377621)
                  ·
                    refine ⟨1138275356876053569580201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24283207613355809484377621 1138275356876053569580201)
                    ·
                      rfl

theorem cell23_6650350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6650350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650350 prefixEnd_6650350 := by exact prefixLift 6650350
  have htrace : WordTrace (prefixWord ++ tailWord_6650350) baseStart_6650350 baseEnd_6650350 := by
    simpa [prefixWord, tailWord_6650350, baseEnd_6650350] using wordTrace_append hprefix tailTrace_6650350
  have hstable : (prefixWord ++ tailWord_6650350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650350).length < 2 ^ (prefixWord ++ tailWord_6650350).sum := by decide
  have hdescent : baseEnd_6650350 < baseStart_6650350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650354 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_6650354 : Nat := 118140960795 + 6650354 * 2 ^ 59
def prefixEnd_6650354 : Nat := 4983230072969 + 3 ^ 40 * 6650354 * 2
def baseEnd_6650354 : Nat := 1138276041516926231030195

theorem tailTrace_6650354 : CollatzResearch.WordTrace tailWord_6650354 prefixEnd_6650354 1138276041516926231030195 := by
  unfold tailWord_6650354
  simp only [CollatzResearch.WordTrace]
  refine ⟨60639584337227680720861529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161705558232607148588964077 60639584337227680720861529)
  ·
    refine ⟨45479688252920760540646147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60639584337227680720861529 45479688252920760540646147)
    ·
      refine ⟨68219532379381140810969221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45479688252920760540646147 68219532379381140810969221)
      ·
        refine ⟨12791162321133963902056729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68219532379381140810969221 12791162321133963902056729)
        ·
          refine ⟨9593371740850472926542547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12791162321133963902056729 9593371740850472926542547)
          ·
            refine ⟨14390057611275709389813821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593371740850472926542547 14390057611275709389813821)
            ·
              refine ⟨5396271604228391021180183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14390057611275709389813821 5396271604228391021180183)
              ·
                refine ⟨8094407406342586531770275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396271604228391021180183 8094407406342586531770275)
                ·
                  refine ⟨12141611109513879797655413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8094407406342586531770275 12141611109513879797655413)
                  ·
                    refine ⟨1138276041516926231030195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12141611109513879797655413 1138276041516926231030195)
                    ·
                      rfl

theorem cell23_6650354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_6650354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650354 prefixEnd_6650354 := by exact prefixLift 6650354
  have htrace : WordTrace (prefixWord ++ tailWord_6650354) baseStart_6650354 baseEnd_6650354 := by
    simpa [prefixWord, tailWord_6650354, baseEnd_6650354] using wordTrace_append hprefix tailTrace_6650354
  have hstable : (prefixWord ++ tailWord_6650354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650354).length < 2 ^ (prefixWord ++ tailWord_6650354).sum := by decide
  have hdescent : baseEnd_6650354 < baseStart_6650354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650380 : List Nat := [2, 2, 1, 2, 4, 3, 1, 8]
def baseStart_6650380 : Nat := 118140960795 + 6650380 * 2 ^ 59
def prefixEnd_6650380 : Nat := 4983230072969 + 3 ^ 40 * 6650380 * 2
def baseEnd_6650380 : Nat := 126475610186955392272795

theorem tailTrace_6650380 : CollatzResearch.WordTrace tailWord_6650380 prefixEnd_6650380 126475610186955392272795 := by
  unfold tailWord_6650380
  simp only [CollatzResearch.WordTrace]
  refine ⟨121279642823408264661946297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161706190431211019549261729 121279642823408264661946297)
  ·
    refine ⟨90959732117556198496459723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121279642823408264661946297 90959732117556198496459723)
    ·
      refine ⟨136439598176334297744689585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90959732117556198496459723 136439598176334297744689585)
      ·
        refine ⟨102329698632250723308517189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136439598176334297744689585 102329698632250723308517189)
        ·
          refine ⟨19186818493547010620346973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102329698632250723308517189 19186818493547010620346973)
          ·
            refine ⟨7195056935080128982630115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19186818493547010620346973 7195056935080128982630115)
            ·
              refine ⟨10792585402620193473945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195056935080128982630115 10792585402620193473945173)
              ·
                refine ⟨126475610186955392272795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10792585402620193473945173 126475610186955392272795)
                ·
                  rfl

theorem cell23_6650380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 8].length) (baseStart_6650380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650380 prefixEnd_6650380 := by exact prefixLift 6650380
  have htrace : WordTrace (prefixWord ++ tailWord_6650380) baseStart_6650380 baseEnd_6650380 := by
    simpa [prefixWord, tailWord_6650380, baseEnd_6650380] using wordTrace_append hprefix tailTrace_6650380
  have hstable : (prefixWord ++ tailWord_6650380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650380).length < 2 ^ (prefixWord ++ tailWord_6650380).sum := by decide
  have hdescent : baseEnd_6650380 < baseStart_6650380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650391 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6650391 : Nat := 118140960795 + 6650391 * 2 ^ 59
def prefixEnd_6650391 : Nat := 4983230072969 + 3 ^ 40 * 6650391 * 2
def baseEnd_6650391 : Nat := 3414847123334995048327915

theorem tailTrace_6650391 : CollatzResearch.WordTrace tailWord_6650391 prefixEnd_6650391 3414847123334995048327915 := by
  unfold tailWord_6650391
  simp only [CollatzResearch.WordTrace]
  refine ⟨242559686849776678202543027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161706457899851118801695351 242559686849776678202543027)
  ·
    refine ⟨363839530274665017303814541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242559686849776678202543027 363839530274665017303814541)
    ·
      refine ⟨136439823852999381488930453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363839530274665017303814541 136439823852999381488930453)
      ·
        refine ⟨6395616743109346007293615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136439823852999381488930453 6395616743109346007293615)
        ·
          refine ⟨9593425114664019010940423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395616743109346007293615 9593425114664019010940423)
          ·
            refine ⟨14390137671996028516410635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593425114664019010940423 14390137671996028516410635)
            ·
              refine ⟨21585206507994042774615953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390137671996028516410635 21585206507994042774615953)
              ·
                refine ⟨16188904880995532080961965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21585206507994042774615953 16188904880995532080961965)
                ·
                  refine ⟨6070839330373324530360737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16188904880995532080961965 6070839330373324530360737)
                  ·
                    refine ⟨4553129497779993397770553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6070839330373324530360737 4553129497779993397770553)
                    ·
                      refine ⟨3414847123334995048327915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553129497779993397770553 3414847123334995048327915)
                      ·
                        rfl

theorem cell23_6650391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6650391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650391 prefixEnd_6650391 := by exact prefixLift 6650391
  have htrace : WordTrace (prefixWord ++ tailWord_6650391) baseStart_6650391 baseEnd_6650391 := by
    simpa [prefixWord, tailWord_6650391, baseEnd_6650391] using wordTrace_append hprefix tailTrace_6650391
  have hstable : (prefixWord ++ tailWord_6650391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650391).length < 2 ^ (prefixWord ++ tailWord_6650391).sum := by decide
  have hdescent : baseEnd_6650391 < baseStart_6650391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650408 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6650408 : Nat := 118140960795 + 6650408 * 2 ^ 59
def prefixEnd_6650408 : Nat := 4983230072969 + 3 ^ 40 * 6650408 * 2
def baseEnd_6650408 : Nat := 3414855852506121481815337

theorem tailTrace_6650408 : CollatzResearch.WordTrace tailWord_6650408 prefixEnd_6650408 3414855852506121481815337 := by
  unfold tailWord_6650408
  simp only [CollatzResearch.WordTrace]
  refine ⟨121280153445357545052955939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161706871260476726737274585 121280153445357545052955939)
  ·
    refine ⟨181920230168036317579433909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121280153445357545052955939 181920230168036317579433909)
    ·
      refine ⟨17055021578253404773071929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181920230168036317579433909 17055021578253404773071929)
      ·
        refine ⟨12791266183690053579803947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17055021578253404773071929 12791266183690053579803947)
        ·
          refine ⟨19186899275535080369705921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791266183690053579803947 19186899275535080369705921)
          ·
            refine ⟨14390174456651310277279441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19186899275535080369705921 14390174456651310277279441)
            ·
              refine ⟨10792630842488482707959581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14390174456651310277279441 10792630842488482707959581)
              ·
                refine ⟨4047236565933181015484843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10792630842488482707959581 4047236565933181015484843)
                ·
                  refine ⟨6070854848899771523227265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047236565933181015484843 6070854848899771523227265)
                  ·
                    refine ⟨4553141136674828642420449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6070854848899771523227265 4553141136674828642420449)
                    ·
                      refine ⟨3414855852506121481815337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553141136674828642420449 3414855852506121481815337)
                      ·
                        rfl

theorem cell23_6650408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6650408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650408 prefixEnd_6650408 := by exact prefixLift 6650408
  have htrace : WordTrace (prefixWord ++ tailWord_6650408) baseStart_6650408 baseEnd_6650408 := by
    simpa [prefixWord, tailWord_6650408, baseEnd_6650408] using wordTrace_append hprefix tailTrace_6650408
  have hstable : (prefixWord ++ tailWord_6650408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650408).length < 2 ^ (prefixWord ++ tailWord_6650408).sum := by decide
  have hdescent : baseEnd_6650408 < baseStart_6650408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650423 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 6]
def baseStart_6650423 : Nat := 118140960795 + 6650423 * 2 ^ 59
def prefixEnd_6650423 : Nat := 4983230072969 + 3 ^ 40 * 6650423 * 2
def baseEnd_6650423 : Nat := 1138287851571979641042589

theorem tailTrace_6650423 : CollatzResearch.WordTrace tailWord_6650423 prefixEnd_6650423 1138287851571979641042589 := by
  unfold tailWord_6650423
  simp only [CollatzResearch.WordTrace]
  refine ⟨242560853985660747667707923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161707235990440498445138615 242560853985660747667707923)
  ·
    refine ⟨363841280978491121501561885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242560853985660747667707923 363841280978491121501561885)
    ·
      refine ⟨136440480366934170563085707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363841280978491121501561885 136440480366934170563085707)
      ·
        refine ⟨204660720550401255844628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136440480366934170563085707 204660720550401255844628561)
        ·
          refine ⟨153495540412800941883471421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204660720550401255844628561 153495540412800941883471421)
          ·
            refine ⟨57560827654800353206301783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153495540412800941883471421 57560827654800353206301783)
            ·
              refine ⟨86341241482200529809452675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57560827654800353206301783 86341241482200529809452675)
              ·
                refine ⟨129511862223300794714179013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86341241482200529809452675 129511862223300794714179013)
                ·
                  refine ⟨24283474166868899008908565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129511862223300794714179013 24283474166868899008908565)
                  ·
                    refine ⟨1138287851571979641042589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24283474166868899008908565 1138287851571979641042589)
                    ·
                      rfl

theorem cell23_6650423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_6650423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650423 prefixEnd_6650423 := by exact prefixLift 6650423
  have htrace : WordTrace (prefixWord ++ tailWord_6650423) baseStart_6650423 baseEnd_6650423 := by
    simpa [prefixWord, tailWord_6650423, baseEnd_6650423] using wordTrace_append hprefix tailTrace_6650423
  have hstable : (prefixWord ++ tailWord_6650423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650423).length < 2 ^ (prefixWord ++ tailWord_6650423).sum := by decide
  have hdescent : baseEnd_6650423 < baseStart_6650423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650447 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 4, 2]
def baseStart_6650447 : Nat := 118140960795 + 6650447 * 2 ^ 59
def prefixEnd_6650447 : Nat := 4983230072969 + 3 ^ 40 * 6650447 * 2
def baseEnd_6650447 : Nat := 3414875878251646829227657

theorem tailTrace_6650447 : CollatzResearch.WordTrace tailWord_6650447 prefixEnd_6650447 3414875878251646829227657 := by
  unfold tailWord_6650447
  simp only [CollatzResearch.WordTrace]
  refine ⟨242561729337573799766581595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161707819558382533177721063 242561729337573799766581595)
  ·
    refine ⟨363842594006360699649872393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242561729337573799766581595 363842594006360699649872393)
    ·
      refine ⟨272881945504770524737404295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363842594006360699649872393 272881945504770524737404295)
      ·
        refine ⟨409322918257155787106106443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272881945504770524737404295 409322918257155787106106443)
        ·
          refine ⟨613984377385733680659159665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409322918257155787106106443 613984377385733680659159665)
          ·
            refine ⟨460488283039300260494369749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613984377385733680659159665 460488283039300260494369749)
            ·
              refine ⟨10792694133733599855336791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460488283039300260494369749 10792694133733599855336791)
              ·
                refine ⟨16189041200600399783005187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792694133733599855336791 16189041200600399783005187)
                ·
                  refine ⟨24283561800900599674507781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16189041200600399783005187 24283561800900599674507781)
                  ·
                    refine ⟨4553167837668862438970209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24283561800900599674507781 4553167837668862438970209)
                    ·
                      refine ⟨3414875878251646829227657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553167837668862438970209 3414875878251646829227657)
                      ·
                        rfl

theorem cell23_6650447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4, 2].length) (baseStart_6650447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650447 prefixEnd_6650447 := by exact prefixLift 6650447
  have htrace : WordTrace (prefixWord ++ tailWord_6650447) baseStart_6650447 baseEnd_6650447 := by
    simpa [prefixWord, tailWord_6650447, baseEnd_6650447] using wordTrace_append hprefix tailTrace_6650447
  have hstable : (prefixWord ++ tailWord_6650447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650447).length < 2 ^ (prefixWord ++ tailWord_6650447).sum := by decide
  have hdescent : baseEnd_6650447 < baseStart_6650447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650450 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6650450 : Nat := 118140960795 + 6650450 * 2 ^ 59
def prefixEnd_6650450 : Nat := 4983230072969 + 3 ^ 40 * 6650450 * 2
def baseEnd_6650450 : Nat := 3414877418693610317490143

theorem tailTrace_6650450 : CollatzResearch.WordTrace tailWord_6650450 prefixEnd_6650450 3414877418693610317490143 := by
  unfold tailWord_6650450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60640459689140732819735201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161707892504375287519293869 60640459689140732819735201)
  ·
    refine ⟨45480344766855549614801401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60640459689140732819735201 45480344766855549614801401)
    ·
      refine ⟨34110258575141662211101051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45480344766855549614801401 34110258575141662211101051)
      ·
        refine ⟨51165387862712493316651577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34110258575141662211101051 51165387862712493316651577)
        ·
          refine ⟨38374040897034369987488683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51165387862712493316651577 38374040897034369987488683)
          ·
            refine ⟨57561061345551554981233025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38374040897034369987488683 57561061345551554981233025)
            ·
              refine ⟨43170796009163666235924769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57561061345551554981233025 43170796009163666235924769)
              ·
                refine ⟨32378097006872749676943577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43170796009163666235924769 32378097006872749676943577)
                ·
                  refine ⟨24283572755154562257707683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32378097006872749676943577 24283572755154562257707683)
                  ·
                    refine ⟨36425359132731843386561525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24283572755154562257707683 36425359132731843386561525)
                    ·
                      refine ⟨3414877418693610317490143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36425359132731843386561525 3414877418693610317490143)
                      ·
                        rfl

theorem cell23_6650450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6650450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650450 prefixEnd_6650450 := by exact prefixLift 6650450
  have htrace : WordTrace (prefixWord ++ tailWord_6650450) baseStart_6650450 baseEnd_6650450 := by
    simpa [prefixWord, tailWord_6650450, baseEnd_6650450] using wordTrace_append hprefix tailTrace_6650450
  have hstable : (prefixWord ++ tailWord_6650450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650450).length < 2 ^ (prefixWord ++ tailWord_6650450).sum := by decide
  have hdescent : baseEnd_6650450 < baseStart_6650450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650483 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 7]
def baseStart_6650483 : Nat := 118140960795 + 6650483 * 2 ^ 59
def prefixEnd_6650483 : Nat := 4983230072969 + 3 ^ 40 * 6650483 * 2
def baseEnd_6650483 : Nat := 1138298121185069562792497

theorem tailTrace_6650483 : CollatzResearch.WordTrace tailWord_6650483 prefixEnd_6650483 1138298121185069562792497 := by
  unfold tailWord_6650483
  simp only [CollatzResearch.WordTrace]
  refine ⟨242563042365443377914892103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161708694910295585276594735 242563042365443377914892103)
  ·
    refine ⟨363844563548165066872338155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242563042365443377914892103 363844563548165066872338155)
    ·
      refine ⟨545766845322247600308507233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363844563548165066872338155 545766845322247600308507233)
      ·
        refine ⟨409325133991685700231380425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545766845322247600308507233 409325133991685700231380425)
        ·
          refine ⟨306993850493764275173535319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409325133991685700231380425 306993850493764275173535319)
          ·
            refine ⟨460490775740646412760302979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306993850493764275173535319 460490775740646412760302979)
            ·
              refine ⟨690736163610969619140454469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460490775740646412760302979 690736163610969619140454469)
              ·
                refine ⟨129513030677056803588835213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690736163610969619140454469 129513030677056803588835213)
                ·
                  refine ⟨48567386503896301345813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129513030677056803588835213 48567386503896301345813205)
                  ·
                    refine ⟨1138298121185069562792497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48567386503896301345813205 1138298121185069562792497)
                    ·
                      rfl

theorem cell23_6650483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_6650483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650483 prefixEnd_6650483 := by exact prefixLift 6650483
  have htrace : WordTrace (prefixWord ++ tailWord_6650483) baseStart_6650483 baseEnd_6650483 := by
    simpa [prefixWord, tailWord_6650483, baseEnd_6650483] using wordTrace_append hprefix tailTrace_6650483
  have hstable : (prefixWord ++ tailWord_6650483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650483).length < 2 ^ (prefixWord ++ tailWord_6650483).sum := by decide
  have hdescent : baseEnd_6650483 < baseStart_6650483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650510 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6650510 : Nat := 118140960795 + 6650510 * 2 ^ 59
def prefixEnd_6650510 : Nat := 4983230072969 + 3 ^ 40 * 6650510 * 2
def baseEnd_6650510 : Nat := 3414908227532880082739867

theorem tailTrace_6650510 : CollatzResearch.WordTrace tailWord_6650510 prefixEnd_6650510 3414908227532880082739867 := by
  unfold tailWord_6650510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320503392043195190765623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161709351424230374350749989 30320503392043195190765623)
  ·
    refine ⟨45480755088064792786148435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30320503392043195190765623 45480755088064792786148435)
    ·
      refine ⟨68221132632097189179222653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45480755088064792786148435 68221132632097189179222653)
      ·
        refine ⟨25582924737036445942208495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68221132632097189179222653 25582924737036445942208495)
        ·
          refine ⟨38374387105554668913312743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25582924737036445942208495 38374387105554668913312743)
          ·
            refine ⟨57561580658332003369969115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38374387105554668913312743 57561580658332003369969115)
            ·
              refine ⟨86342370987498005054953673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57561580658332003369969115 86342370987498005054953673)
              ·
                refine ⟨64756778240623503791215255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86342370987498005054953673 64756778240623503791215255)
                ·
                  refine ⟨97135167360935255686822883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64756778240623503791215255 97135167360935255686822883)
                  ·
                    refine ⟨145702751041402883530234325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97135167360935255686822883 145702751041402883530234325)
                    ·
                      refine ⟨3414908227532880082739867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145702751041402883530234325 3414908227532880082739867)
                      ·
                        rfl

theorem cell23_6650510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6650510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650510 prefixEnd_6650510 := by exact prefixLift 6650510
  have htrace : WordTrace (prefixWord ++ tailWord_6650510) baseStart_6650510 baseEnd_6650510 := by
    simpa [prefixWord, tailWord_6650510, baseEnd_6650510] using wordTrace_append hprefix tailTrace_6650510
  have hstable : (prefixWord ++ tailWord_6650510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650510).length < 2 ^ (prefixWord ++ tailWord_6650510).sum := by decide
  have hdescent : baseEnd_6650510 < baseStart_6650510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650564 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6650564 : Nat := 118140960795 + 6650564 * 2 ^ 59
def prefixEnd_6650564 : Nat := 4983230072969 + 3 ^ 40 * 6650564 * 2
def baseEnd_6650564 : Nat := 1138311985162740957154873

theorem tailTrace_6650564 : CollatzResearch.WordTrace tailWord_6650564 prefixEnd_6650564 1138311985162740957154873 := by
  unfold tailWord_6650564
  simp only [CollatzResearch.WordTrace]
  refine ⟨121282998339074964374295373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161710664452099952499060497 121282998339074964374295373)
  ·
    refine ⟨45481124377153111640360765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121282998339074964374295373 45481124377153111640360765)
    ·
      refine ⟨17055421641432416865135287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45481124377153111640360765 17055421641432416865135287)
      ·
        refine ⟨25583132462148625297702931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17055421641432416865135287 25583132462148625297702931)
        ·
          refine ⟨38374698693222937946554397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25583132462148625297702931 38374698693222937946554397)
          ·
            refine ⟨14390512009958601729957899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38374698693222937946554397 14390512009958601729957899)
            ·
              refine ⟨21585768014937902594936849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390512009958601729957899 21585768014937902594936849)
              ·
                refine ⟨16189326011203426946202637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21585768014937902594936849 16189326011203426946202637)
                ·
                  refine ⟨6070997254201285104825989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16189326011203426946202637 6070997254201285104825989)
                  ·
                    refine ⟨1138311985162740957154873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070997254201285104825989 1138311985162740957154873)
                    ·
                      rfl

theorem cell23_6650564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6650564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650564 prefixEnd_6650564 := by exact prefixLift 6650564
  have htrace : WordTrace (prefixWord ++ tailWord_6650564) baseStart_6650564 baseEnd_6650564 := by
    simpa [prefixWord, tailWord_6650564, baseEnd_6650564] using wordTrace_append hprefix tailTrace_6650564
  have hstable : (prefixWord ++ tailWord_6650564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650564).length < 2 ^ (prefixWord ++ tailWord_6650564).sum := by decide
  have hdescent : baseEnd_6650564 < baseStart_6650564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650574 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_6650574 : Nat := 118140960795 + 6650574 * 2 ^ 59
def prefixEnd_6650574 : Nat := 4983230072969 + 3 ^ 40 * 6650574 * 2
def baseEnd_6650574 : Nat := 3414941090294767832339573

theorem tailTrace_6650574 : CollatzResearch.WordTrace tailWord_6650574 prefixEnd_6650574 3414941090294767832339573 := by
  unfold tailWord_6650574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320795176014212557056847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161710907605409133637636517 30320795176014212557056847)
  ·
    refine ⟨45481192764021318835585271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30320795176014212557056847 45481192764021318835585271)
    ·
      refine ⟨68221789146031978253377907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45481192764021318835585271 68221789146031978253377907)
      ·
        refine ⟨102332683719047967380066861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68221789146031978253377907 102332683719047967380066861)
        ·
          refine ⟨38374756394642987767525073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102332683719047967380066861 38374756394642987767525073)
          ·
            refine ⟨28781067295982240825643805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38374756394642987767525073 28781067295982240825643805)
            ·
              refine ⟨10792900235993340309616427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28781067295982240825643805 10792900235993340309616427)
              ·
                refine ⟨16189350353990010464424641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792900235993340309616427 16189350353990010464424641)
                ·
                  refine ⟨12142012765492507848318481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16189350353990010464424641 12142012765492507848318481)
                  ·
                    refine ⟨9106509574119380886238861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12142012765492507848318481 9106509574119380886238861)
                    ·
                      refine ⟨3414941090294767832339573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106509574119380886238861 3414941090294767832339573)
                      ·
                        rfl

theorem cell23_6650574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_6650574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650574 prefixEnd_6650574 := by exact prefixLift 6650574
  have htrace : WordTrace (prefixWord ++ tailWord_6650574) baseStart_6650574 baseEnd_6650574 := by
    simpa [prefixWord, tailWord_6650574, baseEnd_6650574] using wordTrace_append hprefix tailTrace_6650574
  have hstable : (prefixWord ++ tailWord_6650574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650574).length < 2 ^ (prefixWord ++ tailWord_6650574).sum := by decide
  have hdescent : baseEnd_6650574 < baseStart_6650574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650614 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6650614 : Nat := 118140960795 + 6650614 * 2 ^ 59
def prefixEnd_6650614 : Nat := 4983230072969 + 3 ^ 40 * 6650614 * 2
def baseEnd_6650614 : Nat := 3414961629520947675839389

theorem tailTrace_6650614 : CollatzResearch.WordTrace tailWord_6650614 prefixEnd_6650614 3414961629520947675839389 := by
  unfold tailWord_6650614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15160488770498049205494431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161711880218645858191940597 15160488770498049205494431)
  ·
    refine ⟨22740733155747073808241647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15160488770498049205494431 22740733155747073808241647)
    ·
      refine ⟨34111099733620610712362471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22740733155747073808241647 34111099733620610712362471)
      ·
        refine ⟨51166649600430916068543707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34111099733620610712362471 51166649600430916068543707)
        ·
          refine ⟨76749974400646374102815561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51166649600430916068543707 76749974400646374102815561)
          ·
            refine ⟨57562480800484780577111671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76749974400646374102815561 57562480800484780577111671)
            ·
              refine ⟨86343721200727170865667507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57562480800484780577111671 86343721200727170865667507)
              ·
                refine ⟨129515581801090756298501261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86343721200727170865667507 129515581801090756298501261)
                ·
                  refine ⟨48568343175409033611937973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129515581801090756298501261 48568343175409033611937973)
                  ·
                    refine ⟨4553282172694596901119185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48568343175409033611937973 4553282172694596901119185)
                    ·
                      refine ⟨3414961629520947675839389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553282172694596901119185 3414961629520947675839389)
                      ·
                        rfl

theorem cell23_6650614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6650614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650614 prefixEnd_6650614 := by exact prefixLift 6650614
  have htrace : WordTrace (prefixWord ++ tailWord_6650614) baseStart_6650614 baseEnd_6650614 := by
    simpa [prefixWord, tailWord_6650614, baseEnd_6650614] using wordTrace_append hprefix tailTrace_6650614
  have hstable : (prefixWord ++ tailWord_6650614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650614).length < 2 ^ (prefixWord ++ tailWord_6650614).sum := by decide
  have hdescent : baseEnd_6650614 < baseStart_6650614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650627 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 8, 2]
def baseStart_6650627 : Nat := 118140960795 + 6650627 * 2 ^ 59
def prefixEnd_6650627 : Nat := 4983230072969 + 3 ^ 40 * 6650627 * 2
def baseEnd_6650627 : Nat := 3414968304769456124976829

theorem tailTrace_6650627 : CollatzResearch.WordTrace tailWord_6650627 prefixEnd_6650627 3414968304769456124976829 := by
  unfold tailWord_6650627
  simp only [CollatzResearch.WordTrace]
  refine ⟨242568294476921690508134135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161712196317947793672089423 242568294476921690508134135)
  ·
    refine ⟨363852441715382535762201203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242568294476921690508134135 363852441715382535762201203)
    ·
      refine ⟨545778662573073803643301805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363852441715382535762201203 545778662573073803643301805)
      ·
        refine ⟨204666998464902676366238177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545778662573073803643301805 204666998464902676366238177)
        ·
          refine ⟨153500248848677007274678633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204666998464902676366238177 153500248848677007274678633)
          ·
            refine ⟨115125186636507755456008975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153500248848677007274678633 115125186636507755456008975)
            ·
              refine ⟨172687779954761633184013463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115125186636507755456008975 172687779954761633184013463)
              ·
                refine ⟨259031669932142449776020195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172687779954761633184013463 259031669932142449776020195)
                ·
                  refine ⟨388547504898213674664030293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259031669932142449776020195 388547504898213674664030293)
                  ·
                    refine ⟨4553291073025941499969105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 388547504898213674664030293 4553291073025941499969105)
                    ·
                      refine ⟨3414968304769456124976829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553291073025941499969105 3414968304769456124976829)
                      ·
                        rfl

theorem cell23_6650627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_6650627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650627 prefixEnd_6650627 := by exact prefixLift 6650627
  have htrace : WordTrace (prefixWord ++ tailWord_6650627) baseStart_6650627 baseEnd_6650627 := by
    simpa [prefixWord, tailWord_6650627, baseEnd_6650627] using wordTrace_append hprefix tailTrace_6650627
  have hstable : (prefixWord ++ tailWord_6650627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650627).length < 2 ^ (prefixWord ++ tailWord_6650627).sum := by decide
  have hdescent : baseEnd_6650627 < baseStart_6650627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650664 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6650664 : Nat := 118140960795 + 6650664 * 2 ^ 59
def prefixEnd_6650664 : Nat := 4983230072969 + 3 ^ 40 * 6650664 * 2
def baseEnd_6650664 : Nat := 3414987303553672480214159

theorem tailTrace_6650664 : CollatzResearch.WordTrace tailWord_6650664 prefixEnd_6650664 3414987303553672480214159 := by
  unfold tailWord_6650664
  simp only [CollatzResearch.WordTrace]
  refine ⟨121284821988893822913615523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161713095985191763884820697 121284821988893822913615523)
  ·
    refine ⟨181927232983340734370423285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121284821988893822913615523 181927232983340734370423285)
    ·
      refine ⟨17055678092188193847227183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181927232983340734370423285 17055678092188193847227183)
      ·
        refine ⟨25583517138282290770840775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17055678092188193847227183 25583517138282290770840775)
        ·
          refine ⟨38375275707423436156261163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25583517138282290770840775 38375275707423436156261163)
          ·
            refine ⟨57562913561135154234391745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38375275707423436156261163 57562913561135154234391745)
            ·
              refine ⟨43172185170851365675793809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57562913561135154234391745 43172185170851365675793809)
              ·
                refine ⟨32379138878138524256845357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43172185170851365675793809 32379138878138524256845357)
                ·
                  refine ⟨12142177079301946596317009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32379138878138524256845357 12142177079301946596317009)
                  ·
                    refine ⟨9106632809476459947237757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12142177079301946596317009 9106632809476459947237757)
                    ·
                      refine ⟨3414987303553672480214159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106632809476459947237757 3414987303553672480214159)
                      ·
                        rfl

theorem cell23_6650664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6650664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650664 prefixEnd_6650664 := by exact prefixLift 6650664
  have htrace : WordTrace (prefixWord ++ tailWord_6650664) baseStart_6650664 baseEnd_6650664 := by
    simpa [prefixWord, tailWord_6650664, baseEnd_6650664] using wordTrace_append hprefix tailTrace_6650664
  have hstable : (prefixWord ++ tailWord_6650664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650664).length < 2 ^ (prefixWord ++ tailWord_6650664).sum := by decide
  have hdescent : baseEnd_6650664 < baseStart_6650664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650711 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_6650711 : Nat := 118140960795 + 6650711 * 2 ^ 59
def prefixEnd_6650711 : Nat := 4983230072969 + 3 ^ 40 * 6650711 * 2
def baseEnd_6650711 : Nat := 3415011437144433796326443

theorem tailTrace_6650711 : CollatzResearch.WordTrace tailWord_6650711 prefixEnd_6650711 3415011437144433796326443 := by
  unfold tailWord_6650711
  simp only [CollatzResearch.WordTrace]
  refine ⟨242571358208617372854191987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161714238805744915236127991 242571358208617372854191987)
  ·
    refine ⟨363857037312926059281287981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242571358208617372854191987 363857037312926059281287981)
    ·
      refine ⟨136446388992347272230482993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363857037312926059281287981 136446388992347272230482993)
      ·
        refine ⟨102334791744260454172862245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136446388992347272230482993 102334791744260454172862245)
        ·
          refine ⟨19187773452048835157411671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102334791744260454172862245 19187773452048835157411671)
          ·
            refine ⟨28781660178073252736117507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187773452048835157411671 28781660178073252736117507)
            ·
              refine ⟨43172490267109879104176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28781660178073252736117507 43172490267109879104176261)
              ·
                refine ⟨8094841925083102332033049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43172490267109879104176261 8094841925083102332033049)
                ·
                  refine ⟨6071131443812326749024787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8094841925083102332033049 6071131443812326749024787)
                  ·
                    refine ⟨9106697165718490123537181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071131443812326749024787 9106697165718490123537181)
                    ·
                      refine ⟨3415011437144433796326443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106697165718490123537181 3415011437144433796326443)
                      ·
                        rfl

theorem cell23_6650711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_6650711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650711 prefixEnd_6650711 := by exact prefixLift 6650711
  have htrace : WordTrace (prefixWord ++ tailWord_6650711) baseStart_6650711 baseEnd_6650711 := by
    simpa [prefixWord, tailWord_6650711, baseEnd_6650711] using wordTrace_append hprefix tailTrace_6650711
  have hstable : (prefixWord ++ tailWord_6650711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650711).length < 2 ^ (prefixWord ++ tailWord_6650711).sum := by decide
  have hdescent : baseEnd_6650711 < baseStart_6650711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650727 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 8]
def baseStart_6650727 : Nat := 118140960795 + 6650727 * 2 ^ 59
def prefixEnd_6650727 : Nat := 4983230072969 + 3 ^ 40 * 6650727 * 2
def baseEnd_6650727 : Nat := 1138339884278301911242123

theorem tailTrace_6650727 : CollatzResearch.WordTrace tailWord_6650727 prefixEnd_6650727 1138339884278301911242123 := by
  unfold tailWord_6650727
  simp only [CollatzResearch.WordTrace]
  refine ⟨242571941776559407586774435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161714627851039605057849623 242571941776559407586774435)
  ·
    refine ⟨363857912664839111380161653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242571941776559407586774435 363857912664839111380161653)
    ·
      refine ⟨34111679312328666691890155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363857912664839111380161653 34111679312328666691890155)
      ·
        refine ⟨51167518968493000037835233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34111679312328666691890155 51167518968493000037835233)
        ·
          refine ⟨38375639226369750028376425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51167518968493000037835233 38375639226369750028376425)
          ·
            refine ⟨28781729419777312521282319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38375639226369750028376425 28781729419777312521282319)
            ·
              refine ⟨43172594129665968781923479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28781729419777312521282319 43172594129665968781923479)
              ·
                refine ⟨64758891194498953172885219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43172594129665968781923479 64758891194498953172885219)
                ·
                  refine ⟨97138336791748429759327829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64758891194498953172885219 97138336791748429759327829)
                  ·
                    refine ⟨1138339884278301911242123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97138336791748429759327829 1138339884278301911242123)
                    ·
                      rfl

theorem cell23_6650727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_6650727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650727 prefixEnd_6650727 := by exact prefixLift 6650727
  have htrace : WordTrace (prefixWord ++ tailWord_6650727) baseStart_6650727 baseEnd_6650727 := by
    simpa [prefixWord, tailWord_6650727, baseEnd_6650727] using wordTrace_append hprefix tailTrace_6650727
  have hstable : (prefixWord ++ tailWord_6650727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650727).length < 2 ^ (prefixWord ++ tailWord_6650727).sum := by decide
  have hdescent : baseEnd_6650727 < baseStart_6650727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650767 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_6650767 : Nat := 118140960795 + 6650767 * 2 ^ 59
def prefixEnd_6650767 : Nat := 4983230072969 + 3 ^ 40 * 6650767 * 2
def baseEnd_6650767 : Nat := 3415040192061085577226185

theorem tailTrace_6650767 : CollatzResearch.WordTrace tailWord_6650767 prefixEnd_6650767 3415040192061085577226185 := by
  unfold tailWord_6650767
  simp only [CollatzResearch.WordTrace]
  refine ⟨242573400696414494418230555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161715600464276329612153703 242573400696414494418230555)
  ·
    refine ⟨363860101044621741627345833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242573400696414494418230555 363860101044621741627345833)
    ·
      refine ⟨272895075783466306220509375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363860101044621741627345833 272895075783466306220509375)
      ·
        refine ⟨409342613675199459330764063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272895075783466306220509375 409342613675199459330764063)
        ·
          refine ⟨614013920512799188996146095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409342613675199459330764063 614013920512799188996146095)
          ·
            refine ⟨921020880769198783494219143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614013920512799188996146095 921020880769198783494219143)
            ·
              refine ⟨1381531321153798175241328715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921020880769198783494219143 1381531321153798175241328715)
              ·
                refine ⟨2072296981730697262861993073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381531321153798175241328715 2072296981730697262861993073)
                ·
                  refine ⟨1554222736298022947146494805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072296981730697262861993073 1554222736298022947146494805)
                  ·
                    refine ⟨9106773845496228205936493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1554222736298022947146494805 9106773845496228205936493)
                    ·
                      refine ⟨3415040192061085577226185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106773845496228205936493 3415040192061085577226185)
                      ·
                        rfl

theorem cell23_6650767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_6650767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650767 prefixEnd_6650767 := by exact prefixLift 6650767
  have htrace : WordTrace (prefixWord ++ tailWord_6650767) baseStart_6650767 baseEnd_6650767 := by
    simpa [prefixWord, tailWord_6650767, baseEnd_6650767] using wordTrace_append hprefix tailTrace_6650767
  have hstable : (prefixWord ++ tailWord_6650767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650767).length < 2 ^ (prefixWord ++ tailWord_6650767).sum := by decide
  have hdescent : baseEnd_6650767 < baseStart_6650767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650784 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_6650784 : Nat := 118140960795 + 6650784 * 2 ^ 59
def prefixEnd_6650784 : Nat := 4983230072969 + 3 ^ 40 * 6650784 * 2
def baseEnd_6650784 : Nat := 3415048921232212010713607

theorem tailTrace_6650784 : CollatzResearch.WordTrace tailWord_6650784 prefixEnd_6650784 3415048921232212010713607 := by
  unfold tailWord_6650784
  simp only [CollatzResearch.WordTrace]
  refine ⟨121287010368676453160799703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161716013824901937547732937 121287010368676453160799703)
  ·
    refine ⟨181930515553014679741199555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121287010368676453160799703 181930515553014679741199555)
    ·
      refine ⟨272895773329522019611799333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181930515553014679741199555 272895773329522019611799333)
      ·
        refine ⟨51167957499285378677212375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272895773329522019611799333 51167957499285378677212375)
        ·
          refine ⟨76751936248928068015818563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51167957499285378677212375 76751936248928068015818563)
          ·
            refine ⟨115127904373392102023727845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76751936248928068015818563 115127904373392102023727845)
            ·
              refine ⟨21586482070011019129448971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115127904373392102023727845 21586482070011019129448971)
              ·
                refine ⟨32379723105016528694173457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21586482070011019129448971 32379723105016528694173457)
                ·
                  refine ⟨24284792328762396520630093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32379723105016528694173457 24284792328762396520630093)
                  ·
                    refine ⟨9106797123285898695236285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24284792328762396520630093 9106797123285898695236285)
                    ·
                      refine ⟨3415048921232212010713607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106797123285898695236285 3415048921232212010713607)
                      ·
                        rfl

theorem cell23_6650784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_6650784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650784 prefixEnd_6650784 := by exact prefixLift 6650784
  have htrace : WordTrace (prefixWord ++ tailWord_6650784) baseStart_6650784 baseEnd_6650784 := by
    simpa [prefixWord, tailWord_6650784, baseEnd_6650784] using wordTrace_append hprefix tailTrace_6650784
  have hstable : (prefixWord ++ tailWord_6650784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650784).length < 2 ^ (prefixWord ++ tailWord_6650784).sum := by decide
  have hdescent : baseEnd_6650784 < baseStart_6650784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650787 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 7]
def baseStart_6650787 : Nat := 118140960795 + 6650787 * 2 ^ 59
def prefixEnd_6650787 : Nat := 4983230072969 + 3 ^ 40 * 6650787 * 2
def baseEnd_6650787 : Nat := 1138350153891391832992031

theorem tailTrace_6650787 : CollatzResearch.WordTrace tailWord_6650787 prefixEnd_6650787 1138350153891391832992031 := by
  unfold tailWord_6650787
  simp only [CollatzResearch.WordTrace]
  refine ⟨242574130156342037833958615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161716086770894691889305743 242574130156342037833958615)
  ·
    refine ⟨363861195234513056750937923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242574130156342037833958615 363861195234513056750937923)
    ·
      refine ⟨545791792851769585126406885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363861195234513056750937923 545791792851769585126406885)
      ·
        refine ⟨102335961159706797211201291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545791792851769585126406885 102335961159706797211201291)
        ·
          refine ⟨153503941739560195816801937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102335961159706797211201291 153503941739560195816801937)
          ·
            refine ⟨115127956304670146862601453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153503941739560195816801937 115127956304670146862601453)
            ·
              refine ⟨43172983614251305073475545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115127956304670146862601453 43172983614251305073475545)
              ·
                refine ⟨32379737710688478805106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43172983614251305073475545 32379737710688478805106659)
                ·
                  refine ⟨48569606566032718207659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32379737710688478805106659 48569606566032718207659989)
                  ·
                    refine ⟨1138350153891391832992031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48569606566032718207659989 1138350153891391832992031)
                    ·
                      rfl

theorem cell23_6650787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_6650787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650787 prefixEnd_6650787 := by exact prefixLift 6650787
  have htrace : WordTrace (prefixWord ++ tailWord_6650787) baseStart_6650787 baseEnd_6650787 := by
    simpa [prefixWord, tailWord_6650787, baseEnd_6650787] using wordTrace_append hprefix tailTrace_6650787
  have hstable : (prefixWord ++ tailWord_6650787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650787).length < 2 ^ (prefixWord ++ tailWord_6650787).sum := by decide
  have hdescent : baseEnd_6650787 < baseStart_6650787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650814 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6650814 : Nat := 118140960795 + 6650814 * 2 ^ 59
def prefixEnd_6650814 : Nat := 4983230072969 + 3 ^ 40 * 6650814 * 2
def baseEnd_6650814 : Nat := 3415064325651846893338469

theorem tailTrace_6650814 : CollatzResearch.WordTrace tailWord_6650814 prefixEnd_6650814 3415064325651846893338469 := by
  unfold tailWord_6650814
  simp only [CollatzResearch.WordTrace]
  refine ⟨30321889365905527680648937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161716743284829480963460997 30321889365905527680648937)
  ·
    refine ⟨22741417024429145760486703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30321889365905527680648937 22741417024429145760486703)
    ·
      refine ⟨34112125536643718640730055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22741417024429145760486703 34112125536643718640730055)
      ·
        refine ⟨51168188304965577961095083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34112125536643718640730055 51168188304965577961095083)
        ·
          refine ⟨76752282457448366941642625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51168188304965577961095083 76752282457448366941642625)
          ·
            refine ⟨57564211843086275206231969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76752282457448366941642625 57564211843086275206231969)
            ·
              refine ⟨43173158882314706404673977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57564211843086275206231969 43173158882314706404673977)
              ·
                refine ⟨32379869161736029803505483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43173158882314706404673977 32379869161736029803505483)
                ·
                  refine ⟨48569803742604044705258225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32379869161736029803505483 48569803742604044705258225)
                  ·
                    refine ⟨36427352806953033528943669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48569803742604044705258225 36427352806953033528943669)
                    ·
                      refine ⟨3415064325651846893338469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36427352806953033528943669 3415064325651846893338469)
                      ·
                        rfl

theorem cell23_6650814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6650814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650814 prefixEnd_6650814 := by exact prefixLift 6650814
  have htrace : WordTrace (prefixWord ++ tailWord_6650814) baseStart_6650814 baseEnd_6650814 := by
    simpa [prefixWord, tailWord_6650814, baseEnd_6650814] using wordTrace_append hprefix tailTrace_6650814
  have hstable : (prefixWord ++ tailWord_6650814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650814).length < 2 ^ (prefixWord ++ tailWord_6650814).sum := by decide
  have hdescent : baseEnd_6650814 < baseStart_6650814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650867 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_6650867 : Nat := 118140960795 + 6650867 * 2 ^ 59
def prefixEnd_6650867 : Nat := 4983230072969 + 3 ^ 40 * 6650867 * 2
def baseEnd_6650867 : Nat := 3415091540126535185975725

theorem tailTrace_6650867 : CollatzResearch.WordTrace tailWord_6650867 prefixEnd_6650867 3415091540126535185975725 := by
  unfold tailWord_6650867
  simp only [CollatzResearch.WordTrace]
  refine ⟨242577047996052211496870855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161718031997368140997913903 242577047996052211496870855)
  ·
    refine ⟨363865571994078317245306283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242577047996052211496870855 363865571994078317245306283)
    ·
      refine ⟨545798357991117475867959425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363865571994078317245306283 545798357991117475867959425)
      ·
        refine ⟨409348768493338106900969569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545798357991117475867959425 409348768493338106900969569)
        ·
          refine ⟨307011576370003580175727177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409348768493338106900969569 307011576370003580175727177)
          ·
            refine ⟨230258682277502685131795383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307011576370003580175727177 230258682277502685131795383)
            ·
              refine ⟨345388023416254027697693075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230258682277502685131795383 345388023416254027697693075)
              ·
                refine ⟨518082035124381041546539613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345388023416254027697693075 518082035124381041546539613)
                ·
                  refine ⟨194280763171642890579952355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518082035124381041546539613 194280763171642890579952355)
                  ·
                    refine ⟨291421144757464335869928533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194280763171642890579952355 291421144757464335869928533)
                    ·
                      refine ⟨3415091540126535185975725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291421144757464335869928533 3415091540126535185975725)
                      ·
                        rfl

theorem cell23_6650867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_6650867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650867 prefixEnd_6650867 := by exact prefixLift 6650867
  have htrace : WordTrace (prefixWord ++ tailWord_6650867) baseStart_6650867 baseEnd_6650867 := by
    simpa [prefixWord, tailWord_6650867, baseEnd_6650867] using wordTrace_append hprefix tailTrace_6650867
  have hstable : (prefixWord ++ tailWord_6650867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650867).length < 2 ^ (prefixWord ++ tailWord_6650867).sum := by decide
  have hdescent : baseEnd_6650867 < baseStart_6650867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650881 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 6]
def baseStart_6650881 : Nat := 118140960795 + 6650881 * 2 ^ 59
def prefixEnd_6650881 : Nat := 4983230072969 + 3 ^ 40 * 6650881 * 2
def baseEnd_6650881 : Nat := 379455414317299792355629

theorem tailTrace_6650881 : CollatzResearch.WordTrace tailWord_6650881 prefixEnd_6650881 379455414317299792355629 := by
  unfold tailWord_6650881
  simp only [CollatzResearch.WordTrace]
  refine ⟨242577558618001491887880497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161718372412000994591920331 242577558618001491887880497)
  ·
    refine ⟨181933168963501118915910373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242577558618001491887880497 181933168963501118915910373)
    ·
      refine ⟨34112469180656459796733195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181933168963501118915910373 34112469180656459796733195)
      ·
        refine ⟨51168703770984689695099793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34112469180656459796733195 51168703770984689695099793)
        ·
          refine ⟨38376527828238517271324845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51168703770984689695099793 38376527828238517271324845)
          ·
            refine ⟨14391197935589443976746817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38376527828238517271324845 14391197935589443976746817)
            ·
              refine ⟨10793398451692082982560113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14391197935589443976746817 10793398451692082982560113)
              ·
                refine ⟨8095048838769062236920085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10793398451692082982560113 8095048838769062236920085)
                ·
                  refine ⟨379455414317299792355629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8095048838769062236920085 379455414317299792355629)
                  ·
                    rfl

theorem cell23_6650881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_6650881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650881 prefixEnd_6650881 := by exact prefixLift 6650881
  have htrace : WordTrace (prefixWord ++ tailWord_6650881) baseStart_6650881 baseEnd_6650881 := by
    simpa [prefixWord, tailWord_6650881, baseEnd_6650881] using wordTrace_append hprefix tailTrace_6650881
  have hstable : (prefixWord ++ tailWord_6650881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650881).length < 2 ^ (prefixWord ++ tailWord_6650881).sum := by decide
  have hdescent : baseEnd_6650881 < baseStart_6650881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650912 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6650912 : Nat := 118140960795 + 6650912 * 2 ^ 59
def prefixEnd_6650912 : Nat := 4983230072969 + 3 ^ 40 * 6650912 * 2
def baseEnd_6650912 : Nat := 3415114646755987509913019

theorem tailTrace_6650912 : CollatzResearch.WordTrace tailWord_6650912 prefixEnd_6650912 3415114646755987509913019 := by
  unfold tailWord_6650912
  simp only [CollatzResearch.WordTrace]
  refine ⟨121289344640444592091129495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161719126187259456121505993 121289344640444592091129495)
  ·
    refine ⟨181934016960666888136694243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121289344640444592091129495 181934016960666888136694243)
    ·
      refine ⟨272901025441000332205041365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181934016960666888136694243 272901025441000332205041365)
      ·
        refine ⟨6396117783773445286055657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 272901025441000332205041365 6396117783773445286055657)
        ·
          refine ⟨4797088337830083964541743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6396117783773445286055657 4797088337830083964541743)
          ·
            refine ⟨7195632506745125946812615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797088337830083964541743 7195632506745125946812615)
            ·
              refine ⟨10793448760117688920218923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195632506745125946812615 10793448760117688920218923)
              ·
                refine ⟨16190173140176533380328385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793448760117688920218923 16190173140176533380328385)
                ·
                  refine ⟨12142629855132400035246289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16190173140176533380328385 12142629855132400035246289)
                  ·
                    refine ⟨9106972391349300026434717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12142629855132400035246289 9106972391349300026434717)
                    ·
                      refine ⟨3415114646755987509913019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9106972391349300026434717 3415114646755987509913019)
                      ·
                        rfl

theorem cell23_6650912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6650912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650912 prefixEnd_6650912 := by exact prefixLift 6650912
  have htrace : WordTrace (prefixWord ++ tailWord_6650912) baseStart_6650912 baseEnd_6650912 := by
    simpa [prefixWord, tailWord_6650912, baseEnd_6650912] using wordTrace_append hprefix tailTrace_6650912
  have hstable : (prefixWord ++ tailWord_6650912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650912).length < 2 ^ (prefixWord ++ tailWord_6650912).sum := by decide
  have hdescent : baseEnd_6650912 < baseStart_6650912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650924 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_6650924 : Nat := 118140960795 + 6650924 * 2 ^ 59
def prefixEnd_6650924 : Nat := 4983230072969 + 3 ^ 40 * 6650924 * 2
def baseEnd_6650924 : Nat := 1138373602841280487654321

theorem tailTrace_6650924 : CollatzResearch.WordTrace tailWord_6650924 prefixEnd_6650924 1138373602841280487654321 := by
  unfold tailWord_6650924
  simp only [CollatzResearch.WordTrace]
  refine ⟨121289563478422855115847913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161719417971230473487797217 121289563478422855115847913)
  ·
    refine ⟨90967172608817141336885935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121289563478422855115847913 90967172608817141336885935)
    ·
      refine ⟨136450758913225712005328903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90967172608817141336885935 136450758913225712005328903)
      ·
        refine ⟨204676138369838568007993355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136450758913225712005328903 204676138369838568007993355)
        ·
          refine ⟨307014207554757852011990033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204676138369838568007993355 307014207554757852011990033)
          ·
            refine ⟨230260655666068389008992525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307014207554757852011990033 230260655666068389008992525)
            ·
              refine ⟨86347745874775645878372197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230260655666068389008992525 86347745874775645878372197)
              ·
                refine ⟨16190202351520433602194787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86347745874775645878372197 16190202351520433602194787)
                ·
                  refine ⟨24285303527280650403292181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16190202351520433602194787 24285303527280650403292181)
                  ·
                    refine ⟨1138373602841280487654321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24285303527280650403292181 1138373602841280487654321)
                    ·
                      rfl

theorem cell23_6650924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_6650924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650924 prefixEnd_6650924 := by exact prefixLift 6650924
  have htrace : WordTrace (prefixWord ++ tailWord_6650924) baseStart_6650924 baseEnd_6650924 := by
    simpa [prefixWord, tailWord_6650924, baseEnd_6650924] using wordTrace_append hprefix tailTrace_6650924
  have hstable : (prefixWord ++ tailWord_6650924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650924).length < 2 ^ (prefixWord ++ tailWord_6650924).sum := by decide
  have hdescent : baseEnd_6650924 < baseStart_6650924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650942 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6650942 : Nat := 118140960795 + 6650942 * 2 ^ 59
def prefixEnd_6650942 : Nat := 4983230072969 + 3 ^ 40 * 6650942 * 2
def baseEnd_6650942 : Nat := 3415130051175622392537881

theorem tailTrace_6650942 : CollatzResearch.WordTrace tailWord_6650942 prefixEnd_6650942 3415130051175622392537881 := by
  unfold tailWord_6650942
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322472933847562413231385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161719855647186999537234053 30322472933847562413231385)
  ·
    refine ⟨22741854700385671809923539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30322472933847562413231385 22741854700385671809923539)
    ·
      refine ⟨34112782050578507714885309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22741854700385671809923539 34112782050578507714885309)
      ·
        refine ⟨12792293268966940393081991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34112782050578507714885309 12792293268966940393081991)
        ·
          refine ⟨19188439903450410589622987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792293268966940393081991 19188439903450410589622987)
          ·
            refine ⟨28782659855175615884434481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188439903450410589622987 28782659855175615884434481)
            ·
              refine ⟨21586994891381711913325861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28782659855175615884434481 21586994891381711913325861)
              ·
                refine ⟨4047561542134070983748599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21586994891381711913325861 4047561542134070983748599)
                ·
                  refine ⟨6071342313201106475622899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047561542134070983748599 6071342313201106475622899)
                  ·
                    refine ⟨9107013469801659713434349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071342313201106475622899 9107013469801659713434349)
                    ·
                      refine ⟨3415130051175622392537881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107013469801659713434349 3415130051175622392537881)
                      ·
                        rfl

theorem cell23_6650942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6650942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650942 prefixEnd_6650942 := by exact prefixLift 6650942
  have htrace : WordTrace (prefixWord ++ tailWord_6650942) baseStart_6650942 baseEnd_6650942 := by
    simpa [prefixWord, tailWord_6650942, baseEnd_6650942] using wordTrace_append hprefix tailTrace_6650942
  have hstable : (prefixWord ++ tailWord_6650942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650942).length < 2 ^ (prefixWord ++ tailWord_6650942).sum := by decide
  have hdescent : baseEnd_6650942 < baseStart_6650942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650944 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_6650944 : Nat := 118140960795 + 6650944 * 2 ^ 59
def prefixEnd_6650944 : Nat := 4983230072969 + 3 ^ 40 * 6650944 * 2
def baseEnd_6650944 : Nat := 3415131078136931384712871

theorem tailTrace_6650944 : CollatzResearch.WordTrace tailWord_6650944 prefixEnd_6650944 3415131078136931384712871 := by
  unfold tailWord_6650944
  simp only [CollatzResearch.WordTrace]
  refine ⟨121289928208386626823711943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161719904277848835764949257 121289928208386626823711943)
  ·
    refine ⟨181934892312579940235567915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121289928208386626823711943 181934892312579940235567915)
    ·
      refine ⟨272902338468869910353351873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181934892312579940235567915 272902338468869910353351873)
      ·
        refine ⟨204676753851652432765013905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272902338468869910353351873 204676753851652432765013905)
        ·
          refine ⟨153507565388739324573760429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204676753851652432765013905 153507565388739324573760429)
          ·
            refine ⟨57565337020777246715160161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153507565388739324573760429 57565337020777246715160161)
            ·
              refine ⟨43174002765582935036370121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57565337020777246715160161 43174002765582935036370121)
              ·
                refine ⟨32380502074187201277277591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43174002765582935036370121 32380502074187201277277591)
                ·
                  refine ⟨48570753111280801915916387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32380502074187201277277591 48570753111280801915916387)
                  ·
                    refine ⟨72856129666921202873874581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48570753111280801915916387 72856129666921202873874581)
                    ·
                      refine ⟨3415131078136931384712871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72856129666921202873874581 3415131078136931384712871)
                      ·
                        rfl

theorem cell23_6650944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_6650944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650944 prefixEnd_6650944 := by exact prefixLift 6650944
  have htrace : WordTrace (prefixWord ++ tailWord_6650944) baseStart_6650944 baseEnd_6650944 := by
    simpa [prefixWord, tailWord_6650944, baseEnd_6650944] using wordTrace_append hprefix tailTrace_6650944
  have hstable : (prefixWord ++ tailWord_6650944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650944).length < 2 ^ (prefixWord ++ tailWord_6650944).sum := by decide
  have hdescent : baseEnd_6650944 < baseStart_6650944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650951 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_6650951 : Nat := 118140960795 + 6650951 * 2 ^ 59
def prefixEnd_6650951 : Nat := 4983230072969 + 3 ^ 40 * 6650951 * 2
def baseEnd_6650951 : Nat := 3415134672501512857325339

theorem tailTrace_6650951 : CollatzResearch.WordTrace tailWord_6650951 prefixEnd_6650951 3415134672501512857325339 := by
  unfold tailWord_6650951
  simp only [CollatzResearch.WordTrace]
  refine ⟨242580111727747893842928707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161720074485165262561952471 242580111727747893842928707)
  ·
    refine ⟨363870167591621840764393061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242580111727747893842928707 363870167591621840764393061)
    ·
      refine ⟨68225656423429095143323699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363870167591621840764393061 68225656423429095143323699)
      ·
        refine ⟨102338484635143642714985549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68225656423429095143323699 102338484635143642714985549)
        ·
          refine ⟨38376931738178866018119581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102338484635143642714985549 38376931738178866018119581)
          ·
            refine ⟨14391349401817074756794843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38376931738178866018119581 14391349401817074756794843)
            ·
              refine ⟨21587024102725612135192265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391349401817074756794843 21587024102725612135192265)
              ·
                refine ⟨16190268077044209101394199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21587024102725612135192265 16190268077044209101394199)
                ·
                  refine ⟨24285402115566313652091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16190268077044209101394199 24285402115566313652091299)
                  ·
                    refine ⟨36428103173349470478136949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24285402115566313652091299 36428103173349470478136949)
                    ·
                      refine ⟨3415134672501512857325339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36428103173349470478136949 3415134672501512857325339)
                      ·
                        rfl

theorem cell23_6650951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_6650951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650951 prefixEnd_6650951 := by exact prefixLift 6650951
  have htrace : WordTrace (prefixWord ++ tailWord_6650951) baseStart_6650951 baseEnd_6650951 := by
    simpa [prefixWord, tailWord_6650951, baseEnd_6650951] using wordTrace_append hprefix tailTrace_6650951
  have hstable : (prefixWord ++ tailWord_6650951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650951).length < 2 ^ (prefixWord ++ tailWord_6650951).sum := by decide
  have hdescent : baseEnd_6650951 < baseStart_6650951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650961 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_6650961 : Nat := 118140960795 + 6650961 * 2 ^ 59
def prefixEnd_6650961 : Nat := 4983230072969 + 3 ^ 40 * 6650961 * 2
def baseEnd_6650961 : Nat := 3415139807308057818200293

theorem tailTrace_6650961 : CollatzResearch.WordTrace tailWord_6650961 prefixEnd_6650961 3415139807308057818200293 := by
  unfold tailWord_6650961
  simp only [CollatzResearch.WordTrace]
  refine ⟨242580476457711665550792737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161720317638474443700528491 242580476457711665550792737)
  ·
    refine ⟨181935357343283749163094553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242580476457711665550792737 181935357343283749163094553)
    ·
      refine ⟨136451518007462811872320915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181935357343283749163094553 136451518007462811872320915)
      ·
        refine ⟨204677277011194217808481373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136451518007462811872320915 204677277011194217808481373)
        ·
          refine ⟨76753978879197831678180515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204677277011194217808481373 76753978879197831678180515)
          ·
            refine ⟨115130968318796747517270773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76753978879197831678180515 115130968318796747517270773)
            ·
              refine ⟨10793528279887195079744135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115130968318796747517270773 10793528279887195079744135)
              ·
                refine ⟨16190292419830792619616203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793528279887195079744135 16190292419830792619616203)
                ·
                  refine ⟨24285438629746188929424305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16190292419830792619616203 24285438629746188929424305)
                  ·
                    refine ⟨18214078972309641697068229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24285438629746188929424305 18214078972309641697068229)
                    ·
                      refine ⟨3415139807308057818200293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18214078972309641697068229 3415139807308057818200293)
                      ·
                        rfl

theorem cell23_6650961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_6650961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650961 prefixEnd_6650961 := by exact prefixLift 6650961
  have htrace : WordTrace (prefixWord ++ tailWord_6650961) baseStart_6650961 baseEnd_6650961 := by
    simpa [prefixWord, tailWord_6650961, baseEnd_6650961] using wordTrace_append hprefix tailTrace_6650961
  have hstable : (prefixWord ++ tailWord_6650961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650961).length < 2 ^ (prefixWord ++ tailWord_6650961).sum := by decide
  have hdescent : baseEnd_6650961 < baseStart_6650961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650968 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_6650968 : Nat := 118140960795 + 6650968 * 2 ^ 59
def prefixEnd_6650968 : Nat := 4983230072969 + 3 ^ 40 * 6650968 * 2
def baseEnd_6650968 : Nat := 3415143401672639290812761

theorem tailTrace_6650968 : CollatzResearch.WordTrace tailWord_6650968 prefixEnd_6650968 3415143401672639290812761 := by
  unfold tailWord_6650968
  simp only [CollatzResearch.WordTrace]
  refine ⟨121290365884343152873148779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161720487845790870497531705 121290365884343152873148779)
  ·
    refine ⟨181935548826514729309723169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121290365884343152873148779 181935548826514729309723169)
    ·
      refine ⟨136451661619886046982292377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181935548826514729309723169 136451661619886046982292377)
      ·
        refine ⟨102338746214914535236719283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136451661619886046982292377 102338746214914535236719283)
        ·
          refine ⟨153508119322371802855078925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102338746214914535236719283 153508119322371802855078925)
          ·
            refine ⟨57565544745889426070654597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153508119322371802855078925 57565544745889426070654597)
            ·
              refine ⟨10793539639854267388247737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57565544745889426070654597 10793539639854267388247737)
              ·
                refine ⟨8095154729890700541185803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10793539639854267388247737 8095154729890700541185803)
                ·
                  refine ⟨12142732094836050811778705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095154729890700541185803 12142732094836050811778705)
                  ·
                    refine ⟨9107049071127038108834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12142732094836050811778705 9107049071127038108834029)
                    ·
                      refine ⟨3415143401672639290812761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107049071127038108834029 3415143401672639290812761)
                      ·
                        rfl

theorem cell23_6650968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_6650968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650968 prefixEnd_6650968 := by exact prefixLift 6650968
  have htrace : WordTrace (prefixWord ++ tailWord_6650968) baseStart_6650968 baseEnd_6650968 := by
    simpa [prefixWord, tailWord_6650968, baseEnd_6650968] using wordTrace_append hprefix tailTrace_6650968
  have hstable : (prefixWord ++ tailWord_6650968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650968).length < 2 ^ (prefixWord ++ tailWord_6650968).sum := by decide
  have hdescent : baseEnd_6650968 < baseStart_6650968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650981 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_6650981 : Nat := 118140960795 + 6650981 * 2 ^ 59
def prefixEnd_6650981 : Nat := 4983230072969 + 3 ^ 40 * 6650981 * 2
def baseEnd_6650981 : Nat := 3415150076921147739950201

theorem tailTrace_6650981 : CollatzResearch.WordTrace tailWord_6650981 prefixEnd_6650981 3415150076921147739950201 := by
  unfold tailWord_6650981
  simp only [CollatzResearch.WordTrace]
  refine ⟨242581205917639208966520797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161720803945092805977680531 242581205917639208966520797)
  ·
    refine ⟨90967952219114703362445299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242581205917639208966520797 90967952219114703362445299)
    ·
      refine ⟨136451928328672055043667949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90967952219114703362445299 136451928328672055043667949)
      ·
        refine ⟨51169473123252020641375481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136451928328672055043667949 51169473123252020641375481)
        ·
          refine ⟨38377104842439015481031611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51169473123252020641375481 38377104842439015481031611)
          ·
            refine ⟨57565657263658523221547417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38377104842439015481031611 57565657263658523221547417)
            ·
              refine ⟨43174242947743892416160563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57565657263658523221547417 43174242947743892416160563)
              ·
                refine ⟨64761364421615838624240845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43174242947743892416160563 64761364421615838624240845)
                ·
                  refine ⟨24285511658105939484090317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64761364421615838624240845 24285511658105939484090317)
                  ·
                    refine ⟨9107066871789727306533869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24285511658105939484090317 9107066871789727306533869)
                    ·
                      refine ⟨3415150076921147739950201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107066871789727306533869 3415150076921147739950201)
                      ·
                        rfl

theorem cell23_6650981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_6650981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650981 prefixEnd_6650981 := by exact prefixLift 6650981
  have htrace : WordTrace (prefixWord ++ tailWord_6650981) baseStart_6650981 baseEnd_6650981 := by
    simpa [prefixWord, tailWord_6650981, baseEnd_6650981] using wordTrace_append hprefix tailTrace_6650981
  have hstable : (prefixWord ++ tailWord_6650981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650981).length < 2 ^ (prefixWord ++ tailWord_6650981).sum := by decide
  have hdescent : baseEnd_6650981 < baseStart_6650981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651041 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6651041 : Nat := 118140960795 + 6651041 * 2 ^ 59
def prefixEnd_6651041 : Nat := 4983230072969 + 3 ^ 40 * 6651041 * 2
def baseEnd_6651041 : Nat := 3415180885760417505199925

theorem tailTrace_6651041 : CollatzResearch.WordTrace tailWord_6651041 prefixEnd_6651041 3415180885760417505199925 := by
  unfold tailWord_6651041
  simp only [CollatzResearch.WordTrace]
  refine ⟨242583394297421839213704977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161722262864947892809136651 242583394297421839213704977)
  ·
    refine ⟨181937545723066379410278733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242583394297421839213704977 181937545723066379410278733)
    ·
      refine ⟨68226579646149892278854525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181937545723066379410278733 68226579646149892278854525)
      ·
        refine ⟨25584967367306209604570447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68226579646149892278854525 25584967367306209604570447)
        ·
          refine ⟨38377451050959314406855671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25584967367306209604570447 38377451050959314406855671)
          ·
            refine ⟨57566176576438971610283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38377451050959314406855671 57566176576438971610283507)
            ·
              refine ⟨86349264864658457415425261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57566176576438971610283507 86349264864658457415425261)
              ·
                refine ⟨32380974324246921530784473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86349264864658457415425261 32380974324246921530784473)
                ·
                  refine ⟨24285730743185191148088355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32380974324246921530784473 24285730743185191148088355)
                  ·
                    refine ⟨36428596114777786722132533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24285730743185191148088355 36428596114777786722132533)
                    ·
                      refine ⟨3415180885760417505199925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36428596114777786722132533 3415180885760417505199925)
                      ·
                        rfl

theorem cell23_6651041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6651041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651041 prefixEnd_6651041 := by exact prefixLift 6651041
  have htrace : WordTrace (prefixWord ++ tailWord_6651041) baseStart_6651041 baseEnd_6651041 := by
    simpa [prefixWord, tailWord_6651041, baseEnd_6651041] using wordTrace_append hprefix tailTrace_6651041
  have hstable : (prefixWord ++ tailWord_6651041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651041).length < 2 ^ (prefixWord ++ tailWord_6651041).sum := by decide
  have hdescent : baseEnd_6651041 < baseStart_6651041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651055 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 2, 2, 2]
def baseStart_6651055 : Nat := 118140960795 + 6651055 * 2 ^ 59
def prefixEnd_6651055 : Nat := 4983230072969 + 3 ^ 40 * 6651055 * 2
def baseEnd_6651055 : Nat := 3415188074489580450424861

theorem tailTrace_6651055 : CollatzResearch.WordTrace tailWord_6651055 prefixEnd_6651055 3415188074489580450424861 := by
  unfold tailWord_6651055
  simp only [CollatzResearch.WordTrace]
  refine ⟨242583904919371119604714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161722603279580746403143079 242583904919371119604714619)
  ·
    refine ⟨363875857379056679407071929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242583904919371119604714619 363875857379056679407071929)
    ·
      refine ⟨272906893034292509555303947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363875857379056679407071929 272906893034292509555303947)
      ·
        refine ⟨409360339551438764332955921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272906893034292509555303947 409360339551438764332955921)
        ·
          refine ⟨307020254663579073249716941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409360339551438764332955921 307020254663579073249716941)
          ·
            refine ⟨115132595498842152468643853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307020254663579073249716941 115132595498842152468643853)
            ·
              refine ⟨43174723312065807175741445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115132595498842152468643853 43174723312065807175741445)
              ·
                refine ⟨8095260621012338845451521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43174723312065807175741445 8095260621012338845451521)
                ·
                  refine ⟨6071445465759254134088641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095260621012338845451521 6071445465759254134088641)
                  ·
                    refine ⟨4553584099319440600566481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071445465759254134088641 4553584099319440600566481)
                    ·
                      refine ⟨3415188074489580450424861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553584099319440600566481 3415188074489580450424861)
                      ·
                        rfl

theorem cell23_6651055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2, 2].length) (baseStart_6651055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651055 prefixEnd_6651055 := by exact prefixLift 6651055
  have htrace : WordTrace (prefixWord ++ tailWord_6651055) baseStart_6651055 baseEnd_6651055 := by
    simpa [prefixWord, tailWord_6651055, baseEnd_6651055] using wordTrace_append hprefix tailTrace_6651055
  have hstable : (prefixWord ++ tailWord_6651055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651055).length < 2 ^ (prefixWord ++ tailWord_6651055).sum := by decide
  have hdescent : baseEnd_6651055 < baseStart_6651055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651068 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6651068 : Nat := 118140960795 + 6651068 * 2 ^ 59
def prefixEnd_6651068 : Nat := 4983230072969 + 3 ^ 40 * 6651068 * 2
def baseEnd_6651068 : Nat := 3415194749738088899562301

theorem tailTrace_6651068 : CollatzResearch.WordTrace tailWord_6651068 prefixEnd_6651068 3415194749738088899562301 := by
  unfold tailWord_6651068
  simp only [CollatzResearch.WordTrace]
  refine ⟨121292189534162011412468929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161722919378882681883291905 121292189534162011412468929)
  ·
    refine ⟨90969142150621508559351697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121292189534162011412468929 90969142150621508559351697)
    ·
      refine ⟨68226856612966131419513773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90969142150621508559351697 68226856612966131419513773)
      ·
        refine ⟨25585071229862299282317665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68226856612966131419513773 25585071229862299282317665)
        ·
          refine ⟨19188803422396724461738249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25585071229862299282317665 19188803422396724461738249)
          ·
            refine ⟨14391602566797543346303687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19188803422396724461738249 14391602566797543346303687)
            ·
              refine ⟨21587403850196315019455531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391602566797543346303687 21587403850196315019455531)
              ·
                refine ⟨32381105775294472529183297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21587403850196315019455531 32381105775294472529183297)
                ·
                  refine ⟨24285829331470854396887473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32381105775294472529183297 24285829331470854396887473)
                  ·
                    refine ⟨18214371998603140797665605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24285829331470854396887473 18214371998603140797665605)
                    ·
                      refine ⟨3415194749738088899562301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18214371998603140797665605 3415194749738088899562301)
                      ·
                        rfl

theorem cell23_6651068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6651068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651068 prefixEnd_6651068 := by exact prefixLift 6651068
  have htrace : WordTrace (prefixWord ++ tailWord_6651068) baseStart_6651068 baseEnd_6651068 := by
    simpa [prefixWord, tailWord_6651068, baseEnd_6651068] using wordTrace_append hprefix tailTrace_6651068
  have hstable : (prefixWord ++ tailWord_6651068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651068).length < 2 ^ (prefixWord ++ tailWord_6651068).sum := by decide
  have hdescent : baseEnd_6651068 < baseStart_6651068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651071 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_6651071 : Nat := 118140960795 + 6651071 * 2 ^ 59
def prefixEnd_6651071 : Nat := 4983230072969 + 3 ^ 40 * 6651071 * 2
def baseEnd_6651071 : Nat := 3415196290180052387824787

theorem tailTrace_6651071 : CollatzResearch.WordTrace tailWord_6651071 prefixEnd_6651071 3415196290180052387824787 := by
  unfold tailWord_6651071
  simp only [CollatzResearch.WordTrace]
  refine ⟨242584488487313154337297067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161722992324875436224864711 242584488487313154337297067)
  ·
    refine ⟨363876732730969731505945601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242584488487313154337297067 363876732730969731505945601)
    ·
      refine ⟨272907549548227298629459201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363876732730969731505945601 272907549548227298629459201)
      ·
        refine ⟨204680662161170473972094401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272907549548227298629459201 204680662161170473972094401)
        ·
          refine ⟨153510496620877855479070801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204680662161170473972094401 153510496620877855479070801)
          ·
            refine ⟨115132872465658391609303101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153510496620877855479070801 115132872465658391609303101)
            ·
              refine ⟨43174827174621896853488663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115132872465658391609303101 43174827174621896853488663)
              ·
                refine ⟨64762240761932845280232995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43174827174621896853488663 64762240761932845280232995)
                ·
                  refine ⟨97143361142899267920349493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64762240761932845280232995 97143361142899267920349493)
                  ·
                    refine ⟨9107190107146806367532765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97143361142899267920349493 9107190107146806367532765)
                    ·
                      refine ⟨3415196290180052387824787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107190107146806367532765 3415196290180052387824787)
                      ·
                        rfl

theorem cell23_6651071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_6651071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651071 prefixEnd_6651071 := by exact prefixLift 6651071
  have htrace : WordTrace (prefixWord ++ tailWord_6651071) baseStart_6651071 baseEnd_6651071 := by
    simpa [prefixWord, tailWord_6651071, baseEnd_6651071] using wordTrace_append hprefix tailTrace_6651071
  have hstable : (prefixWord ++ tailWord_6651071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651071).length < 2 ^ (prefixWord ++ tailWord_6651071).sum := by decide
  have hdescent : baseEnd_6651071 < baseStart_6651071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651141 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_6651141 : Nat := 118140960795 + 6651141 * 2 ^ 59
def prefixEnd_6651141 : Nat := 4983230072969 + 3 ^ 40 * 6651141 * 2
def baseEnd_6651141 : Nat := 3415232233825867113949465

theorem tailTrace_6651141 : CollatzResearch.WordTrace tailWord_6651141 prefixEnd_6651141 3415232233825867113949465 := by
  unfold tailWord_6651141
  simp only [CollatzResearch.WordTrace]
  refine ⟨242587041597059556292345277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161724694398039704194896851 242587041597059556292345277)
  ·
    refine ⟨90970140598897333609629479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242587041597059556292345277 90970140598897333609629479)
    ·
      refine ⟨136455210898346000414444219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90970140598897333609629479 136455210898346000414444219)
      ·
        refine ⟨204682816347519000621666329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136455210898346000414444219 204682816347519000621666329)
        ·
          refine ⟨153512112260639250466249747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204682816347519000621666329 153512112260639250466249747)
          ·
            refine ⟨230268168390958875699374621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153512112260639250466249747 230268168390958875699374621)
            ·
              refine ⟨86350563146609578387265483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230268168390958875699374621 86350563146609578387265483)
              ·
                refine ⟨129525844719914367580898225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86350563146609578387265483 129525844719914367580898225)
                ·
                  refine ⟨97144383539935775685673669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129525844719914367580898225 97144383539935775685673669)
                  ·
                    refine ⟨18214571913737957941063813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97144383539935775685673669 18214571913737957941063813)
                    ·
                      refine ⟨3415232233825867113949465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18214571913737957941063813 3415232233825867113949465)
                      ·
                        rfl

theorem cell23_6651141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_6651141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651141 prefixEnd_6651141 := by exact prefixLift 6651141
  have htrace : WordTrace (prefixWord ++ tailWord_6651141) baseStart_6651141 baseEnd_6651141 := by
    simpa [prefixWord, tailWord_6651141, baseEnd_6651141] using wordTrace_append hprefix tailTrace_6651141
  have hstable : (prefixWord ++ tailWord_6651141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651141).length < 2 ^ (prefixWord ++ tailWord_6651141).sum := by decide
  have hdescent : baseEnd_6651141 < baseStart_6651141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651148 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_6651148 : Nat := 118140960795 + 6651148 * 2 ^ 59
def prefixEnd_6651148 : Nat := 4983230072969 + 3 ^ 40 * 6651148 * 2
def baseEnd_6651148 : Nat := 3415235828190448586561933

theorem tailTrace_6651148 : CollatzResearch.WordTrace tailWord_6651148 prefixEnd_6651148 3415235828190448586561933 := by
  unfold tailWord_6651148
  simp only [CollatzResearch.WordTrace]
  refine ⟨121293648454017098243925049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161724864605356130991900065 121293648454017098243925049)
  ·
    refine ⟨90970236340512823682943787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121293648454017098243925049 90970236340512823682943787)
    ·
      refine ⟨136455354510769235524415681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90970236340512823682943787 136455354510769235524415681)
      ·
        refine ⟨102341515883076926643311761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136455354510769235524415681 102341515883076926643311761)
        ·
          refine ⟨76756136912307694982483821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102341515883076926643311761 76756136912307694982483821)
          ·
            refine ⟨28783551342115385618431433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76756136912307694982483821 28783551342115385618431433)
            ·
              refine ⟨21587663506586539213823575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28783551342115385618431433 21587663506586539213823575)
              ·
                refine ⟨32381495259879808820735363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21587663506586539213823575 32381495259879808820735363)
                ·
                  refine ⟨48572242889819713231103045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32381495259879808820735363 48572242889819713231103045)
                  ·
                    refine ⟨9107295541841196230831821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48572242889819713231103045 9107295541841196230831821)
                    ·
                      refine ⟨3415235828190448586561933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107295541841196230831821 3415235828190448586561933)
                      ·
                        rfl

theorem cell23_6651148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_6651148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651148 prefixEnd_6651148 := by exact prefixLift 6651148
  have htrace : WordTrace (prefixWord ++ tailWord_6651148) baseStart_6651148 baseEnd_6651148 := by
    simpa [prefixWord, tailWord_6651148, baseEnd_6651148] using wordTrace_append hprefix tailTrace_6651148
  have hstable : (prefixWord ++ tailWord_6651148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651148).length < 2 ^ (prefixWord ++ tailWord_6651148).sum := by decide
  have hdescent : baseEnd_6651148 < baseStart_6651148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651165 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6651165 : Nat := 118140960795 + 6651165 * 2 ^ 59
def prefixEnd_6651165 : Nat := 4983230072969 + 3 ^ 40 * 6651165 * 2
def baseEnd_6651165 : Nat := 3415244557361575020049355

theorem tailTrace_6651165 : CollatzResearch.WordTrace tailWord_6651165 prefixEnd_6651165 3415244557361575020049355 := by
  unfold tailWord_6651165
  simp only [CollatzResearch.WordTrace]
  refine ⟨242587916948972608391218949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161725277965981738927479299 242587916948972608391218949)
  ·
    refine ⟨45485234427932364073353553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242587916948972608391218949 45485234427932364073353553)
    ·
      refine ⟨34113925820949273055015165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45485234427932364073353553 34113925820949273055015165)
      ·
        refine ⟨12792722182855977395630687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34113925820949273055015165 12792722182855977395630687)
        ·
          refine ⟨19189083274283966093446031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792722182855977395630687 19189083274283966093446031)
          ·
            refine ⟨28783624911425949140169047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189083274283966093446031 28783624911425949140169047)
            ·
              refine ⟨43175437367138923710253571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28783624911425949140169047 43175437367138923710253571)
              ·
                refine ⟨64763156050708385565380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43175437367138923710253571 64763156050708385565380357)
                ·
                  refine ⟨12143091759507822293508817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64763156050708385565380357 12143091759507822293508817)
                  ·
                    refine ⟨9107318819630866720131613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12143091759507822293508817 9107318819630866720131613)
                    ·
                      refine ⟨3415244557361575020049355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107318819630866720131613 3415244557361575020049355)
                      ·
                        rfl

theorem cell23_6651165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6651165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651165 prefixEnd_6651165 := by exact prefixLift 6651165
  have htrace : WordTrace (prefixWord ++ tailWord_6651165) baseStart_6651165 baseEnd_6651165 := by
    simpa [prefixWord, tailWord_6651165, baseEnd_6651165] using wordTrace_append hprefix tailTrace_6651165
  have hstable : (prefixWord ++ tailWord_6651165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651165).length < 2 ^ (prefixWord ++ tailWord_6651165).sum := by decide
  have hdescent : baseEnd_6651165 < baseStart_6651165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651185 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 6]
def baseStart_6651185 : Nat := 118140960795 + 6651185 * 2 ^ 59
def prefixEnd_6651185 : Nat := 4983230072969 + 3 ^ 40 * 6651185 * 2
def baseEnd_6651185 : Nat := 379472758552740549088807

theorem tailTrace_6651185 : CollatzResearch.WordTrace tailWord_6651185 prefixEnd_6651185 379472758552740549088807 := by
  unfold tailWord_6651185
  simp only [CollatzResearch.WordTrace]
  refine ⟨242588646408900151806947009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161725764272600101204631339 242588646408900151806947009)
  ·
    refine ⟨181941484806675113855210257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242588646408900151806947009 181941484806675113855210257)
    ·
      refine ⟨136456113605006335391407693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181941484806675113855210257 136456113605006335391407693)
      ·
        refine ⟨51171042601877375771777885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136456113605006335391407693 51171042601877375771777885)
        ·
          refine ⟨19189140975704015914416707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51171042601877375771777885 19189140975704015914416707)
          ·
            refine ⟨28783711463556023871625061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189140975704015914416707 28783711463556023871625061)
            ·
              refine ⟨5396945899416754475929699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28783711463556023871625061 5396945899416754475929699)
              ·
                refine ⟨8095418849125131713894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396945899416754475929699 8095418849125131713894549)
                ·
                  refine ⟨379472758552740549088807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8095418849125131713894549 379472758552740549088807)
                  ·
                    rfl

theorem cell23_6651185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_6651185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651185 prefixEnd_6651185 := by exact prefixLift 6651185
  have htrace : WordTrace (prefixWord ++ tailWord_6651185) baseStart_6651185 baseEnd_6651185 := by
    simpa [prefixWord, tailWord_6651185, baseEnd_6651185] using wordTrace_append hprefix tailTrace_6651185
  have hstable : (prefixWord ++ tailWord_6651185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651185).length < 2 ^ (prefixWord ++ tailWord_6651185).sum := by decide
  have hdescent : baseEnd_6651185 < baseStart_6651185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651241 : List Nat := [1, 2, 1, 1, 1, 3, 2, 12]
def baseStart_6651241 : Nat := 118140960795 + 6651241 * 2 ^ 59
def prefixEnd_6651241 : Nat := 4983230072969 + 3 ^ 40 * 6651241 * 2
def baseEnd_6651241 : Nat := 126491984514493211951815

theorem tailTrace_6651241 : CollatzResearch.WordTrace tailWord_6651241 prefixEnd_6651241 126491984514493211951815 := by
  unfold tailWord_6651241
  simp only [CollatzResearch.WordTrace]
  refine ⟨242590688896697273370985577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161727125931131515580657051 242590688896697273370985577)
  ·
    refine ⟨181943016672522955028239183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242590688896697273370985577 181943016672522955028239183)
    ·
      refine ⟨272914525008784432542358775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181943016672522955028239183 272914525008784432542358775)
      ·
        refine ⟨409371787513176648813538163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272914525008784432542358775 409371787513176648813538163)
        ·
          refine ⟨614057681269764973220307245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409371787513176648813538163 614057681269764973220307245)
          ·
            refine ⟨230271630476161864957615217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614057681269764973220307245 230271630476161864957615217)
            ·
              refine ⟨172703722857121398718211413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230271630476161864957615217 172703722857121398718211413)
              ·
                refine ⟨126491984514493211951815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 172703722857121398718211413 126491984514493211951815)
                ·
                  rfl

theorem cell23_6651241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 12].length) (baseStart_6651241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651241 prefixEnd_6651241 := by exact prefixLift 6651241
  have htrace : WordTrace (prefixWord ++ tailWord_6651241) baseStart_6651241 baseEnd_6651241 := by
    simpa [prefixWord, tailWord_6651241, baseEnd_6651241] using wordTrace_append hprefix tailTrace_6651241
  have hstable : (prefixWord ++ tailWord_6651241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651241).length < 2 ^ (prefixWord ++ tailWord_6651241).sum := by decide
  have hdescent : baseEnd_6651241 < baseStart_6651241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651245 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_6651245 : Nat := 118140960795 + 6651245 * 2 ^ 59
def prefixEnd_6651245 : Nat := 4983230072969 + 3 ^ 40 * 6651245 * 2
def baseEnd_6651245 : Nat := 1138428545271311569016329

theorem tailTrace_6651245 : CollatzResearch.WordTrace tailWord_6651245 prefixEnd_6651245 1138428545271311569016329 := by
  unfold tailWord_6651245
  simp only [CollatzResearch.WordTrace]
  refine ⟨242590834788682782054131189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161727223192455188036087459 242590834788682782054131189)
  ·
    refine ⟨22742890761439010817574799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242590834788682782054131189 22742890761439010817574799)
    ·
      refine ⟨34114336142158516226362199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22742890761439010817574799 34114336142158516226362199)
      ·
        refine ⟨51171504213237774339543299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34114336142158516226362199 51171504213237774339543299)
        ·
          refine ⟨76757256319856661509314949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51171504213237774339543299 76757256319856661509314949)
          ·
            refine ⟨14391985559973124032996553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76757256319856661509314949 14391985559973124032996553)
            ·
              refine ⟨10793989169979843024747415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14391985559973124032996553 10793989169979843024747415)
              ·
                refine ⟨16190983754969764537121123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793989169979843024747415 16190983754969764537121123)
                ·
                  refine ⟨24286475632454646805681685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16190983754969764537121123 24286475632454646805681685)
                  ·
                    refine ⟨1138428545271311569016329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24286475632454646805681685 1138428545271311569016329)
                    ·
                      rfl

theorem cell23_6651245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_6651245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651245 prefixEnd_6651245 := by exact prefixLift 6651245
  have htrace : WordTrace (prefixWord ++ tailWord_6651245) baseStart_6651245 baseEnd_6651245 := by
    simpa [prefixWord, tailWord_6651245, baseEnd_6651245] using wordTrace_append hprefix tailTrace_6651245
  have hstable : (prefixWord ++ tailWord_6651245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651245).length < 2 ^ (prefixWord ++ tailWord_6651245).sum := by decide
  have hdescent : baseEnd_6651245 < baseStart_6651245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651255 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_6651255 : Nat := 118140960795 + 6651255 * 2 ^ 59
def prefixEnd_6651255 : Nat := 4983230072969 + 3 ^ 40 * 6651255 * 2
def baseEnd_6651255 : Nat := 3415290770620479667923941

theorem tailTrace_6651255 : CollatzResearch.WordTrace tailWord_6651255 prefixEnd_6651255 3415290770620479667923941 := by
  unfold tailWord_6651255
  simp only [CollatzResearch.WordTrace]
  refine ⟨242591199518646553761995219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161727466345764369174663479 242591199518646553761995219)
  ·
    refine ⟨363886799277969830642992829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242591199518646553761995219 363886799277969830642992829)
    ·
      refine ⟨136457549729238686491122311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363886799277969830642992829 136457549729238686491122311)
      ·
        refine ⟨204686324593858029736683467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136457549729238686491122311 204686324593858029736683467)
        ·
          refine ⟨307029486890787044605025201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204686324593858029736683467 307029486890787044605025201)
          ·
            refine ⟨230272115168090283453768901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307029486890787044605025201 230272115168090283453768901)
            ·
              refine ⟨43176021594016928147581669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230272115168090283453768901 43176021594016928147581669)
              ·
                refine ⟨8095504048878174027671563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43176021594016928147581669 8095504048878174027671563)
                ·
                  refine ⟨12143256073317261041507345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095504048878174027671563 12143256073317261041507345)
                  ·
                    refine ⟨9107442054987945781130509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12143256073317261041507345 9107442054987945781130509)
                    ·
                      refine ⟨3415290770620479667923941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107442054987945781130509 3415290770620479667923941)
                      ·
                        rfl

theorem cell23_6651255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_6651255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651255 prefixEnd_6651255 := by exact prefixLift 6651255
  have htrace : WordTrace (prefixWord ++ tailWord_6651255) baseStart_6651255 baseEnd_6651255 := by
    simpa [prefixWord, tailWord_6651255, baseEnd_6651255] using wordTrace_append hprefix tailTrace_6651255
  have hstable : (prefixWord ++ tailWord_6651255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651255).length < 2 ^ (prefixWord ++ tailWord_6651255).sum := by decide
  have hdescent : baseEnd_6651255 < baseStart_6651255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651266 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6651266 : Nat := 118140960795 + 6651266 * 2 ^ 59
def prefixEnd_6651266 : Nat := 4983230072969 + 3 ^ 40 * 6651266 * 2
def baseEnd_6651266 : Nat := 1138432139635893041628797

theorem tailTrace_6651266 : CollatzResearch.WordTrace tailWord_6651266 prefixEnd_6651266 1138432139635893041628797 := by
  unfold tailWord_6651266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60647900180401675660161413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161727733814404468427097101 60647900180401675660161413)
  ·
    refine ⟨11371481283825314186280265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60647900180401675660161413 11371481283825314186280265)
    ·
      refine ⟨8528610962868985639710199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11371481283825314186280265 8528610962868985639710199)
      ·
        refine ⟨12792916444303478459565299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528610962868985639710199 12792916444303478459565299)
        ·
          refine ⟨19189374666455217689347949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792916444303478459565299 19189374666455217689347949)
          ·
            refine ⟨7196015499920706633505481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19189374666455217689347949 7196015499920706633505481)
            ·
              refine ⟨5397011624940529975129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7196015499920706633505481 5397011624940529975129111)
              ·
                refine ⟨8095517437410794962693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397011624940529975129111 8095517437410794962693667)
                ·
                  refine ⟨12143276156116192444040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095517437410794962693667 12143276156116192444040501)
                  ·
                    refine ⟨1138432139635893041628797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12143276156116192444040501 1138432139635893041628797)
                    ·
                      rfl

theorem cell23_6651266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6651266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651266 prefixEnd_6651266 := by exact prefixLift 6651266
  have htrace : WordTrace (prefixWord ++ tailWord_6651266) baseStart_6651266 baseEnd_6651266 := by
    simpa [prefixWord, tailWord_6651266, baseEnd_6651266] using wordTrace_append hprefix tailTrace_6651266
  have hstable : (prefixWord ++ tailWord_6651266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651266).length < 2 ^ (prefixWord ++ tailWord_6651266).sum := by decide
  have hdescent : baseEnd_6651266 < baseStart_6651266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651269 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_6651269 : Nat := 118140960795 + 6651269 * 2 ^ 59
def prefixEnd_6651269 : Nat := 4983230072969 + 3 ^ 40 * 6651269 * 2
def baseEnd_6651269 : Nat := 3415297959349642613148877

theorem tailTrace_6651269 : CollatzResearch.WordTrace tailWord_6651269 prefixEnd_6651269 3415297959349642613148877 := by
  unfold tailWord_6651269
  simp only [CollatzResearch.WordTrace]
  refine ⟨242591710140595834153004861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161727806760397222768669907 242591710140595834153004861)
  ·
    refine ⟨90971891302723437807376823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242591710140595834153004861 90971891302723437807376823)
    ·
      refine ⟨136457836954085156711065235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90971891302723437807376823 136457836954085156711065235)
      ·
        refine ⟨204686755431127735066597853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136457836954085156711065235 204686755431127735066597853)
        ·
          refine ⟨76757533286672900649974195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204686755431127735066597853 76757533286672900649974195)
          ·
            refine ⟨115136299930009350974961293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76757533286672900649974195 115136299930009350974961293)
            ·
              refine ⟨43176112473753506615610485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115136299930009350974961293 43176112473753506615610485)
              ·
                refine ⟨4047760544414391245213483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43176112473753506615610485 4047760544414391245213483)
                ·
                  refine ⟨6071640816621586867820225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047760544414391245213483 6071640816621586867820225)
                  ·
                    refine ⟨4553730612466190150865169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071640816621586867820225 4553730612466190150865169)
                    ·
                      refine ⟨3415297959349642613148877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553730612466190150865169 3415297959349642613148877)
                      ·
                        rfl

theorem cell23_6651269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_6651269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651269 prefixEnd_6651269 := by exact prefixLift 6651269
  have htrace : WordTrace (prefixWord ++ tailWord_6651269) baseStart_6651269 baseEnd_6651269 := by
    simpa [prefixWord, tailWord_6651269, baseEnd_6651269] using wordTrace_append hprefix tailTrace_6651269
  have hstable : (prefixWord ++ tailWord_6651269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651269).length < 2 ^ (prefixWord ++ tailWord_6651269).sum := by decide
  have hdescent : baseEnd_6651269 < baseStart_6651269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651272 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6651272 : Nat := 118140960795 + 6651272 * 2 ^ 59
def prefixEnd_6651272 : Nat := 4983230072969 + 3 ^ 40 * 6651272 * 2
def baseEnd_6651272 : Nat := 3415299499791606101411363

theorem tailTrace_6651272 : CollatzResearch.WordTrace tailWord_6651272 prefixEnd_6651272 3415299499791606101411363 := by
  unfold tailWord_6651272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121295909779792482832682035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161727879706389977110242713 121295909779792482832682035)
  ·
    refine ⟨181943864669688724249023053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121295909779792482832682035 181943864669688724249023053)
    ·
      refine ⟨68228949251133271593383645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181943864669688724249023053 68228949251133271593383645)
      ·
        refine ⟨25585855969174976847518867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68228949251133271593383645 25585855969174976847518867)
        ·
          refine ⟨38378783953762465271278301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25585855969174976847518867 38378783953762465271278301)
          ·
            refine ⟨14392043982660924476729363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38378783953762465271278301 14392043982660924476729363)
            ·
              refine ⟨21588065973991386715094045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392043982660924476729363 21588065973991386715094045)
              ·
                refine ⟨8095524740246770018160267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21588065973991386715094045 8095524740246770018160267)
                ·
                  refine ⟨12143287110370155027240401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095524740246770018160267 12143287110370155027240401)
                  ·
                    refine ⟨9107465332777616270430301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12143287110370155027240401 9107465332777616270430301)
                    ·
                      refine ⟨3415299499791606101411363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107465332777616270430301 3415299499791606101411363)
                      ·
                        rfl

theorem cell23_6651272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6651272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651272 prefixEnd_6651272 := by exact prefixLift 6651272
  have htrace : WordTrace (prefixWord ++ tailWord_6651272) baseStart_6651272 baseEnd_6651272 := by
    simpa [prefixWord, tailWord_6651272, baseEnd_6651272] using wordTrace_append hprefix tailTrace_6651272
  have hstable : (prefixWord ++ tailWord_6651272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651272).length < 2 ^ (prefixWord ++ tailWord_6651272).sum := by decide
  have hdescent : baseEnd_6651272 < baseStart_6651272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651308 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_6651308 : Nat := 118140960795 + 6651308 * 2 ^ 59
def prefixEnd_6651308 : Nat := 4983230072969 + 3 ^ 40 * 6651308 * 2
def baseEnd_6651308 : Nat := 3415317985095167960561197

theorem tailTrace_6651308 : CollatzResearch.WordTrace tailWord_6651308 prefixEnd_6651308 3415317985095167960561197 := by
  unfold tailWord_6651308
  simp only [CollatzResearch.WordTrace]
  refine ⟨121296566293727271906837289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161728755058303029209116385 121296566293727271906837289)
  ·
    refine ⟨90972424720295453930127967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121296566293727271906837289 90972424720295453930127967)
    ·
      refine ⟨136458637080443180895191951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90972424720295453930127967 136458637080443180895191951)
      ·
        refine ⟨204687955620664771342787927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136458637080443180895191951 204687955620664771342787927)
        ·
          refine ⟨307031933430997157014181891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204687955620664771342787927 307031933430997157014181891)
          ·
            refine ⟨460547900146495735521272837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307031933430997157014181891 460547900146495735521272837)
            ·
              refine ⟨86352731277467950410238657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460547900146495735521272837 86352731277467950410238657)
              ·
                refine ⟨64764548458100962807678993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86352731277467950410238657 64764548458100962807678993)
                ·
                  refine ⟨48573411343575722105759245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64764548458100962807678993 48573411343575722105759245)
                  ·
                    refine ⟨18215029253840895789659717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48573411343575722105759245 18215029253840895789659717)
                    ·
                      refine ⟨3415317985095167960561197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18215029253840895789659717 3415317985095167960561197)
                      ·
                        rfl

theorem cell23_6651308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_6651308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651308 prefixEnd_6651308 := by exact prefixLift 6651308
  have htrace : WordTrace (prefixWord ++ tailWord_6651308) baseStart_6651308 baseEnd_6651308 := by
    simpa [prefixWord, tailWord_6651308, baseEnd_6651308] using wordTrace_append hprefix tailTrace_6651308
  have hstable : (prefixWord ++ tailWord_6651308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651308).length < 2 ^ (prefixWord ++ tailWord_6651308).sum := by decide
  have hdescent : baseEnd_6651308 < baseStart_6651308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651328 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_6651328 : Nat := 118140960795 + 6651328 * 2 ^ 59
def prefixEnd_6651328 : Nat := 4983230072969 + 3 ^ 40 * 6651328 * 2
def baseEnd_6651328 : Nat := 3415328254708257882311105

theorem tailTrace_6651328 : CollatzResearch.WordTrace tailWord_6651328 prefixEnd_6651328 3415328254708257882311105 := by
  unfold tailWord_6651328
  simp only [CollatzResearch.WordTrace]
  refine ⟨121296931023691043614701319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161729241364921391486268425 121296931023691043614701319)
  ·
    refine ⟨181945396535536565422051979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121296931023691043614701319 181945396535536565422051979)
    ·
      refine ⟨272918094803304848133077969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181945396535536565422051979 272918094803304848133077969)
      ·
        refine ⟨204688571102478636099808477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272918094803304848133077969 204688571102478636099808477)
        ·
          refine ⟨76758214163429488537428179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204688571102478636099808477 76758214163429488537428179)
          ·
            refine ⟨115137321245144232806142269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76758214163429488537428179 115137321245144232806142269)
            ·
              refine ⟨43176495466929087302303351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115137321245144232806142269 43176495466929087302303351)
              ·
                refine ⟨64764743200393630953455027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43176495466929087302303351 64764743200393630953455027)
                ·
                  refine ⟨97147114800590446430182541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64764743200393630953455027 97147114800590446430182541)
                  ·
                    refine ⟨36430168050221417411318453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97147114800590446430182541 36430168050221417411318453)
                    ·
                      refine ⟨3415328254708257882311105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36430168050221417411318453 3415328254708257882311105)
                      ·
                        rfl

theorem cell23_6651328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_6651328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651328 prefixEnd_6651328 := by exact prefixLift 6651328
  have htrace : WordTrace (prefixWord ++ tailWord_6651328) baseStart_6651328 baseEnd_6651328 := by
    simpa [prefixWord, tailWord_6651328, baseEnd_6651328] using wordTrace_append hprefix tailTrace_6651328
  have hstable : (prefixWord ++ tailWord_6651328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651328).length < 2 ^ (prefixWord ++ tailWord_6651328).sum := by decide
  have hdescent : baseEnd_6651328 < baseStart_6651328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651359 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 2, 2, 2]
def baseStart_6651359 : Nat := 118140960795 + 6651359 * 2 ^ 59
def prefixEnd_6651359 : Nat := 4983230072969 + 3 ^ 40 * 6651359 * 2
def baseEnd_6651359 : Nat := 3415344172608547261023463

theorem tailTrace_6651359 : CollatzResearch.WordTrace tailWord_6651359 prefixEnd_6651359 3415344172608547261023463 := by
  unfold tailWord_6651359
  simp only [CollatzResearch.WordTrace]
  refine ⟨242594992710269779523781131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161729995140179853015854087 242594992710269779523781131)
  ·
    refine ⟨363892489065404669285671697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242594992710269779523781131 363892489065404669285671697)
    ·
      refine ⟨272919366799053501964253773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363892489065404669285671697 272919366799053501964253773)
      ·
        refine ⟨102344762549645063236595165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272919366799053501964253773 102344762549645063236595165)
        ·
          refine ⟨38379285956116898713723187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102344762549645063236595165 38379285956116898713723187)
          ·
            refine ⟨57568928934175348070584781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38379285956116898713723187 57568928934175348070584781)
            ·
              refine ⟨21588348350315755526469293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57568928934175348070584781 21588348350315755526469293)
              ·
                refine ⟨8095630631368408322425985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21588348350315755526469293 8095630631368408322425985)
                ·
                  refine ⟨6071722973526306241819489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095630631368408322425985 6071722973526306241819489)
                  ·
                    refine ⟨4553792230144729681364617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071722973526306241819489 4553792230144729681364617)
                    ·
                      refine ⟨3415344172608547261023463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553792230144729681364617 3415344172608547261023463)
                      ·
                        rfl

theorem cell23_6651359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_6651359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651359 prefixEnd_6651359 := by exact prefixLift 6651359
  have htrace : WordTrace (prefixWord ++ tailWord_6651359) baseStart_6651359 baseEnd_6651359 := by
    simpa [prefixWord, tailWord_6651359, baseEnd_6651359] using wordTrace_append hprefix tailTrace_6651359
  have hstable : (prefixWord ++ tailWord_6651359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651359).length < 2 ^ (prefixWord ++ tailWord_6651359).sum := by decide
  have hdescent : baseEnd_6651359 < baseStart_6651359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651399 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 5]
def baseStart_6651399 : Nat := 118140960795 + 6651399 * 2 ^ 59
def prefixEnd_6651399 : Nat := 4983230072969 + 3 ^ 40 * 6651399 * 2
def baseEnd_6651399 : Nat := 379484967981636344947031

theorem tailTrace_6651399 : CollatzResearch.WordTrace tailWord_6651399 prefixEnd_6651399 379484967981636344947031 := by
  unfold tailWord_6651399
  simp only [CollatzResearch.WordTrace]
  refine ⟨242596451630124866355237251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161730967753416577570158167 242596451630124866355237251)
  ·
    refine ⟨363894677445187299532855877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242596451630124866355237251 363894677445187299532855877)
    ·
      refine ⟨68230252020972618662410477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363894677445187299532855877 68230252020972618662410477)
      ·
        refine ⟨25586344507864731998403929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68230252020972618662410477 25586344507864731998403929)
        ·
          refine ⟨19189758380898548998802947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25586344507864731998403929 19189758380898548998802947)
          ·
            refine ⟨28784637571347823498204421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189758380898548998802947 28784637571347823498204421)
            ·
              refine ⟨5397119544627716905913329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28784637571347823498204421 5397119544627716905913329)
              ·
                refine ⟨4047839658470787679434997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397119544627716905913329 4047839658470787679434997)
                ·
                  refine ⟨379484967981636344947031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047839658470787679434997 379484967981636344947031)
                  ·
                    rfl

theorem cell23_6651399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 5].length) (baseStart_6651399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651399 prefixEnd_6651399 := by exact prefixLift 6651399
  have htrace : WordTrace (prefixWord ++ tailWord_6651399) baseStart_6651399 baseEnd_6651399 := by
    simpa [prefixWord, tailWord_6651399, baseEnd_6651399] using wordTrace_append hprefix tailTrace_6651399
  have hstable : (prefixWord ++ tailWord_6651399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651399).length < 2 ^ (prefixWord ++ tailWord_6651399).sum := by decide
  have hdescent : baseEnd_6651399 < baseStart_6651399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651402 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_6651402 : Nat := 118140960795 + 6651402 * 2 ^ 59
def prefixEnd_6651402 : Nat := 4983230072969 + 3 ^ 40 * 6651402 * 2
def baseEnd_6651402 : Nat := 3415366252276690592785765

theorem tailTrace_6651402 : CollatzResearch.WordTrace tailWord_6651402 prefixEnd_6651402 3415366252276690592785765 := by
  unfold tailWord_6651402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60649140262278499466899115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161731040699409331911730973 60649140262278499466899115)
  ·
    refine ⟨90973710393417749200348673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60649140262278499466899115 90973710393417749200348673)
    ·
      refine ⟨68230282795063311900261505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90973710393417749200348673 68230282795063311900261505)
      ·
        refine ⟨51172712096297483925196129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68230282795063311900261505 51172712096297483925196129)
        ·
          refine ⟨38379534072223112943897097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51172712096297483925196129 38379534072223112943897097)
          ·
            refine ⟨28784650554167334707922823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38379534072223112943897097 28784650554167334707922823)
            ·
              refine ⟨43176975831251002061884235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28784650554167334707922823 43176975831251002061884235)
              ·
                refine ⟨64765463746876503092826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43176975831251002061884235 64765463746876503092826353)
                ·
                  refine ⟨48574097810157377319619765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64765463746876503092826353 48574097810157377319619765)
                  ·
                    refine ⟨4553821669702254123714353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48574097810157377319619765 4553821669702254123714353)
                    ·
                      refine ⟨3415366252276690592785765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553821669702254123714353 3415366252276690592785765)
                      ·
                        rfl

theorem cell23_6651402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_6651402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651402 prefixEnd_6651402 := by exact prefixLift 6651402
  have htrace : WordTrace (prefixWord ++ tailWord_6651402) baseStart_6651402 baseEnd_6651402 := by
    simpa [prefixWord, tailWord_6651402, baseEnd_6651402] using wordTrace_append hprefix tailTrace_6651402
  have hstable : (prefixWord ++ tailWord_6651402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651402).length < 2 ^ (prefixWord ++ tailWord_6651402).sum := by decide
  have hdescent : baseEnd_6651402 < baseStart_6651402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651445 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_6651445 : Nat := 118140960795 + 6651445 * 2 ^ 59
def prefixEnd_6651445 : Nat := 4983230072969 + 3 ^ 40 * 6651445 * 2
def baseEnd_6651445 : Nat := 3415388331944833924548067

theorem tailTrace_6651445 : CollatzResearch.WordTrace tailWord_6651445 prefixEnd_6651445 3415388331944833924548067 := by
  unfold tailWord_6651445
  simp only [CollatzResearch.WordTrace]
  refine ⟨242598129387958216211411789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161732086258638810807607859 242598129387958216211411789)
  ·
    refine ⟨90974298520484331079279421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242598129387958216211411789 90974298520484331079279421)
    ·
      refine ⟨34115361945181624154729783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90974298520484331079279421 34115361945181624154729783)
      ·
        refine ⟨51173042917772436232094675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34115361945181624154729783 51173042917772436232094675)
        ·
          refine ⟨76759564376658654348142013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51173042917772436232094675 76759564376658654348142013)
          ·
            refine ⟨28784836641246995380553255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76759564376658654348142013 28784836641246995380553255)
            ·
              refine ⟨43177254961870493070829883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28784836641246995380553255 43177254961870493070829883)
              ·
                refine ⟨64765882442805739606244825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43177254961870493070829883 64765882442805739606244825)
                ·
                  refine ⟨48574411832104304704683619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64765882442805739606244825 48574411832104304704683619)
                  ·
                    refine ⟨72861617748156457057025429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48574411832104304704683619 72861617748156457057025429)
                    ·
                      refine ⟨3415388331944833924548067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72861617748156457057025429 3415388331944833924548067)
                      ·
                        rfl

theorem cell23_6651445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_6651445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651445 prefixEnd_6651445 := by exact prefixLift 6651445
  have htrace : WordTrace (prefixWord ++ tailWord_6651445) baseStart_6651445 baseEnd_6651445 := by
    simpa [prefixWord, tailWord_6651445, baseEnd_6651445] using wordTrace_append hprefix tailTrace_6651445
  have hstable : (prefixWord ++ tailWord_6651445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651445).length < 2 ^ (prefixWord ++ tailWord_6651445).sum := by decide
  have hdescent : baseEnd_6651445 < baseStart_6651445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651455 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 8]
def baseStart_6651455 : Nat := 118140960795 + 6651455 * 2 ^ 59
def prefixEnd_6651455 : Nat := 4983230072969 + 3 ^ 40 * 6651455 * 2
def baseEnd_6651455 : Nat := 379488162972375431713669

theorem tailTrace_6651455 : CollatzResearch.WordTrace tailWord_6651455 prefixEnd_6651455 379488162972375431713669 := by
  unfold tailWord_6651455
  simp only [CollatzResearch.WordTrace]
  refine ⟨242598494117921987919275819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161732329411947991946183879 242598494117921987919275819)
  ·
    refine ⟨363897741176882981878913729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242598494117921987919275819 363897741176882981878913729)
    ·
      refine ⟨272923305882662236409185297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363897741176882981878913729 272923305882662236409185297)
      ·
        refine ⟨204692479411996677306888973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272923305882662236409185297 204692479411996677306888973)
        ·
          refine ⟨76759679779498753990083365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204692479411996677306888973 76759679779498753990083365)
          ·
            refine ⟨14392439958656016373140631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76759679779498753990083365 14392439958656016373140631)
            ·
              refine ⟨21588659937984024559710947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392439958656016373140631 21588659937984024559710947)
              ·
                refine ⟨32382989906976036839566421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21588659937984024559710947 32382989906976036839566421)
                ·
                  refine ⟨379488162972375431713669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32382989906976036839566421 379488162972375431713669)
                  ·
                    rfl

theorem cell23_6651455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 8].length) (baseStart_6651455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651455 prefixEnd_6651455 := by exact prefixLift 6651455
  have htrace : WordTrace (prefixWord ++ tailWord_6651455) baseStart_6651455 baseEnd_6651455 := by
    simpa [prefixWord, tailWord_6651455, baseEnd_6651455] using wordTrace_append hprefix tailTrace_6651455
  have hstable : (prefixWord ++ tailWord_6651455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651455).length < 2 ^ (prefixWord ++ tailWord_6651455).sum := by decide
  have hdescent : baseEnd_6651455 < baseStart_6651455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651472 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 6]
def baseStart_6651472 : Nat := 118140960795 + 6651472 * 2 ^ 59
def prefixEnd_6651472 : Nat := 4983230072969 + 3 ^ 40 * 6651472 * 2
def baseEnd_6651472 : Nat := 379489132880278368767827

theorem tailTrace_6651472 : CollatzResearch.WordTrace tailWord_6651472 prefixEnd_6651472 379489132880278368767827 := by
  unfold tailWord_6651472
  simp only [CollatzResearch.WordTrace]
  refine ⟨121299557079430199911322335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161732742772573599881763113 121299557079430199911322335)
  ·
    refine ⟨181949335619145299866983503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121299557079430199911322335 181949335619145299866983503)
    ·
      refine ⟨272924003428717949800475255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181949335619145299866983503 272924003428717949800475255)
      ·
        refine ⟨409386005143076924700712883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272924003428717949800475255 409386005143076924700712883)
        ·
          refine ⟨614079007714615387051069325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409386005143076924700712883 614079007714615387051069325)
          ·
            refine ⟨230279627892980770144150997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614079007714615387051069325 230279627892980770144150997)
            ·
              refine ⟨5397178778741736800253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230279627892980770144150997 5397178778741736800253539)
              ·
                refine ⟨8095768168112605200380309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397178778741736800253539 8095768168112605200380309)
                ·
                  refine ⟨379489132880278368767827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8095768168112605200380309 379489132880278368767827)
                  ·
                    rfl

theorem cell23_6651472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_6651472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651472 prefixEnd_6651472 := by exact prefixLift 6651472
  have htrace : WordTrace (prefixWord ++ tailWord_6651472) baseStart_6651472 baseEnd_6651472 := by
    simpa [prefixWord, tailWord_6651472, baseEnd_6651472] using wordTrace_append hprefix tailTrace_6651472
  have hstable : (prefixWord ++ tailWord_6651472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651472).length < 2 ^ (prefixWord ++ tailWord_6651472).sum := by decide
  have hdescent : baseEnd_6651472 < baseStart_6651472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651552 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6651552 : Nat := 118140960795 + 6651552 * 2 ^ 59
def prefixEnd_6651552 : Nat := 4983230072969 + 3 ^ 40 * 6651552 * 2
def baseEnd_6651552 : Nat := 3415443274374865005910075

theorem tailTrace_6651552 : CollatzResearch.WordTrace tailWord_6651552 prefixEnd_6651552 3415443274374865005910075 := by
  unfold tailWord_6651552
  simp only [CollatzResearch.WordTrace]
  refine ⟨121301015999285286742778455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161734687999047048990371273 121301015999285286742778455)
  ·
    refine ⟨181951523998927930114167683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121301015999285286742778455 181951523998927930114167683)
    ·
      refine ⟨272927285998391895171251525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181951523998927930114167683 272927285998391895171251525)
      ·
        refine ⟨51173866124698480344609661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272927285998391895171251525 51173866124698480344609661)
        ·
          refine ⟨19190199796761930129228623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51173866124698480344609661 19190199796761930129228623)
          ·
            refine ⟨28785299695142895193842935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19190199796761930129228623 28785299695142895193842935)
            ·
              refine ⟨43177949542714342790764403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28785299695142895193842935 43177949542714342790764403)
              ·
                refine ⟨64766924314071514186146605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43177949542714342790764403 64766924314071514186146605)
                ·
                  refine ⟨24287596617776817819804977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64766924314071514186146605 24287596617776817819804977)
                  ·
                    refine ⟨18215697463332613364853733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24287596617776817819804977 18215697463332613364853733)
                    ·
                      refine ⟨3415443274374865005910075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18215697463332613364853733 3415443274374865005910075)
                      ·
                        rfl

theorem cell23_6651552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6651552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651552 prefixEnd_6651552 := by exact prefixLift 6651552
  have htrace : WordTrace (prefixWord ++ tailWord_6651552) baseStart_6651552 baseEnd_6651552 := by
    simpa [prefixWord, tailWord_6651552, baseEnd_6651552] using wordTrace_append hprefix tailTrace_6651552
  have hstable : (prefixWord ++ tailWord_6651552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651552).length < 2 ^ (prefixWord ++ tailWord_6651552).sum := by decide
  have hdescent : baseEnd_6651552 < baseStart_6651552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651556 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_6651556 : Nat := 118140960795 + 6651556 * 2 ^ 59
def prefixEnd_6651556 : Nat := 4983230072969 + 3 ^ 40 * 6651556 * 2
def baseEnd_6651556 : Nat := 3415445328297482990260057

theorem tailTrace_6651556 : CollatzResearch.WordTrace tailWord_6651556 prefixEnd_6651556 3415445328297482990260057 := by
  unfold tailWord_6651556
  simp only [CollatzResearch.WordTrace]
  refine ⟨121301088945278041084351261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161734785260370721445801681 121301088945278041084351261)
  ·
    refine ⟨45487908354479265406631723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121301088945278041084351261 45487908354479265406631723)
    ·
      refine ⟨68231862531718898109947585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45487908354479265406631723 68231862531718898109947585)
      ·
        refine ⟨51173896898789173582460689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68231862531718898109947585 51173896898789173582460689)
        ·
          refine ⟨38380422674091880186845517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51173896898789173582460689 38380422674091880186845517)
          ·
            refine ⟨14392658502784455070067069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38380422674091880186845517 14392658502784455070067069)
            ·
              refine ⟨5397246938544170651275151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14392658502784455070067069 5397246938544170651275151)
              ·
                refine ⟨8095870407816255976912727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397246938544170651275151 8095870407816255976912727)
                ·
                  refine ⟨12143805611724383965369091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095870407816255976912727 12143805611724383965369091)
                  ·
                    refine ⟨18215708417586575948053637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12143805611724383965369091 18215708417586575948053637)
                    ·
                      refine ⟨3415445328297482990260057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18215708417586575948053637 3415445328297482990260057)
                      ·
                        rfl

theorem cell23_6651556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_6651556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651556 prefixEnd_6651556 := by exact prefixLift 6651556
  have htrace : WordTrace (prefixWord ++ tailWord_6651556) baseStart_6651556 baseEnd_6651556 := by
    simpa [prefixWord, tailWord_6651556, baseEnd_6651556] using wordTrace_append hprefix tailTrace_6651556
  have hstable : (prefixWord ++ tailWord_6651556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651556).length < 2 ^ (prefixWord ++ tailWord_6651556).sum := by decide
  have hdescent : baseEnd_6651556 < baseStart_6651556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651590 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6651590 : Nat := 118140960795 + 6651590 * 2 ^ 59
def prefixEnd_6651590 : Nat := 4983230072969 + 3 ^ 40 * 6651590 * 2
def baseEnd_6651590 : Nat := 3415462786639735857234901

theorem tailTrace_6651590 : CollatzResearch.WordTrace tailWord_6651590 prefixEnd_6651590 3415462786639735857234901 := by
  unfold tailWord_6651590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581356811638528311732507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161735611981621937316960149 7581356811638528311732507)
  ·
    refine ⟨11372035217457792467598761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7581356811638528311732507 11372035217457792467598761)
    ·
      refine ⟨8529026413093344350699071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11372035217457792467598761 8529026413093344350699071)
      ·
        refine ⟨12793539619640016526048607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529026413093344350699071 12793539619640016526048607)
        ·
          refine ⟨19190309429460024789072911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793539619640016526048607 19190309429460024789072911)
          ·
            refine ⟨28785464144190037183609367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19190309429460024789072911 28785464144190037183609367)
            ·
              refine ⟨43178196216285055775414051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28785464144190037183609367 43178196216285055775414051)
              ·
                refine ⟨64767294324427583663121077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43178196216285055775414051 64767294324427583663121077)
                ·
                  refine ⟨6071933842915085968417601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64767294324427583663121077 6071933842915085968417601)
                  ·
                    refine ⟨4553950382186314476313201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071933842915085968417601 4553950382186314476313201)
                    ·
                      refine ⟨3415462786639735857234901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4553950382186314476313201 3415462786639735857234901)
                      ·
                        rfl

theorem cell23_6651590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6651590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651590 prefixEnd_6651590 := by exact prefixLift 6651590
  have htrace : WordTrace (prefixWord ++ tailWord_6651590) baseStart_6651590 baseEnd_6651590 := by
    simpa [prefixWord, tailWord_6651590, baseEnd_6651590] using wordTrace_append hprefix tailTrace_6651590
  have hstable : (prefixWord ++ tailWord_6651590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651590).length < 2 ^ (prefixWord ++ tailWord_6651590).sum := by decide
  have hdescent : baseEnd_6651590 < baseStart_6651590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651623 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6651623 : Nat := 118140960795 + 6651623 * 2 ^ 59
def prefixEnd_6651623 : Nat := 4983230072969 + 3 ^ 40 * 6651623 * 2
def baseEnd_6651623 : Nat := 3415479731501334228122249

theorem tailTrace_6651623 : CollatzResearch.WordTrace tailWord_6651623 prefixEnd_6651623 3415479731501334228122249 := by
  unfold tailWord_6651623
  simp only [CollatzResearch.WordTrace]
  refine ⟨242604621581313352611391523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161736414387542235074261015 242604621581313352611391523)
  ·
    refine ⟨363906932371970028917087285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242604621581313352611391523 363906932371970028917087285)
    ·
      refine ⟨34116274909872190210976933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363906932371970028917087285 34116274909872190210976933)
      ·
        refine ⟨6396801545601035664558175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34116274909872190210976933 6396801545601035664558175)
        ·
          refine ⟨9595202318401553496837263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396801545601035664558175 9595202318401553496837263)
          ·
            refine ⟨14392803477602330245255895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9595202318401553496837263 14392803477602330245255895)
            ·
              refine ⟨21589205216403495367883843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392803477602330245255895 21589205216403495367883843)
              ·
                refine ⟨32383807824605243051825765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21589205216403495367883843 32383807824605243051825765)
                ·
                  refine ⟨6071963967113483072217331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32383807824605243051825765 6071963967113483072217331)
                  ·
                    refine ⟨9107945950670224608325997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071963967113483072217331 9107945950670224608325997)
                    ·
                      refine ⟨3415479731501334228122249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107945950670224608325997 3415479731501334228122249)
                      ·
                        rfl

theorem cell23_6651623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6651623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651623 prefixEnd_6651623 := by exact prefixLift 6651623
  have htrace : WordTrace (prefixWord ++ tailWord_6651623) baseStart_6651623 baseEnd_6651623 := by
    simpa [prefixWord, tailWord_6651623, baseEnd_6651623] using wordTrace_append hprefix tailTrace_6651623
  have hstable : (prefixWord ++ tailWord_6651623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651623).length < 2 ^ (prefixWord ++ tailWord_6651623).sum := by decide
  have hdescent : baseEnd_6651623 < baseStart_6651623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651632 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_6651632 : Nat := 118140960795 + 6651632 * 2 ^ 59
def prefixEnd_6651632 : Nat := 4983230072969 + 3 ^ 40 * 6651632 * 2
def baseEnd_6651632 : Nat := 3415484352827224692909707

theorem tailTrace_6651632 : CollatzResearch.WordTrace tailWord_6651632 prefixEnd_6651632 3415484352827224692909707 := by
  unfold tailWord_6651632
  simp only [CollatzResearch.WordTrace]
  refine ⟨121302474919140373574234575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161736633225520498098979433 121302474919140373574234575)
  ·
    refine ⟨181953712378710560361351863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121302474919140373574234575 181953712378710560361351863)
    ·
      refine ⟨272930568568065840542027795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181953712378710560361351863 272930568568065840542027795)
      ·
        refine ⟨409395852852098760813041693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272930568568065840542027795 409395852852098760813041693)
        ·
          refine ⟨153523444819537035304890635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409395852852098760813041693 153523444819537035304890635)
          ·
            refine ⟨230285167229305552957335953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153523444819537035304890635 230285167229305552957335953)
            ·
              refine ⟨172713875421979164718001965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230285167229305552957335953 172713875421979164718001965)
              ·
                refine ⟨64767703283242186769250737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172713875421979164718001965 64767703283242186769250737)
                ·
                  refine ⟨48575777462431640076938053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64767703283242186769250737 48575777462431640076938053)
                  ·
                    refine ⟨9107958274205932514425885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48575777462431640076938053 9107958274205932514425885)
                    ·
                      refine ⟨3415484352827224692909707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9107958274205932514425885 3415484352827224692909707)
                      ·
                        rfl

theorem cell23_6651632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_6651632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651632 prefixEnd_6651632 := by exact prefixLift 6651632
  have htrace : WordTrace (prefixWord ++ tailWord_6651632) baseStart_6651632 baseEnd_6651632 := by
    simpa [prefixWord, tailWord_6651632, baseEnd_6651632] using wordTrace_append hprefix tailTrace_6651632
  have hstable : (prefixWord ++ tailWord_6651632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651632).length < 2 ^ (prefixWord ++ tailWord_6651632).sum := by decide
  have hdescent : baseEnd_6651632 < baseStart_6651632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651666 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6651666 : Nat := 118140960795 + 6651666 * 2 ^ 59
def prefixEnd_6651666 : Nat := 4983230072969 + 3 ^ 40 * 6651666 * 2
def baseEnd_6651666 : Nat := 3415501811169477559884551

theorem tailTrace_6651666 : CollatzResearch.WordTrace tailWord_6651666 prefixEnd_6651666 3415501811169477559884551 := by
  unfold tailWord_6651666
  simp only [CollatzResearch.WordTrace]
  refine ⟨60651547480039392738801713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161737459946771713970137901 60651547480039392738801713)
  ·
    refine ⟨45488660610029544554101285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60651547480039392738801713 45488660610029544554101285)
    ·
      refine ⟨8529123864380539603893991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45488660610029544554101285 8529123864380539603893991)
      ·
        refine ⟨12793685796570809405840987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529123864380539603893991 12793685796570809405840987)
        ·
          refine ⟨19190528694856214108761481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793685796570809405840987 19190528694856214108761481)
          ·
            refine ⟨14392896521142160581571111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19190528694856214108761481 14392896521142160581571111)
            ·
              refine ⟨21589344781713240872356667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392896521142160581571111 21589344781713240872356667)
              ·
                refine ⟨32384017172569861308535001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21589344781713240872356667 32384017172569861308535001)
                ·
                  refine ⟨24288012879427395981401251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32384017172569861308535001 24288012879427395981401251)
                  ·
                    refine ⟨36432019319141093972101877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24288012879427395981401251 36432019319141093972101877)
                    ·
                      refine ⟨3415501811169477559884551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36432019319141093972101877 3415501811169477559884551)
                      ·
                        rfl

theorem cell23_6651666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6651666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651666 prefixEnd_6651666 := by exact prefixLift 6651666
  have htrace : WordTrace (prefixWord ++ tailWord_6651666) baseStart_6651666 baseEnd_6651666 := by
    simpa [prefixWord, tailWord_6651666, baseEnd_6651666] using wordTrace_append hprefix tailTrace_6651666
  have hstable : (prefixWord ++ tailWord_6651666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651666).length < 2 ^ (prefixWord ++ tailWord_6651666).sum := by decide
  have hdescent : baseEnd_6651666 < baseStart_6651666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651692 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_6651692 : Nat := 118140960795 + 6651692 * 2 ^ 59
def prefixEnd_6651692 : Nat := 4983230072969 + 3 ^ 40 * 6651692 * 2
def baseEnd_6651692 : Nat := 3415515161666494458159431

theorem tailTrace_6651692 : CollatzResearch.WordTrace tailWord_6651692 prefixEnd_6651692 3415515161666494458159431 := by
  unfold tailWord_6651692
  simp only [CollatzResearch.WordTrace]
  refine ⟨121303569109031688697826665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161738092145375584930435553 121303569109031688697826665)
  ·
    refine ⟨90977676831773766523369999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121303569109031688697826665 90977676831773766523369999)
    ·
      refine ⟨136466515247660649785054999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90977676831773766523369999 136466515247660649785054999)
      ·
        refine ⟨204699772871490974677582499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136466515247660649785054999 204699772871490974677582499)
        ·
          refine ⟨307049659307236462016373749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204699772871490974677582499 307049659307236462016373749)
          ·
            refine ⟨28785905560053418314035039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307049659307236462016373749 28785905560053418314035039)
            ·
              refine ⟨43178858340080127471052559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28785905560053418314035039 43178858340080127471052559)
              ·
                refine ⟨64768287510120191206578839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43178858340080127471052559 64768287510120191206578839)
                ·
                  refine ⟨97152431265180286809868259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64768287510120191206578839 97152431265180286809868259)
                  ·
                    refine ⟨145728646897770430214802389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97152431265180286809868259 145728646897770430214802389)
                    ·
                      refine ⟨3415515161666494458159431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145728646897770430214802389 3415515161666494458159431)
                      ·
                        rfl

theorem cell23_6651692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_6651692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651692 prefixEnd_6651692 := by exact prefixLift 6651692
  have htrace : WordTrace (prefixWord ++ tailWord_6651692) baseStart_6651692 baseEnd_6651692 := by
    simpa [prefixWord, tailWord_6651692, baseEnd_6651692] using wordTrace_append hprefix tailTrace_6651692
  have hstable : (prefixWord ++ tailWord_6651692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651692).length < 2 ^ (prefixWord ++ tailWord_6651692).sum := by decide
  have hdescent : baseEnd_6651692 < baseStart_6651692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651719 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_6651719 : Nat := 118140960795 + 6651719 * 2 ^ 59
def prefixEnd_6651719 : Nat := 4983230072969 + 3 ^ 40 * 6651719 * 2
def baseEnd_6651719 : Nat := 3415529025644165852521807

theorem tailTrace_6651719 : CollatzResearch.WordTrace tailWord_6651719 prefixEnd_6651719 3415529025644165852521807 := by
  unfold tailWord_6651719
  simp only [CollatzResearch.WordTrace]
  refine ⟨242608122988965561006886211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161738748659310374004590807 242608122988965561006886211)
  ·
    refine ⟨363912184483448341510329317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242608122988965561006886211 363912184483448341510329317)
    ·
      refine ⟨68233534590646564033186747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363912184483448341510329317 68233534590646564033186747)
      ·
        refine ⟨102350301885969846049780121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68233534590646564033186747 102350301885969846049780121)
        ·
          refine ⟨76762726414477384537335091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102350301885969846049780121 76762726414477384537335091)
          ·
            refine ⟨115144089621716076806002637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76762726414477384537335091 115144089621716076806002637)
            ·
              refine ⟨43179033608143528802250989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115144089621716076806002637 43179033608143528802250989)
              ·
                refine ⟨16192137603053823300844121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43179033608143528802250989 16192137603053823300844121)
                ·
                  refine ⟨12144103202290367475633091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16192137603053823300844121 12144103202290367475633091)
                  ·
                    refine ⟨18216154803435551213449637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12144103202290367475633091 18216154803435551213449637)
                    ·
                      refine ⟨3415529025644165852521807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18216154803435551213449637 3415529025644165852521807)
                      ·
                        rfl

theorem cell23_6651719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_6651719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651719 prefixEnd_6651719 := by exact prefixLift 6651719
  have htrace : WordTrace (prefixWord ++ tailWord_6651719) baseStart_6651719 baseEnd_6651719 := by
    simpa [prefixWord, tailWord_6651719, baseEnd_6651719] using wordTrace_append hprefix tailTrace_6651719
  have hstable : (prefixWord ++ tailWord_6651719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651719).length < 2 ^ (prefixWord ++ tailWord_6651719).sum := by decide
  have hdescent : baseEnd_6651719 < baseStart_6651719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651819 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 8, 4]
def baseStart_6651819 : Nat := 118140960795 + 6651819 * 2 ^ 59
def prefixEnd_6651819 : Nat := 4983230072969 + 3 ^ 40 * 6651819 * 2
def baseEnd_6651819 : Nat := 1138526791236538487090449

theorem tailTrace_6651819 : CollatzResearch.WordTrace tailWord_6651819 prefixEnd_6651819 1138526791236538487090449 := by
  unfold tailWord_6651819
  simp only [CollatzResearch.WordTrace]
  refine ⟨242611770288603278085526511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161741180192402185390351007 242611770288603278085526511)
  ·
    refine ⟨363917655432904917128289767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242611770288603278085526511 363917655432904917128289767)
    ·
      refine ⟨545876483149357375692434651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363917655432904917128289767 545876483149357375692434651)
      ·
        refine ⟨818814724724036063538651977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545876483149357375692434651 818814724724036063538651977)
        ·
          refine ⟨614111043543027047653988983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818814724724036063538651977 614111043543027047653988983)
          ·
            refine ⟨921166565314540571480983475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614111043543027047653988983 921166565314540571480983475)
            ·
              refine ⟨1381749847971810857221475213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921166565314540571480983475 1381749847971810857221475213)
              ·
                refine ⟨518156192989429071458053205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381749847971810857221475213 518156192989429071458053205)
                ·
                  refine ⟨6072142886594871931149061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 518156192989429071458053205 6072142886594871931149061)
                  ·
                    refine ⟨1138526791236538487090449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072142886594871931149061 1138526791236538487090449)
                    ·
                      rfl

theorem cell23_6651819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 4].length) (baseStart_6651819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651819 prefixEnd_6651819 := by exact prefixLift 6651819
  have htrace : WordTrace (prefixWord ++ tailWord_6651819) baseStart_6651819 baseEnd_6651819 := by
    simpa [prefixWord, tailWord_6651819, baseEnd_6651819] using wordTrace_append hprefix tailTrace_6651819
  have hstable : (prefixWord ++ tailWord_6651819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651819).length < 2 ^ (prefixWord ++ tailWord_6651819).sum := by decide
  have hdescent : baseEnd_6651819 < baseStart_6651819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651837 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6651837 : Nat := 118140960795 + 6651837 * 2 ^ 59
def prefixEnd_6651837 : Nat := 4983230072969 + 3 ^ 40 * 6651837 * 2
def baseEnd_6651837 : Nat := 3415589616361396390846265

theorem tailTrace_6651837 : CollatzResearch.WordTrace tailWord_6651837 prefixEnd_6651837 3415589616361396390846265 := by
  unfold tailWord_6651837
  simp only [CollatzResearch.WordTrace]
  refine ⟨242612426802538067159681765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161741617868358711439787843 242612426802538067159681765)
  ·
    refine ⟨45489830025475887592440331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242612426802538067159681765 45489830025475887592440331)
    ·
      refine ⟨68234745038213831388660497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45489830025475887592440331 68234745038213831388660497)
      ·
        refine ⟨51176058778660373541495373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68234745038213831388660497 51176058778660373541495373)
        ·
          refine ⟨19191022041997640078060765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51176058778660373541495373 19191022041997640078060765)
          ·
            refine ⟨7196633265749115029272787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19191022041997640078060765 7196633265749115029272787)
            ·
              refine ⟨10794949898623672543909181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196633265749115029272787 10794949898623672543909181)
              ·
                refine ⟨4048106211983877203965943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10794949898623672543909181 4048106211983877203965943)
                ·
                  refine ⟨6072159317975815805948915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048106211983877203965943 6072159317975815805948915)
                  ·
                    refine ⟨9108238976963723708923373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6072159317975815805948915 9108238976963723708923373)
                    ·
                      refine ⟨3415589616361396390846265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108238976963723708923373 3415589616361396390846265)
                      ·
                        rfl

theorem cell23_6651837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6651837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651837 prefixEnd_6651837 := by exact prefixLift 6651837
  have htrace : WordTrace (prefixWord ++ tailWord_6651837) baseStart_6651837 baseEnd_6651837 := by
    simpa [prefixWord, tailWord_6651837, baseEnd_6651837] using wordTrace_append hprefix tailTrace_6651837
  have hstable : (prefixWord ++ tailWord_6651837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651837).length < 2 ^ (prefixWord ++ tailWord_6651837).sum := by decide
  have hdescent : baseEnd_6651837 < baseStart_6651837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651839 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_6651839 : Nat := 118140960795 + 6651839 * 2 ^ 59
def prefixEnd_6651839 : Nat := 4983230072969 + 3 ^ 40 * 6651839 * 2
def baseEnd_6651839 : Nat := 3415590643322705383021255

theorem tailTrace_6651839 : CollatzResearch.WordTrace tailWord_6651839 prefixEnd_6651839 3415590643322705383021255 := by
  unfold tailWord_6651839
  simp only [CollatzResearch.WordTrace]
  refine ⟨242612499748530821501254571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161741666499020547667503047 242612499748530821501254571)
  ·
    refine ⟨363918749622796232251881857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242612499748530821501254571 363918749622796232251881857)
    ·
      refine ⟨272939062217097174188911393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363918749622796232251881857 272939062217097174188911393)
      ·
        refine ⟨204704296662822880641683545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272939062217097174188911393 204704296662822880641683545)
        ·
          refine ⟨153528222497117160481262659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204704296662822880641683545 153528222497117160481262659)
          ·
            refine ⟨230292333745675740721893989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153528222497117160481262659 230292333745675740721893989)
            ·
              refine ⟨43179812577314201385355123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230292333745675740721893989 43179812577314201385355123)
              ·
                refine ⟨64769718865971302078032685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43179812577314201385355123 64769718865971302078032685)
                ·
                  refine ⟨24288644574739238279262257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64769718865971302078032685 24288644574739238279262257)
                  ·
                    refine ⟨18216483431054428709446693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24288644574739238279262257 18216483431054428709446693)
                    ·
                      refine ⟨3415590643322705383021255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18216483431054428709446693 3415590643322705383021255)
                      ·
                        rfl

theorem cell23_6651839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_6651839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651839 prefixEnd_6651839 := by exact prefixLift 6651839
  have htrace : WordTrace (prefixWord ++ tailWord_6651839) baseStart_6651839 baseEnd_6651839 := by
    simpa [prefixWord, tailWord_6651839, baseEnd_6651839] using wordTrace_append hprefix tailTrace_6651839
  have hstable : (prefixWord ++ tailWord_6651839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651839).length < 2 ^ (prefixWord ++ tailWord_6651839).sum := by decide
  have hdescent : baseEnd_6651839 < baseStart_6651839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651866 : List Nat := [3, 1, 1, 2, 5, 1, 2, 8]
def baseStart_6651866 : Nat := 118140960795 + 6651866 * 2 ^ 59
def prefixEnd_6651866 : Nat := 4983230072969 + 3 ^ 40 * 6651866 * 2
def baseEnd_6651866 : Nat := 126503870640754695458653

theorem tailTrace_6651866 : CollatzResearch.WordTrace tailWord_6651866 prefixEnd_6651866 126503870640754695458653 := by
  unfold tailWord_6651866
  simp only [CollatzResearch.WordTrace]
  refine ⟨60653371129858251278121863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161742323012955336741658301 60653371129858251278121863)
  ·
    refine ⟨90980056694787376917182795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60653371129858251278121863 90980056694787376917182795)
    ·
      refine ⟨136470085042181065375774193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90980056694787376917182795 136470085042181065375774193)
      ·
        refine ⟨102352563781635799031830645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136470085042181065375774193 102352563781635799031830645)
        ·
          refine ⟨9595552854528356159234123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102352563781635799031830645 9595552854528356159234123)
          ·
            refine ⟨14393329281792534238851185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9595552854528356159234123 14393329281792534238851185)
            ·
              refine ⟨10794996961344400679138389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14393329281792534238851185 10794996961344400679138389)
              ·
                refine ⟨126503870640754695458653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10794996961344400679138389 126503870640754695458653)
                ·
                  rfl

theorem cell23_6651866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_6651866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651866 prefixEnd_6651866 := by exact prefixLift 6651866
  have htrace : WordTrace (prefixWord ++ tailWord_6651866) baseStart_6651866 baseEnd_6651866 := by
    simpa [prefixWord, tailWord_6651866, baseEnd_6651866] using wordTrace_append hprefix tailTrace_6651866
  have hstable : (prefixWord ++ tailWord_6651866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651866).length < 2 ^ (prefixWord ++ tailWord_6651866).sum := by decide
  have hdescent : baseEnd_6651866 < baseStart_6651866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651876 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_6651876 : Nat := 118140960795 + 6651876 * 2 ^ 59
def prefixEnd_6651876 : Nat := 4983230072969 + 3 ^ 40 * 6651876 * 2
def baseEnd_6651876 : Nat := 3415609642106921738258585

theorem tailTrace_6651876 : CollatzResearch.WordTrace tailWord_6651876 prefixEnd_6651876 3415609642106921738258585 := by
  unfold tailWord_6651876
  simp only [CollatzResearch.WordTrace]
  refine ⟨121306924624698388410175741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161742566166264517880234321 121306924624698388410175741)
  ·
    refine ⟨45490096734261895653815903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121306924624698388410175741 45490096734261895653815903)
    ·
      refine ⟨68235145101392843480723855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45490096734261895653815903 68235145101392843480723855)
      ·
        refine ⟨102352717652089265221085783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68235145101392843480723855 102352717652089265221085783)
        ·
          refine ⟨153529076478133897831628675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102352717652089265221085783 153529076478133897831628675)
          ·
            refine ⟨230293614717200846747443013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153529076478133897831628675 230293614717200846747443013)
            ·
              refine ⟨43180052759475158765145565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230293614717200846747443013 43180052759475158765145565)
              ·
                refine ⟨16192519784803184536929587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43180052759475158765145565 16192519784803184536929587)
                ·
                  refine ⟨24288779677204776805394381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16192519784803184536929587 24288779677204776805394381)
                  ·
                    refine ⟨9108292378951791302022893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24288779677204776805394381 9108292378951791302022893)
                    ·
                      refine ⟨3415609642106921738258585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108292378951791302022893 3415609642106921738258585)
                      ·
                        rfl

theorem cell23_6651876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_6651876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651876 prefixEnd_6651876 := by exact prefixLift 6651876
  have htrace : WordTrace (prefixWord ++ tailWord_6651876) baseStart_6651876 baseEnd_6651876 := by
    simpa [prefixWord, tailWord_6651876, baseEnd_6651876] using wordTrace_append hprefix tailTrace_6651876
  have hstable : (prefixWord ++ tailWord_6651876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651876).length < 2 ^ (prefixWord ++ tailWord_6651876).sum := by decide
  have hdescent : baseEnd_6651876 < baseStart_6651876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651903 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 1, 3, 2]
def baseStart_6651903 : Nat := 118140960795 + 6651903 * 2 ^ 59
def prefixEnd_6651903 : Nat := 4983230072969 + 3 ^ 40 * 6651903 * 2
def baseEnd_6651903 : Nat := 3415623506084593132620961

theorem tailTrace_6651903 : CollatzResearch.WordTrace tailWord_6651903 prefixEnd_6651903 3415623506084593132620961 := by
  unfold tailWord_6651903
  simp only [CollatzResearch.WordTrace]
  refine ⟨242614834020298960431584363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161743222680199306954389575 242614834020298960431584363)
  ·
    refine ⟨363922251030448440647376545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242614834020298960431584363 363922251030448440647376545)
    ·
      refine ⟨272941688272836330485532409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363922251030448440647376545 272941688272836330485532409)
      ·
        refine ⟨204706266204627247864149307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272941688272836330485532409 204706266204627247864149307)
        ·
          refine ⟨307059399306940871796223961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204706266204627247864149307 307059399306940871796223961)
          ·
            refine ⟨230294549480205653847167971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307059399306940871796223961 230294549480205653847167971)
            ·
              refine ⟨345441824220308480770751957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230294549480205653847167971 345441824220308480770751957)
              ·
                refine ⟨8096292755163480018064499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 345441824220308480770751957 8096292755163480018064499)
                ·
                  refine ⟨12144439132745220027096749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8096292755163480018064499 12144439132745220027096749)
                  ·
                    refine ⟨4554164674779457510161281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12144439132745220027096749 4554164674779457510161281)
                    ·
                      refine ⟨3415623506084593132620961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554164674779457510161281 3415623506084593132620961)
                      ·
                        rfl

theorem cell23_6651903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_6651903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651903 prefixEnd_6651903 := by exact prefixLift 6651903
  have htrace : WordTrace (prefixWord ++ tailWord_6651903) baseStart_6651903 baseEnd_6651903 := by
    simpa [prefixWord, tailWord_6651903, baseEnd_6651903] using wordTrace_append hprefix tailTrace_6651903
  have hstable : (prefixWord ++ tailWord_6651903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651903).length < 2 ^ (prefixWord ++ tailWord_6651903).sum := by decide
  have hdescent : baseEnd_6651903 < baseStart_6651903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651917 : List Nat := [1, 7, 1, 2, 1, 2, 1, 8]
def baseStart_6651917 : Nat := 118140960795 + 6651917 * 2 ^ 59
def prefixEnd_6651917 : Nat := 4983230072969 + 3 ^ 40 * 6651917 * 2
def baseEnd_6651917 : Nat := 126504840548657632512811

theorem tailTrace_6651917 : CollatzResearch.WordTrace tailWord_6651917 prefixEnd_6651917 126504840548657632512811 := by
  unfold tailWord_6651917
  simp only [CollatzResearch.WordTrace]
  refine ⟨242615344642248240822594005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161743563094832160548396003 242615344642248240822594005)
  ·
    refine ⟨5686297140052693144279547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 242615344642248240822594005 5686297140052693144279547)
    ·
      refine ⟨8529445710079039716419321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686297140052693144279547 8529445710079039716419321)
      ·
        refine ⟨6397084282559279787314491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8529445710079039716419321 6397084282559279787314491)
        ·
          refine ⟨9595626423838919680971737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397084282559279787314491 9595626423838919680971737)
          ·
            refine ⟨7196719817879189760728803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9595626423838919680971737 7196719817879189760728803)
            ·
              refine ⟨10795079726818784641093205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196719817879189760728803 10795079726818784641093205)
              ·
                refine ⟨126504840548657632512811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10795079726818784641093205 126504840548657632512811)
                ·
                  rfl

theorem cell23_6651917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 8].length) (baseStart_6651917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651917 prefixEnd_6651917 := by exact prefixLift 6651917
  have htrace : WordTrace (prefixWord ++ tailWord_6651917) baseStart_6651917 baseEnd_6651917 := by
    simpa [prefixWord, tailWord_6651917, baseEnd_6651917] using wordTrace_append hprefix tailTrace_6651917
  have hstable : (prefixWord ++ tailWord_6651917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651917).length < 2 ^ (prefixWord ++ tailWord_6651917).sum := by decide
  have hdescent : baseEnd_6651917 < baseStart_6651917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651950 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_6651950 : Nat := 118140960795 + 6651950 * 2 ^ 59
def prefixEnd_6651950 : Nat := 4983230072969 + 3 ^ 40 * 6651950 * 2
def baseEnd_6651950 : Nat := 3415647639675354448733245

theorem tailTrace_6651950 : CollatzResearch.WordTrace tailWord_6651950 prefixEnd_6651950 3415647639675354448733245 := by
  unfold tailWord_6651950
  simp only [CollatzResearch.WordTrace]
  refine ⟨30327068531391085932318163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161744365500752458305696869 30327068531391085932318163)
  ·
    refine ⟨45490602797086628898477245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30327068531391085932318163 45490602797086628898477245)
    ·
      refine ⟨17058976048907485836928967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45490602797086628898477245 17058976048907485836928967)
      ·
        refine ⟨25588464073361228755393451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17058976048907485836928967 25588464073361228755393451)
        ·
          refine ⟨38382696110041843133090177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25588464073361228755393451 38382696110041843133090177)
          ·
            refine ⟨28787022082531382349817633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38382696110041843133090177 28787022082531382349817633)
            ·
              refine ⟨21590266561898536762363225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28787022082531382349817633 21590266561898536762363225)
              ·
                refine ⟨16192699921423902571772419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21590266561898536762363225 16192699921423902571772419)
                ·
                  refine ⟨24289049882135853857658629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16192699921423902571772419 24289049882135853857658629)
                  ·
                    refine ⟨4554196852900472598310993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24289049882135853857658629 4554196852900472598310993)
                    ·
                      refine ⟨3415647639675354448733245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554196852900472598310993 3415647639675354448733245)
                      ·
                        rfl

theorem cell23_6651950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_6651950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651950 prefixEnd_6651950 := by exact prefixLift 6651950
  have htrace : WordTrace (prefixWord ++ tailWord_6651950) baseStart_6651950 baseEnd_6651950 := by
    simpa [prefixWord, tailWord_6651950, baseEnd_6651950] using wordTrace_append hprefix tailTrace_6651950
  have hstable : (prefixWord ++ tailWord_6651950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651950).length < 2 ^ (prefixWord ++ tailWord_6651950).sum := by decide
  have hdescent : baseEnd_6651950 < baseStart_6651950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6651990 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_6651990 : Nat := 118140960795 + 6651990 * 2 ^ 59
def prefixEnd_6651990 : Nat := 4983230072969 + 3 ^ 40 * 6651990 * 2
def baseEnd_6651990 : Nat := 379518686544614921359229

theorem tailTrace_6651990 : CollatzResearch.WordTrace tailWord_6651990 prefixEnd_6651990 379518686544614921359229 := by
  unfold tailWord_6651990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163625448186485893125089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161745338113989182860000949 15163625448186485893125089)
  ·
    refine ⟨11372719086139864419843817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15163625448186485893125089 11372719086139864419843817)
    ·
      refine ⟨8529539314604898314882863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11372719086139864419843817 8529539314604898314882863)
      ·
        refine ⟨12794308971907347472324295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529539314604898314882863 12794308971907347472324295)
        ·
          refine ⟨19191463457861021208486443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794308971907347472324295 19191463457861021208486443)
          ·
            refine ⟨28787195186791531812729665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19191463457861021208486443 28787195186791531812729665)
            ·
              refine ⟨21590396390093648859547249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28787195186791531812729665 21590396390093648859547249)
              ·
                refine ⟨16192797292570236644660437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21590396390093648859547249 16192797292570236644660437)
                ·
                  refine ⟨379518686544614921359229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16192797292570236644660437 379518686544614921359229)
                  ·
                    rfl

theorem cell23_6651990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_6651990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6651990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6651990 prefixEnd_6651990 := by exact prefixLift 6651990
  have htrace : WordTrace (prefixWord ++ tailWord_6651990) baseStart_6651990 baseEnd_6651990 := by
    simpa [prefixWord, tailWord_6651990, baseEnd_6651990] using wordTrace_append hprefix tailTrace_6651990
  have hstable : (prefixWord ++ tailWord_6651990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6651990).length < 2 ^ (prefixWord ++ tailWord_6651990).sum := by decide
  have hdescent : baseEnd_6651990 < baseStart_6651990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6651990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
