import V185TrunkScan21Chunk153

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1877610 : List Nat := [3, 1, 3, 2, 1, 4, 1, 6]
def baseStart_1877610 : Nat := 118140960795 + 1877610 * 2 ^ 59
def prefixEnd_1877610 : Nat := 4983230072969 + 3 ^ 40 * 1877610 * 2
def baseEnd_1877610 : Nat := 142832060990889492731857

theorem tailTrace_1877610 : CollatzResearch.WordTrace tailWord_1877610 prefixEnd_1877610 142832060990889492731857 := by
  unfold tailWord_1877610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120515681936778775811571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45654708485164743402164189 17120515681936778775811571)
  ·
    refine ⟨25680773522905168163717357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17120515681936778775811571 25680773522905168163717357)
    ·
      refine ⟨9630290071089438061394009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25680773522905168163717357 9630290071089438061394009)
      ·
        refine ⟨7222717553317078546045507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9630290071089438061394009 7222717553317078546045507)
        ·
          refine ⟨10834076329975617819068261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222717553317078546045507 10834076329975617819068261)
          ·
            refine ⟨2031389311870428341075299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10834076329975617819068261 2031389311870428341075299)
            ·
              refine ⟨3047083967805642511612949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031389311870428341075299 3047083967805642511612949)
              ·
                refine ⟨142832060990889492731857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3047083967805642511612949 142832060990889492731857)
                ·
                  rfl

theorem cell21_1877610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_1877610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877610 prefixEnd_1877610 := by exact prefixLift 1877610
  have htrace : WordTrace (prefixWord ++ tailWord_1877610) baseStart_1877610 baseEnd_1877610 := by
    simpa [prefixWord, tailWord_1877610, baseEnd_1877610] using wordTrace_append hprefix tailTrace_1877610
  have hstable : (prefixWord ++ tailWord_1877610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877610).length < 2 ^ (prefixWord ++ tailWord_1877610).sum := by decide
  have hdescent : baseEnd_1877610 < baseStart_1877610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877655 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_1877655 : Nat := 118140960795 + 1877655 * 2 ^ 59
def prefixEnd_1877655 : Nat := 4983230072969 + 3 ^ 40 * 1877655 * 2
def baseEnd_1877655 : Nat := 428506452585758399945479

theorem tailTrace_1877655 : CollatzResearch.WordTrace tailWord_1877655 prefixEnd_1877655 428506452585758399945479 := by
  unfold tailWord_1877655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68483704012584087788634419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45655802675056058525756279 68483704012584087788634419)
  ·
    refine ⟨102725556018876131682951629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68483704012584087788634419 102725556018876131682951629)
    ·
      refine ⟨38522083507078549381106861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102725556018876131682951629 38522083507078549381106861)
      ·
        refine ⟨14445781315154456017915073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38522083507078549381106861 14445781315154456017915073)
        ·
          refine ⟨10834335986365842013436305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14445781315154456017915073 10834335986365842013436305)
          ·
            refine ⟨8125751989774381510077229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834335986365842013436305 8125751989774381510077229)
            ·
              refine ⟨3047156996165393066278961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8125751989774381510077229 3047156996165393066278961)
              ·
                refine ⟨2285367747124044799709221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047156996165393066278961 2285367747124044799709221)
                ·
                  refine ⟨428506452585758399945479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285367747124044799709221 428506452585758399945479)
                  ·
                    rfl

theorem cell21_1877655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_1877655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877655 prefixEnd_1877655 := by exact prefixLift 1877655
  have htrace : WordTrace (prefixWord ++ tailWord_1877655) baseStart_1877655 baseEnd_1877655 := by
    simpa [prefixWord, tailWord_1877655, baseEnd_1877655] using wordTrace_append hprefix tailTrace_1877655
  have hstable : (prefixWord ++ tailWord_1877655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877655).length < 2 ^ (prefixWord ++ tailWord_1877655).sum := by decide
  have hdescent : baseEnd_1877655 < baseStart_1877655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877683 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_1877683 : Nat := 118140960795 + 1877683 * 2 ^ 59
def prefixEnd_1877683 : Nat := 4983230072969 + 3 ^ 40 * 1877683 * 2
def baseEnd_1877683 : Nat := 428512842567236573478755

theorem tailTrace_1877683 : CollatzResearch.WordTrace tailWord_1877683 prefixEnd_1877683 428512842567236573478755 := by
  unfold tailWord_1877683
  simp only [CollatzResearch.WordTrace]
  refine ⟨68484725256482648570653703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45656483504321765713769135 68484725256482648570653703)
  ·
    refine ⟨102727087884723972855980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68484725256482648570653703 102727087884723972855980555)
    ·
      refine ⟨154090631827085959283970833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102727087884723972855980555 154090631827085959283970833)
      ·
        refine ⟨115567973870314469462978125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154090631827085959283970833 115567973870314469462978125)
        ·
          refine ⟨43337990201367926048616797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115567973870314469462978125 43337990201367926048616797)
          ·
            refine ⟨16251746325512972268231299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43337990201367926048616797 16251746325512972268231299)
            ·
              refine ⟨24377619488269458402346949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16251746325512972268231299 24377619488269458402346949)
              ·
                refine ⟨4570803654050523450440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24377619488269458402346949 4570803654050523450440053)
                ·
                  refine ⟨428512842567236573478755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570803654050523450440053 428512842567236573478755)
                  ·
                    rfl

theorem cell21_1877683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_1877683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877683 prefixEnd_1877683 := by exact prefixLift 1877683
  have htrace : WordTrace (prefixWord ++ tailWord_1877683) baseStart_1877683 baseEnd_1877683 := by
    simpa [prefixWord, tailWord_1877683, baseEnd_1877683] using wordTrace_append hprefix tailTrace_1877683
  have hstable : (prefixWord ++ tailWord_1877683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877683).length < 2 ^ (prefixWord ++ tailWord_1877683).sum := by decide
  have hdescent : baseEnd_1877683 < baseStart_1877683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877728 : List Nat := [2, 1, 1, 3, 1, 2, 3, 8]
def baseStart_1877728 : Nat := 118140960795 + 1877728 * 2 ^ 59
def prefixEnd_1877728 : Nat := 4983230072969 + 3 ^ 40 * 1877728 * 2
def baseEnd_1877728 : Nat := 142841037393442165076221

theorem tailTrace_1877728 : CollatzResearch.WordTrace tailWord_1877728 prefixEnd_1877728 142841037393442165076221 := by
  unfold tailWord_1877728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34243183270659810628020919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45657577694213080837361225 34243183270659810628020919)
  ·
    refine ⟨51364774905989715942031379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34243183270659810628020919 51364774905989715942031379)
    ·
      refine ⟨77047162358984573913047069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51364774905989715942031379 77047162358984573913047069)
      ·
        refine ⟨28892685884619215217392651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77047162358984573913047069 28892685884619215217392651)
        ·
          refine ⟨43339028826928822826088977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28892685884619215217392651 43339028826928822826088977)
          ·
            refine ⟨32504271620196617119566733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43339028826928822826088977 32504271620196617119566733)
            ·
              refine ⟨12189101857573731419837525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32504271620196617119566733 12189101857573731419837525)
              ·
                refine ⟨142841037393442165076221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12189101857573731419837525 142841037393442165076221)
                ·
                  rfl

theorem cell21_1877728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_1877728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877728 prefixEnd_1877728 := by exact prefixLift 1877728
  have htrace : WordTrace (prefixWord ++ tailWord_1877728) baseStart_1877728 baseEnd_1877728 := by
    simpa [prefixWord, tailWord_1877728, baseEnd_1877728] using wordTrace_append hprefix tailTrace_1877728
  have hstable : (prefixWord ++ tailWord_1877728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877728).length < 2 ^ (prefixWord ++ tailWord_1877728).sum := by decide
  have hdescent : baseEnd_1877728 < baseStart_1877728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877821 : List Nat := [1, 4, 1, 4, 1, 2, 8]
def baseStart_1877821 : Nat := 118140960795 + 1877821 * 2 ^ 59
def prefixEnd_1877821 : Nat := 4983230072969 + 3 ^ 40 * 1877821 * 2
def baseEnd_1877821 : Nat := 47616037338597666686497

theorem tailTrace_1877821 : CollatzResearch.WordTrace tailWord_1877821 prefixEnd_1877821 47616037338597666686497 := by
  unfold tailWord_1877821
  simp only [CollatzResearch.WordTrace]
  refine ⟨68489758529982698139177317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45659839019988465426118211 68489758529982698139177317)
  ·
    refine ⟨12841829724371755901095747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68489758529982698139177317 12841829724371755901095747)
    ·
      refine ⟨19262744586557633851643621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841829724371755901095747 19262744586557633851643621)
      ·
        refine ⟨3611764609979556347183179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19262744586557633851643621 3611764609979556347183179)
        ·
          refine ⟨5417646914969334520774769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611764609979556347183179 5417646914969334520774769)
          ·
            refine ⟨4063235186227000890581077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417646914969334520774769 4063235186227000890581077)
            ·
              refine ⟨47616037338597666686497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4063235186227000890581077 47616037338597666686497)
              ·
                rfl

theorem cell21_1877821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 8].length) (baseStart_1877821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877821 prefixEnd_1877821 := by exact prefixLift 1877821
  have htrace : WordTrace (prefixWord ++ tailWord_1877821) baseStart_1877821 baseEnd_1877821 := by
    simpa [prefixWord, tailWord_1877821, baseEnd_1877821] using wordTrace_append hprefix tailTrace_1877821
  have hstable : (prefixWord ++ tailWord_1877821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877821).length < 2 ^ (prefixWord ++ tailWord_1877821).sum := by decide
  have hdescent : baseEnd_1877821 < baseStart_1877821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877869 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 3]
def baseStart_1877869 : Nat := 118140960795 + 1877869 * 2 ^ 59
def prefixEnd_1877869 : Nat := 4983230072969 + 3 ^ 40 * 1877869 * 2
def baseEnd_1877869 : Nat := 428555290301341583378375

theorem tailTrace_1877869 : CollatzResearch.WordTrace tailWord_1877869 prefixEnd_1877869 428555290301341583378375 := by
  unfold tailWord_1877869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68491509233808802336924661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45661006155872534891283107 68491509233808802336924661)
  ·
    refine ⟨6421078990669575219086687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68491509233808802336924661 6421078990669575219086687)
    ·
      refine ⟨9631618486004362828630031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421078990669575219086687 9631618486004362828630031)
      ·
        refine ⟨14447427729006544242945047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631618486004362828630031 14447427729006544242945047)
        ·
          refine ⟨21671141593509816364417571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14447427729006544242945047 21671141593509816364417571)
          ·
            refine ⟨32506712390264724546626357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671141593509816364417571 32506712390264724546626357)
            ·
              refine ⟨3047504286587317926246221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32506712390264724546626357 3047504286587317926246221)
              ·
                refine ⟨1142814107470244222342333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047504286587317926246221 1142814107470244222342333)
                ·
                  refine ⟨428555290301341583378375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142814107470244222342333 428555290301341583378375)
                  ·
                    rfl

theorem cell21_1877869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_1877869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877869 prefixEnd_1877869 := by exact prefixLift 1877869
  have htrace : WordTrace (prefixWord ++ tailWord_1877869) baseStart_1877869 baseEnd_1877869 := by
    simpa [prefixWord, tailWord_1877869, baseEnd_1877869] using wordTrace_append hprefix tailTrace_1877869
  have hstable : (prefixWord ++ tailWord_1877869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877869).length < 2 ^ (prefixWord ++ tailWord_1877869).sum := by decide
  have hdescent : baseEnd_1877869 < baseStart_1877869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877886 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1877886 : Nat := 118140960795 + 1877886 * 2 ^ 59
def prefixEnd_1877886 : Nat := 4983230072969 + 3 ^ 40 * 1877886 * 2
def baseEnd_1877886 : Nat := 428559169932953331595007

theorem tailTrace_1877886 : CollatzResearch.WordTrace tailWord_1877886 prefixEnd_1877886 428559169932953331595007 := by
  unfold tailWord_1877886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561516159343401780036689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45661419516498142826862341 8561516159343401780036689)
  ·
    refine ⟨6421137119507551335027517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8561516159343401780036689 6421137119507551335027517)
    ·
      refine ⟨2407926419815331750635319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6421137119507551335027517 2407926419815331750635319)
      ·
        refine ⟨3611889629722997625952979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407926419815331750635319 3611889629722997625952979)
        ·
          refine ⟨5417834444584496438929469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611889629722997625952979 5417834444584496438929469)
          ·
            refine ⟨2031687916719186164598551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5417834444584496438929469 2031687916719186164598551)
            ·
              refine ⟨3047531875078779246897827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031687916719186164598551 3047531875078779246897827)
              ·
                refine ⟨4571297812618168870346741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047531875078779246897827 4571297812618168870346741)
                ·
                  refine ⟨428559169932953331595007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571297812618168870346741 428559169932953331595007)
                  ·
                    rfl

theorem cell21_1877886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1877886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877886 prefixEnd_1877886 := by exact prefixLift 1877886
  have htrace : WordTrace (prefixWord ++ tailWord_1877886) baseStart_1877886 baseEnd_1877886 := by
    simpa [prefixWord, tailWord_1877886, baseEnd_1877886] using wordTrace_append hprefix tailTrace_1877886
  have hstable : (prefixWord ++ tailWord_1877886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877886).length < 2 ^ (prefixWord ++ tailWord_1877886).sum := by decide
  have hdescent : baseEnd_1877886 < baseStart_1877886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877925 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1877925 : Nat := 118140960795 + 1877925 * 2 ^ 59
def prefixEnd_1877925 : Nat := 4983230072969 + 3 ^ 40 * 1877925 * 2
def baseEnd_1877925 : Nat := 428568070264297930444927

theorem tailTrace_1877925 : CollatzResearch.WordTrace tailWord_1877925 prefixEnd_1877925 428568070264297930444927 := by
  unfold tailWord_1877925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68493551721605923900963229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45662367814403949267308819 68493551721605923900963229)
  ·
    refine ⟨25685081895602221462861211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68493551721605923900963229 25685081895602221462861211)
    ·
      refine ⟨38527622843403332194291817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25685081895602221462861211 38527622843403332194291817)
      ·
        refine ⟨28895717132552499145718863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38527622843403332194291817 28895717132552499145718863)
        ·
          refine ⟨43343575698828748718578295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28895717132552499145718863 43343575698828748718578295)
          ·
            refine ⟨65015363548243123077867443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43343575698828748718578295 65015363548243123077867443)
            ·
              refine ⟨97523045322364684616801165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65015363548243123077867443 97523045322364684616801165)
              ·
                refine ⟨36571141995886756731300437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97523045322364684616801165 36571141995886756731300437)
                ·
                  refine ⟨428568070264297930444927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36571141995886756731300437 428568070264297930444927)
                  ·
                    rfl

theorem cell21_1877925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1877925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877925 prefixEnd_1877925 := by exact prefixLift 1877925
  have htrace : WordTrace (prefixWord ++ tailWord_1877925) baseStart_1877925 baseEnd_1877925 := by
    simpa [prefixWord, tailWord_1877925, baseEnd_1877925] using wordTrace_append hprefix tailTrace_1877925
  have hstable : (prefixWord ++ tailWord_1877925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877925).length < 2 ^ (prefixWord ++ tailWord_1877925).sum := by decide
  have hdescent : baseEnd_1877925 < baseStart_1877925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877934 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1877934 : Nat := 118140960795 + 1877934 * 2 ^ 59
def prefixEnd_1877934 : Nat := 4983230072969 + 3 ^ 40 * 1877934 * 2
def baseEnd_1877934 : Nat := 428570124186915914794909

theorem tailTrace_1877934 : CollatzResearch.WordTrace tailWord_1877934 prefixEnd_1877934 428570124186915914794909 := by
  unfold tailWord_1877934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561734997321664804755107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45662586652382212292027237 8561734997321664804755107)
  ·
    refine ⟨12842602495982497207132661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8561734997321664804755107 12842602495982497207132661)
    ·
      refine ⟨1203993983998359113168687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12842602495982497207132661 1203993983998359113168687)
      ·
        refine ⟨1805990975997538669753031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203993983998359113168687 1805990975997538669753031)
        ·
          refine ⟨2708986463996308004629547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805990975997538669753031 2708986463996308004629547)
          ·
            refine ⟨4063479695994462006944321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708986463996308004629547 4063479695994462006944321)
            ·
              refine ⟨3047609771995846505208241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063479695994462006944321 3047609771995846505208241)
              ·
                refine ⟨2285707328996884878906181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047609771995846505208241 2285707328996884878906181)
                ·
                  refine ⟨428570124186915914794909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285707328996884878906181 428570124186915914794909)
                  ·
                    rfl

theorem cell21_1877934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1877934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877934 prefixEnd_1877934 := by exact prefixLift 1877934
  have htrace : WordTrace (prefixWord ++ tailWord_1877934) baseStart_1877934 baseEnd_1877934 := by
    simpa [prefixWord, tailWord_1877934, baseEnd_1877934] using wordTrace_append hprefix tailTrace_1877934
  have hstable : (prefixWord ++ tailWord_1877934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877934).length < 2 ^ (prefixWord ++ tailWord_1877934).sum := by decide
  have hdescent : baseEnd_1877934 < baseStart_1877934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878049 : List Nat := [1, 2, 3, 2, 4, 2, 7]
def baseStart_1878049 : Nat := 118140960795 + 1878049 * 2 ^ 59
def prefixEnd_1878049 : Nat := 4983230072969 + 3 ^ 40 * 1878049 * 2
def baseEnd_1878049 : Nat := 47621818750411252264223

theorem tailTrace_1878049 : CollatzResearch.WordTrace tailWord_1878049 prefixEnd_1878049 47621818750411252264223 := by
  unfold tailWord_1878049
  simp only [CollatzResearch.WordTrace]
  refine ⟨68498074373156693078477201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45665382915437795385651467 68498074373156693078477201)
  ·
    refine ⟨51373555779867519808857901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68498074373156693078477201 51373555779867519808857901)
    ·
      refine ⟨19265083417450319928321713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51373555779867519808857901 19265083417450319928321713)
      ·
        refine ⟨14448812563087739946241285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19265083417450319928321713 14448812563087739946241285)
        ·
          refine ⟨2709152355578951239920241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14448812563087739946241285 2709152355578951239920241)
          ·
            refine ⟨2031864266684213429940181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709152355578951239920241 2031864266684213429940181)
            ·
              refine ⟨47621818750411252264223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2031864266684213429940181 47621818750411252264223)
              ·
                rfl

theorem cell21_1878049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 7].length) (baseStart_1878049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878049 prefixEnd_1878049 := by exact prefixLift 1878049
  have htrace : WordTrace (prefixWord ++ tailWord_1878049) baseStart_1878049 baseEnd_1878049 := by
    simpa [prefixWord, tailWord_1878049, baseEnd_1878049] using wordTrace_append hprefix tailTrace_1878049
  have hstable : (prefixWord ++ tailWord_1878049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878049).length < 2 ^ (prefixWord ++ tailWord_1878049).sum := by decide
  have hdescent : baseEnd_1878049 < baseStart_1878049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878055 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 3]
def baseStart_1878055 : Nat := 118140960795 + 1878055 * 2 ^ 59
def prefixEnd_1878055 : Nat := 4983230072969 + 3 ^ 40 * 1878055 * 2
def baseEnd_1878055 : Nat := 428597738035446593277995

theorem tailTrace_1878055 : CollatzResearch.WordTrace tailWord_1878055 prefixEnd_1878055 428597738035446593277995 := by
  unfold tailWord_1878055
  simp only [CollatzResearch.WordTrace]
  refine ⟨68498293211134956103195619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45665528807423304068797079 68498293211134956103195619)
  ·
    refine ⟨102747439816702434154793429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68498293211134956103195619 102747439816702434154793429)
    ·
      refine ⟨2408143120703963300502971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102747439816702434154793429 2408143120703963300502971)
      ·
        refine ⟨3612214681055944950754457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408143120703963300502971 3612214681055944950754457)
        ·
          refine ⟨2709161010791958713065843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612214681055944950754457 2709161010791958713065843)
          ·
            refine ⟨4063741516187938069598765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709161010791958713065843 4063741516187938069598765)
            ·
              refine ⟨1523903068570476776099537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4063741516187938069598765 1523903068570476776099537)
              ·
                refine ⟨1142927301427857582074653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523903068570476776099537 1142927301427857582074653)
                ·
                  refine ⟨428597738035446593277995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142927301427857582074653 428597738035446593277995)
                  ·
                    rfl

theorem cell21_1878055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].length) (baseStart_1878055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878055 prefixEnd_1878055 := by exact prefixLift 1878055
  have htrace : WordTrace (prefixWord ++ tailWord_1878055) baseStart_1878055 baseEnd_1878055 := by
    simpa [prefixWord, tailWord_1878055, baseEnd_1878055] using wordTrace_append hprefix tailTrace_1878055
  have hstable : (prefixWord ++ tailWord_1878055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878055).length < 2 ^ (prefixWord ++ tailWord_1878055).sum := by decide
  have hdescent : baseEnd_1878055 < baseStart_1878055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878108 : List Nat := [2, 2, 4, 1, 1, 11]
def baseStart_1878108 : Nat := 118140960795 + 1878108 * 2 ^ 59
def prefixEnd_1878108 : Nat := 4983230072969 + 3 ^ 40 * 1878108 * 2
def baseEnd_1878108 : Nat := 15874438272501121440539

theorem tailTrace_1878108 : CollatzResearch.WordTrace tailWord_1878108 prefixEnd_1878108 15874438272501121440539 := by
  unfold tailWord_1878108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250113139971473077437489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45666817519961964103249985 34250113139971473077437489)
  ·
    refine ⟨25687584854978604808078117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34250113139971473077437489 25687584854978604808078117)
    ·
      refine ⟨4816422160308488401514647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25687584854978604808078117 4816422160308488401514647)
      ·
        refine ⟨7224633240462732602271971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816422160308488401514647 7224633240462732602271971)
        ·
          refine ⟨10836949860694098903407957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224633240462732602271971 10836949860694098903407957)
          ·
            refine ⟨15874438272501121440539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10836949860694098903407957 15874438272501121440539)
            ·
              rfl

theorem cell21_1878108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 11].length) (baseStart_1878108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878108 prefixEnd_1878108 := by exact prefixLift 1878108
  have htrace : WordTrace (prefixWord ++ tailWord_1878108) baseStart_1878108 baseEnd_1878108 := by
    simpa [prefixWord, tailWord_1878108, baseEnd_1878108] using wordTrace_append hprefix tailTrace_1878108
  have hstable : (prefixWord ++ tailWord_1878108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878108).length < 2 ^ (prefixWord ++ tailWord_1878108).sum := by decide
  have hdescent : baseEnd_1878108 < baseStart_1878108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878114 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1878114 : Nat := 118140960795 + 1878114 * 2 ^ 59
def prefixEnd_1878114 : Nat := 4983230072969 + 3 ^ 40 * 1878114 * 2
def baseEnd_1878114 : Nat := 428611202639275601794541

theorem tailTrace_1878114 : CollatzResearch.WordTrace tailWord_1878114 prefixEnd_1878114 428611202639275601794541 := by
  unfold tailWord_1878114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125111279480302294898349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45666963411947472786395597 17125111279480302294898349)
  ·
    refine ⟨6421916729805113360586881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17125111279480302294898349 6421916729805113360586881)
    ·
      refine ⟨4816437547353835020440161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6421916729805113360586881 4816437547353835020440161)
      ·
        refine ⟨3612328160515376265330121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4816437547353835020440161 3612328160515376265330121)
        ·
          refine ⟨2709246120386532198997591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612328160515376265330121 2709246120386532198997591)
          ·
            refine ⟨4063869180579798298496387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709246120386532198997591 4063869180579798298496387)
            ·
              refine ⟨6095803770869697447744581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063869180579798298496387 6095803770869697447744581)
              ·
                refine ⟨1142963207038068271452109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6095803770869697447744581 1142963207038068271452109)
                ·
                  refine ⟨428611202639275601794541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142963207038068271452109 428611202639275601794541)
                  ·
                    rfl

theorem cell21_1878114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1878114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878114 prefixEnd_1878114 := by exact prefixLift 1878114
  have htrace : WordTrace (prefixWord ++ tailWord_1878114) baseStart_1878114 baseEnd_1878114 := by
    simpa [prefixWord, tailWord_1878114, baseEnd_1878114] using wordTrace_append hprefix tailTrace_1878114
  have hstable : (prefixWord ++ tailWord_1878114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878114).length < 2 ^ (prefixWord ++ tailWord_1878114).sum := by decide
  have hdescent : baseEnd_1878114 < baseStart_1878114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878153 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_1878153 : Nat := 118140960795 + 1878153 * 2 ^ 59
def prefixEnd_1878153 : Nat := 4983230072969 + 3 ^ 40 * 1878153 * 2
def baseEnd_1878153 : Nat := 428620102970620200644461

theorem tailTrace_1878153 : CollatzResearch.WordTrace tailWord_1878153 prefixEnd_1878153 428620102970620200644461 := by
  unfold tailWord_1878153
  simp only [CollatzResearch.WordTrace]
  refine ⟨68501867564779918840263113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45667911709853279226842075 68501867564779918840263113)
  ·
    refine ⟨51376400673584939130197335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68501867564779918840263113 51376400673584939130197335)
    ·
      refine ⟨77064601010377408695296003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51376400673584939130197335 77064601010377408695296003)
      ·
        refine ⟨115596901515566113042944005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77064601010377408695296003 115596901515566113042944005)
        ·
          refine ⟨21674419034168646195552001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115596901515566113042944005 21674419034168646195552001)
          ·
            refine ⟨16255814275626484646664001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21674419034168646195552001 16255814275626484646664001)
            ·
              refine ⟨12191860706719863484998001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16255814275626484646664001 12191860706719863484998001)
              ·
                refine ⟨9143895530039897613748501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12191860706719863484998001 9143895530039897613748501)
                ·
                  refine ⟨428620102970620200644461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9143895530039897613748501 428620102970620200644461)
                  ·
                    rfl

theorem cell21_1878153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_1878153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878153 prefixEnd_1878153 := by exact prefixLift 1878153
  have htrace : WordTrace (prefixWord ++ tailWord_1878153) baseStart_1878153 baseEnd_1878153 := by
    simpa [prefixWord, tailWord_1878153, baseEnd_1878153] using wordTrace_append hprefix tailTrace_1878153
  have hstable : (prefixWord ++ tailWord_1878153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878153).length < 2 ^ (prefixWord ++ tailWord_1878153).sum := by decide
  have hdescent : baseEnd_1878153 < baseStart_1878153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878232 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_1878232 : Nat := 118140960795 + 1878232 * 2 ^ 59
def prefixEnd_1878232 : Nat := 4983230072969 + 3 ^ 40 * 1878232 * 2
def baseEnd_1878232 : Nat := 428638131846933618827633

theorem tailTrace_1878232 : CollatzResearch.WordTrace tailWord_1878232 prefixEnd_1878232 428638131846933618827633 := by
  unfold tailWord_1878232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34252374465746857666194475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45669832620995810221592633 34252374465746857666194475)
  ·
    refine ⟨51378561698620286499291713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34252374465746857666194475 51378561698620286499291713)
    ·
      refine ⟨38533921273965214874468785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51378561698620286499291713 38533921273965214874468785)
      ·
        refine ⟨28900440955473911155851589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38533921273965214874468785 28900440955473911155851589)
        ·
          refine ⟨5418832679151358341722173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28900440955473911155851589 5418832679151358341722173)
          ·
            refine ⟨2032062254681759378145815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5418832679151358341722173 2032062254681759378145815)
            ·
              refine ⟨3048093382022639067218723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032062254681759378145815 3048093382022639067218723)
              ·
                refine ⟨4572140073033958600828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048093382022639067218723 4572140073033958600828085)
                ·
                  refine ⟨428638131846933618827633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4572140073033958600828085 428638131846933618827633)
                  ·
                    rfl

theorem cell21_1878232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_1878232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878232 prefixEnd_1878232 := by exact prefixLift 1878232
  have htrace : WordTrace (prefixWord ++ tailWord_1878232) baseStart_1878232 baseEnd_1878232 := by
    simpa [prefixWord, tailWord_1878232, baseEnd_1878232] using wordTrace_append hprefix tailTrace_1878232
  have hstable : (prefixWord ++ tailWord_1878232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878232).length < 2 ^ (prefixWord ++ tailWord_1878232).sum := by decide
  have hdescent : baseEnd_1878232 < baseStart_1878232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878319 : List Nat := [1, 1, 2, 1, 2, 1, 4, 9]
def baseStart_1878319 : Nat := 118140960795 + 1878319 * 2 ^ 59
def prefixEnd_1878319 : Nat := 4983230072969 + 3 ^ 40 * 1878319 * 2
def baseEnd_1878319 : Nat := 142885995477413600292485

theorem tailTrace_1878319 : CollatzResearch.WordTrace tailWord_1878319 prefixEnd_1878319 142885995477413600292485 := by
  unfold tailWord_1878319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68507922082178529190806011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45671948054785686127204007 68507922082178529190806011)
  ·
    refine ⟨102761883123267793786209017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68507922082178529190806011 102761883123267793786209017)
    ·
      refine ⟨77071412342450845339656763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102761883123267793786209017 77071412342450845339656763)
      ·
        refine ⟨115607118513676268009485145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77071412342450845339656763 115607118513676268009485145)
        ·
          refine ⟨86705338885257201007113859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115607118513676268009485145 86705338885257201007113859)
          ·
            refine ⟨130058008327885801510670789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86705338885257201007113859 130058008327885801510670789)
            ·
              refine ⟨24385876561478587783250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130058008327885801510670789 24385876561478587783250773)
              ·
                refine ⟨142885995477413600292485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24385876561478587783250773 142885995477413600292485)
                ·
                  rfl

theorem cell21_1878319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_1878319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878319 prefixEnd_1878319 := by exact prefixLift 1878319
  have htrace : WordTrace (prefixWord ++ tailWord_1878319) baseStart_1878319 baseEnd_1878319 := by
    simpa [prefixWord, tailWord_1878319, baseEnd_1878319] using wordTrace_append hprefix tailTrace_1878319
  have hstable : (prefixWord ++ tailWord_1878319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878319).length < 2 ^ (prefixWord ++ tailWord_1878319).sum := by decide
  have hdescent : baseEnd_1878319 < baseStart_1878319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878370 : List Nat := [3, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1878370 : Nat := 118140960795 + 1878370 * 2 ^ 59
def prefixEnd_1878370 : Nat := 4983230072969 + 3 ^ 40 * 1878370 * 2
def baseEnd_1878370 : Nat := 142889875109025348509117

theorem tailTrace_1878370 : CollatzResearch.WordTrace tailWord_1878370 prefixEnd_1878370 142889875109025348509117 := by
  unfold tailWord_1878370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127445551248441225228141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45673188136662509933941709 17127445551248441225228141)
  ·
    refine ⟨6422792081718165459460553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17127445551248441225228141 6422792081718165459460553)
    ·
      refine ⟨4817094061288624094595415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6422792081718165459460553 4817094061288624094595415)
      ·
        refine ⟨7225641091932936141893123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817094061288624094595415 7225641091932936141893123)
        ·
          refine ⟨10838461637899404212839685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225641091932936141893123 10838461637899404212839685)
          ·
            refine ⟨2032211557106138289907441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10838461637899404212839685 2032211557106138289907441)
            ·
              refine ⟨1524158667829603717430581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032211557106138289907441 1524158667829603717430581)
              ·
                refine ⟨142889875109025348509117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524158667829603717430581 142889875109025348509117)
                ·
                  rfl

theorem cell21_1878370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1878370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878370 prefixEnd_1878370 := by exact prefixLift 1878370
  have htrace : WordTrace (prefixWord ++ tailWord_1878370) baseStart_1878370 baseEnd_1878370 := by
    simpa [prefixWord, tailWord_1878370, baseEnd_1878370] using wordTrace_append hprefix tailTrace_1878370
  have hstable : (prefixWord ++ tailWord_1878370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878370).length < 2 ^ (prefixWord ++ tailWord_1878370).sum := by decide
  have hdescent : baseEnd_1878370 < baseStart_1878370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878381 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1878381 : Nat := 118140960795 + 1878381 * 2 ^ 59
def prefixEnd_1878381 : Nat := 4983230072969 + 3 ^ 40 * 1878381 * 2
def baseEnd_1878381 : Nat := 428672135676942470843995

theorem tailTrace_1878381 : CollatzResearch.WordTrace tailWord_1878381 prefixEnd_1878381 428672135676942470843995 := by
  unfold tailWord_1878381
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510183407953913779562997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45673455605302609186375331 68510183407953913779562997)
  ·
    refine ⟨6422829694495679416834031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68510183407953913779562997 6422829694495679416834031)
    ·
      refine ⟨9634244541743519125251047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6422829694495679416834031 9634244541743519125251047)
      ·
        refine ⟨14451366812615278687876571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634244541743519125251047 14451366812615278687876571)
        ·
          refine ⟨21677050218922918031814857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451366812615278687876571 21677050218922918031814857)
          ·
            refine ⟨16257787664192188523861143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21677050218922918031814857 16257787664192188523861143)
            ·
              refine ⟨24386681496288282785791715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257787664192188523861143 24386681496288282785791715)
              ·
                refine ⟨36580022244432424178687573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24386681496288282785791715 36580022244432424178687573)
                ·
                  refine ⟨428672135676942470843995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36580022244432424178687573 428672135676942470843995)
                  ·
                    rfl

theorem cell21_1878381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1878381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878381 prefixEnd_1878381 := by exact prefixLift 1878381
  have htrace : WordTrace (prefixWord ++ tailWord_1878381) baseStart_1878381 baseEnd_1878381 := by
    simpa [prefixWord, tailWord_1878381, baseEnd_1878381] using wordTrace_append hprefix tailTrace_1878381
  have hstable : (prefixWord ++ tailWord_1878381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878381).length < 2 ^ (prefixWord ++ tailWord_1878381).sum := by decide
  have hdescent : baseEnd_1878381 < baseStart_1878381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878384 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_1878384 : Nat := 118140960795 + 1878384 * 2 ^ 59
def prefixEnd_1878384 : Nat := 4983230072969 + 3 ^ 40 * 1878384 * 2
def baseEnd_1878384 : Nat := 428672820317815132293989

theorem tailTrace_1878384 : CollatzResearch.WordTrace tailWord_1878384 prefixEnd_1878384 428672820317815132293989 := by
  unfold tailWord_1878384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255146413471522645961103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45673528551295363527948137 34255146413471522645961103)
  ·
    refine ⟨51382719620207283968941655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255146413471522645961103 51382719620207283968941655)
    ·
      refine ⟨77074079430310925953412483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51382719620207283968941655 77074079430310925953412483)
      ·
        refine ⟨115611119145466388930118725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77074079430310925953412483 115611119145466388930118725)
        ·
          refine ⟨21677084839774947924397261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115611119145466388930118725 21677084839774947924397261)
          ·
            refine ⟨8128906814915605471648973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21677084839774947924397261 8128906814915605471648973)
            ·
              refine ⟨3048340055593352051868365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8128906814915605471648973 3048340055593352051868365)
              ·
                refine ⟨1143127520847507019450637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3048340055593352051868365 1143127520847507019450637)
                ·
                  refine ⟨428672820317815132293989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143127520847507019450637 428672820317815132293989)
                  ·
                    rfl

theorem cell21_1878384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_1878384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878384 prefixEnd_1878384 := by exact prefixLift 1878384
  have htrace : WordTrace (prefixWord ++ tailWord_1878384) baseStart_1878384 baseEnd_1878384 := by
    simpa [prefixWord, tailWord_1878384, baseEnd_1878384] using wordTrace_append hprefix tailTrace_1878384
  have hstable : (prefixWord ++ tailWord_1878384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878384).length < 2 ^ (prefixWord ++ tailWord_1878384).sum := by decide
  have hdescent : baseEnd_1878384 < baseStart_1878384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878395 : List Nat := [1, 1, 1, 1, 1, 7, 9]
def baseStart_1878395 : Nat := 118140960795 + 1878395 * 2 ^ 59
def prefixEnd_1878395 : Nat := 4983230072969 + 3 ^ 40 * 1878395 * 2
def baseEnd_1878395 : Nat := 47630592296409061956737

theorem tailTrace_1878395 : CollatzResearch.WordTrace tailWord_1878395 prefixEnd_1878395 47630592296409061956737 := by
  unfold tailWord_1878395
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510694029903194170572639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45673796019935462780381759 68510694029903194170572639)
  ·
    refine ⟨102766041044854791255858959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68510694029903194170572639 102766041044854791255858959)
    ·
      refine ⟨154149061567282186883788439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102766041044854791255858959 154149061567282186883788439)
      ·
        refine ⟨231223592350923280325682659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154149061567282186883788439 231223592350923280325682659)
        ·
          refine ⟨346835388526384920488523989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231223592350923280325682659 346835388526384920488523989)
          ·
            refine ⟨8128954418587146573949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346835388526384920488523989 8128954418587146573949781)
            ·
              refine ⟨47630592296409061956737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8128954418587146573949781 47630592296409061956737)
              ·
                rfl

theorem cell21_1878395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_1878395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878395 prefixEnd_1878395 := by exact prefixLift 1878395
  have htrace : WordTrace (prefixWord ++ tailWord_1878395) baseStart_1878395 baseEnd_1878395 := by
    simpa [prefixWord, tailWord_1878395, baseEnd_1878395] using wordTrace_append hprefix tailTrace_1878395
  have hstable : (prefixWord ++ tailWord_1878395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878395).length < 2 ^ (prefixWord ++ tailWord_1878395).sum := by decide
  have hdescent : baseEnd_1878395 < baseStart_1878395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878412 : List Nat := [2, 2, 1, 2, 1, 5, 2, 6]
def baseStart_1878412 : Nat := 118140960795 + 1878412 * 2 ^ 59
def prefixEnd_1878412 : Nat := 4983230072969 + 3 ^ 40 * 1878412 * 2
def baseEnd_1878412 : Nat := 142893070099764435275755

theorem tailTrace_1878412 : CollatzResearch.WordTrace tailWord_1878412 prefixEnd_1878412 142893070099764435275755 := by
  unfold tailWord_1878412
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255657035420803036970745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45674209380561070715960993 34255657035420803036970745)
  ·
    refine ⟨25691742776565602277728059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34255657035420803036970745 25691742776565602277728059)
    ·
      refine ⟨38537614164848403416592089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25691742776565602277728059 38537614164848403416592089)
      ·
        refine ⟨28903210623636302562444067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38537614164848403416592089 28903210623636302562444067)
        ·
          refine ⟨43354815935454453843666101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28903210623636302562444067 43354815935454453843666101)
          ·
            refine ⟨4064513993948855047843697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43354815935454453843666101 4064513993948855047843697)
            ·
              refine ⟨3048385495461641285882773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064513993948855047843697 3048385495461641285882773)
              ·
                refine ⟨142893070099764435275755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3048385495461641285882773 142893070099764435275755)
                ·
                  rfl

theorem cell21_1878412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_1878412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878412 prefixEnd_1878412 := by exact prefixLift 1878412
  have htrace : WordTrace (prefixWord ++ tailWord_1878412) baseStart_1878412 baseEnd_1878412 := by
    simpa [prefixWord, tailWord_1878412, baseEnd_1878412] using wordTrace_append hprefix tailTrace_1878412
  have hstable : (prefixWord ++ tailWord_1878412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878412).length < 2 ^ (prefixWord ++ tailWord_1878412).sum := by decide
  have hdescent : baseEnd_1878412 < baseStart_1878412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878452 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1878452 : Nat := 118140960795 + 1878452 * 2 ^ 59
def prefixEnd_1878452 : Nat := 4983230072969 + 3 ^ 40 * 1878452 * 2
def baseEnd_1878452 : Nat := 428688338844262125160517

theorem tailTrace_1878452 : CollatzResearch.WordTrace tailWord_1878452 prefixEnd_1878452 428688338844262125160517 := by
  unfold tailWord_1878452
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256386495348346452698805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45675181993797795270265073 34256386495348346452698805)
  ·
    refine ⟨3211536233938907479940513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34256386495348346452698805 3211536233938907479940513)
    ·
      refine ⟨2408652175454180609955385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211536233938907479940513 2408652175454180609955385)
      ·
        refine ⟨1806489131590635457466539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408652175454180609955385 1806489131590635457466539)
        ·
          refine ⟨2709733697385953186199809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806489131590635457466539 2709733697385953186199809)
          ·
            refine ⟨2032300273039464889649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709733697385953186199809 2032300273039464889649857)
            ·
              refine ⟨1524225204779598667237393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032300273039464889649857 1524225204779598667237393)
              ·
                refine ⟨1143168903584699000428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524225204779598667237393 1143168903584699000428045)
                ·
                  refine ⟨428688338844262125160517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143168903584699000428045 428688338844262125160517)
                  ·
                    rfl

theorem cell21_1878452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1878452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878452 prefixEnd_1878452 := by exact prefixLift 1878452
  have htrace : WordTrace (prefixWord ++ tailWord_1878452) baseStart_1878452 baseEnd_1878452 := by
    simpa [prefixWord, tailWord_1878452, baseEnd_1878452] using wordTrace_append hprefix tailTrace_1878452
  have hstable : (prefixWord ++ tailWord_1878452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878452).length < 2 ^ (prefixWord ++ tailWord_1878452).sum := by decide
  have hdescent : baseEnd_1878452 < baseStart_1878452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878533 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1878533 : Nat := 118140960795 + 1878533 * 2 ^ 59
def prefixEnd_1878533 : Nat := 4983230072969 + 3 ^ 40 * 1878533 * 2
def baseEnd_1878533 : Nat := 428706824147823984310351

theorem tailTrace_1878533 : CollatzResearch.WordTrace tailWord_1878533 prefixEnd_1878533 428706824147823984310351 := by
  unfold tailWord_1878533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68515727303403243739096253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45677151535602162492730835 68515727303403243739096253)
  ·
    refine ⟨25693397738776216402161095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68515727303403243739096253 25693397738776216402161095)
    ·
      refine ⟨38540096608164324603241643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25693397738776216402161095 38540096608164324603241643)
      ·
        refine ⟨57810144912246486904862465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38540096608164324603241643 57810144912246486904862465)
        ·
          refine ⟨43357608684184865178646849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57810144912246486904862465 43357608684184865178646849)
          ·
            refine ⟨32518206513138648883985137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43357608684184865178646849 32518206513138648883985137)
            ·
              refine ⟨24388654884853986662988853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32518206513138648883985137 24388654884853986662988853)
              ·
                refine ⟨2286436395455061249655205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24388654884853986662988853 2286436395455061249655205)
                ·
                  refine ⟨428706824147823984310351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2286436395455061249655205 428706824147823984310351)
                  ·
                    rfl

theorem cell21_1878533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1878533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878533 prefixEnd_1878533 := by exact prefixLift 1878533
  have htrace : WordTrace (prefixWord ++ tailWord_1878533) baseStart_1878533 baseEnd_1878533 := by
    simpa [prefixWord, tailWord_1878533, baseEnd_1878533] using wordTrace_append hprefix tailTrace_1878533
  have hstable : (prefixWord ++ tailWord_1878533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878533).length < 2 ^ (prefixWord ++ tailWord_1878533).sum := by decide
  have hdescent : baseEnd_1878533 < baseStart_1878533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878547 : List Nat := [1, 1, 1, 2, 1, 5, 3, 7]
def baseStart_1878547 : Nat := 118140960795 + 1878547 * 2 ^ 59
def prefixEnd_1878547 : Nat := 4983230072969 + 3 ^ 40 * 1878547 * 2
def baseEnd_1878547 : Nat := 142903339712854357025663

theorem tailTrace_1878547 : CollatzResearch.WordTrace tailWord_1878547 prefixEnd_1878547 142903339712854357025663 := by
  unfold tailWord_1878547
  simp only [CollatzResearch.WordTrace]
  refine ⟨68516237925352524130105895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45677491950235016086737263 68516237925352524130105895)
  ·
    refine ⟨102774356888028786195158843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68516237925352524130105895 102774356888028786195158843)
    ·
      refine ⟨154161535332043179292738265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102774356888028786195158843 154161535332043179292738265)
      ·
        refine ⟨115621151499032384469553699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154161535332043179292738265 115621151499032384469553699)
        ·
          refine ⟨173431727248548576704330549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115621151499032384469553699 173431727248548576704330549)
          ·
            refine ⟨16259224429551429066030989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173431727248548576704330549 16259224429551429066030989)
            ·
              refine ⟨6097209161081785899761621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16259224429551429066030989 6097209161081785899761621)
              ·
                refine ⟨142903339712854357025663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6097209161081785899761621 142903339712854357025663)
                ·
                  rfl

theorem cell21_1878547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_1878547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878547 prefixEnd_1878547 := by exact prefixLift 1878547
  have htrace : WordTrace (prefixWord ++ tailWord_1878547) baseStart_1878547 baseEnd_1878547 := by
    simpa [prefixWord, tailWord_1878547, baseEnd_1878547] using wordTrace_append hprefix tailTrace_1878547
  have hstable : (prefixWord ++ tailWord_1878547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878547).length < 2 ^ (prefixWord ++ tailWord_1878547).sum := by decide
  have hdescent : baseEnd_1878547 < baseStart_1878547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878826 : List Nat := [3, 1, 4, 3, 1, 1, 3, 5]
def baseStart_1878826 : Nat := 118140960795 + 1878826 * 2 ^ 59
def prefixEnd_1878826 : Nat := 4983230072969 + 3 ^ 40 * 1878826 * 2
def baseEnd_1878826 : Nat := 142924563579906861975473

theorem tailTrace_1878826 : CollatzResearch.WordTrace tailWord_1878826 prefixEnd_1878826 142924563579906861975473 := by
  unfold tailWord_1878826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131603472835438694878083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45684275927561169853008221 17131603472835438694878083)
  ·
    refine ⟨25697405209253158042317125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17131603472835438694878083 25697405209253158042317125)
    ·
      refine ⟨4818263476734967132934461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25697405209253158042317125 4818263476734967132934461)
      ·
        refine ⟨1806848803775612674850423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4818263476734967132934461 1806848803775612674850423)
        ·
          refine ⟨2710273205663419012275635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806848803775612674850423 2710273205663419012275635)
          ·
            refine ⟨4065409808495128518413453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710273205663419012275635 4065409808495128518413453)
            ·
              refine ⟨1524528678185673194405045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4065409808495128518413453 1524528678185673194405045)
              ·
                refine ⟨142924563579906861975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524528678185673194405045 142924563579906861975473)
                ·
                  rfl

theorem cell21_1878826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_1878826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878826 prefixEnd_1878826 := by exact prefixLift 1878826
  have htrace : WordTrace (prefixWord ++ tailWord_1878826) baseStart_1878826 baseEnd_1878826 := by
    simpa [prefixWord, tailWord_1878826, baseEnd_1878826] using wordTrace_append hprefix tailTrace_1878826
  have hstable : (prefixWord ++ tailWord_1878826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878826).length < 2 ^ (prefixWord ++ tailWord_1878826).sum := by decide
  have hdescent : baseEnd_1878826 < baseStart_1878826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878896 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1878896 : Nat := 118140960795 + 1878896 * 2 ^ 59
def prefixEnd_1878896 : Nat := 4983230072969 + 3 ^ 40 * 1878896 * 2
def baseEnd_1878896 : Nat := 428789665693416019759609

theorem tailTrace_1878896 : CollatzResearch.WordTrace tailWord_1878896 prefixEnd_1878896 428789665693416019759609 := by
  unfold tailWord_1878896
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264483500544078367280271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45685978000725437823040361 34264483500544078367280271)
  ·
    refine ⟨51396725250816117550920407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34264483500544078367280271 51396725250816117550920407)
    ·
      refine ⟨77095087876224176326380611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51396725250816117550920407 77095087876224176326380611)
      ·
        refine ⟨115642631814336264489570917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77095087876224176326380611 115642631814336264489570917)
        ·
          refine ⟨21682993465188049591794547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115642631814336264489570917 21682993465188049591794547)
          ·
            refine ⟨32524490197782074387691821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21682993465188049591794547 32524490197782074387691821)
            ·
              refine ⟨12196683824168277895384433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32524490197782074387691821 12196683824168277895384433)
              ·
                refine ⟨9147512868126208421538325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12196683824168277895384433 9147512868126208421538325)
                ·
                  refine ⟨428789665693416019759609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9147512868126208421538325 428789665693416019759609)
                  ·
                    rfl

theorem cell21_1878896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1878896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878896 prefixEnd_1878896 := by exact prefixLift 1878896
  have htrace : WordTrace (prefixWord ++ tailWord_1878896) baseStart_1878896 baseEnd_1878896 := by
    simpa [prefixWord, tailWord_1878896, baseEnd_1878896] using wordTrace_append hprefix tailTrace_1878896
  have hstable : (prefixWord ++ tailWord_1878896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878896).length < 2 ^ (prefixWord ++ tailWord_1878896).sum := by decide
  have hdescent : baseEnd_1878896 < baseStart_1878896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878899 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 3]
def baseStart_1878899 : Nat := 118140960795 + 1878899 * 2 ^ 59
def prefixEnd_1878899 : Nat := 4983230072969 + 3 ^ 40 * 1878899 * 2
def baseEnd_1878899 : Nat := 428790350334288681209603

theorem tailTrace_1878899 : CollatzResearch.WordTrace tailWord_1878899 prefixEnd_1878899 428790350334288681209603 := by
  unfold tailWord_1878899
  simp only [CollatzResearch.WordTrace]
  refine ⟨68529076420077288246919751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45686050946718192164613167 68529076420077288246919751)
  ·
    refine ⟨102793614630115932370379627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68529076420077288246919751 102793614630115932370379627)
    ·
      refine ⟨154190421945173898555569441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102793614630115932370379627 154190421945173898555569441)
      ·
        refine ⟨115642816458880423916677081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154190421945173898555569441 115642816458880423916677081)
        ·
          refine ⟨86732112344160317937507811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115642816458880423916677081 86732112344160317937507811)
          ·
            refine ⟨130098168516240476906261717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86732112344160317937507811 130098168516240476906261717)
            ·
              refine ⟨3049175824599386177490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130098168516240476906261717 3049175824599386177490509)
              ·
                refine ⟨1143440934224769816558941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049175824599386177490509 1143440934224769816558941)
                ·
                  refine ⟨428790350334288681209603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143440934224769816558941 428790350334288681209603)
                  ·
                    rfl

theorem cell21_1878899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].length) (baseStart_1878899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1878899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1878899 prefixEnd_1878899 := by exact prefixLift 1878899
  have htrace : WordTrace (prefixWord ++ tailWord_1878899) baseStart_1878899 baseEnd_1878899 := by
    simpa [prefixWord, tailWord_1878899, baseEnd_1878899] using wordTrace_append hprefix tailTrace_1878899
  have hstable : (prefixWord ++ tailWord_1878899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878899).length < 2 ^ (prefixWord ++ tailWord_1878899).sum := by decide
  have hdescent : baseEnd_1878899 < baseStart_1878899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879124 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1879124 : Nat := 118140960795 + 1879124 * 2 ^ 59
def prefixEnd_1879124 : Nat := 4983230072969 + 3 ^ 40 * 1879124 * 2
def baseEnd_1879124 : Nat := 428841698399738289959143

theorem tailTrace_1879124 : CollatzResearch.WordTrace tailWord_1879124 prefixEnd_1879124 428841698399738289959143 := by
  unfold tailWord_1879124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268641422131075836930213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45691521896174767782573617 34268641422131075836930213)
  ·
    refine ⟨6425370266649576719424415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34268641422131075836930213 6425370266649576719424415)
    ·
      refine ⟨9638055399974365079136623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425370266649576719424415 9638055399974365079136623)
      ·
        refine ⟨14457083099961547618704935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638055399974365079136623 14457083099961547618704935)
        ·
          refine ⟨21685624649942321428057403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457083099961547618704935 21685624649942321428057403)
          ·
            refine ⟨32528436974913482142086105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21685624649942321428057403 32528436974913482142086105)
            ·
              refine ⟨24396327731185111606564579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32528436974913482142086105 24396327731185111606564579)
              ·
                refine ⟨36594491596777667409846869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24396327731185111606564579 36594491596777667409846869)
                ·
                  refine ⟨428841698399738289959143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36594491596777667409846869 428841698399738289959143)
                  ·
                    rfl

theorem cell21_1879124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1879124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879124 prefixEnd_1879124 := by exact prefixLift 1879124
  have htrace : WordTrace (prefixWord ++ tailWord_1879124) baseStart_1879124 baseEnd_1879124 := by
    simpa [prefixWord, tailWord_1879124, baseEnd_1879124] using wordTrace_append hprefix tailTrace_1879124
  have hstable : (prefixWord ++ tailWord_1879124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879124).length < 2 ^ (prefixWord ++ tailWord_1879124).sum := by decide
  have hdescent : baseEnd_1879124 < baseStart_1879124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879141 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_1879141 : Nat := 118140960795 + 1879141 * 2 ^ 59
def prefixEnd_1879141 : Nat := 4983230072969 + 3 ^ 40 * 1879141 * 2
def baseEnd_1879141 : Nat := 428845578031350038175775

theorem tailTrace_1879141 : CollatzResearch.WordTrace tailWord_1879141 prefixEnd_1879141 428845578031350038175775 := by
  unfold tailWord_1879141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68537902885200563577229277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45691935256800375718152851 68537902885200563577229277)
  ·
    refine ⟨25701713581950211341460979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68537902885200563577229277 25701713581950211341460979)
    ·
      refine ⟨38552570372925317012191469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25701713581950211341460979 38552570372925317012191469)
      ·
        refine ⟨14457213889846993879571801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38552570372925317012191469 14457213889846993879571801)
        ·
          refine ⟨10842910417385245409678851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14457213889846993879571801 10842910417385245409678851)
          ·
            refine ⟨16264365626077868114518277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842910417385245409678851 16264365626077868114518277)
            ·
              refine ⟨3049568554889600271472177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16264365626077868114518277 3049568554889600271472177)
              ·
                refine ⟨2287176416167200203604133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049568554889600271472177 2287176416167200203604133)
                ·
                  refine ⟨428845578031350038175775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287176416167200203604133 428845578031350038175775)
                  ·
                    rfl

theorem cell21_1879141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_1879141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879141 prefixEnd_1879141 := by exact prefixLift 1879141
  have htrace : WordTrace (prefixWord ++ tailWord_1879141) baseStart_1879141 baseEnd_1879141 := by
    simpa [prefixWord, tailWord_1879141, baseEnd_1879141] using wordTrace_append hprefix tailTrace_1879141
  have hstable : (prefixWord ++ tailWord_1879141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879141).length < 2 ^ (prefixWord ++ tailWord_1879141).sum := by decide
  have hdescent : baseEnd_1879141 < baseStart_1879141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879172 : List Nat := [2, 3, 2, 1, 2, 3, 3, 5]
def baseStart_1879172 : Nat := 118140960795 + 1879172 * 2 ^ 59
def prefixEnd_1879172 : Nat := 4983230072969 + 3 ^ 40 * 1879172 * 2
def baseEnd_1879172 : Nat := 142950884217900291053015

theorem tailTrace_1879172 : CollatzResearch.WordTrace tailWord_1879172 prefixEnd_1879172 142950884217900291053015 := by
  unfold tailWord_1879172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34269516774044127935803885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45692689032058837247738513 34269516774044127935803885)
  ·
    refine ⟨12851068790266547975926457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34269516774044127935803885 12851068790266547975926457)
    ·
      refine ⟨9638301592699910981944843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12851068790266547975926457 9638301592699910981944843)
      ·
        refine ⟨14457452389049866472917265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638301592699910981944843 14457452389049866472917265)
        ·
          refine ⟨10843089291787399854687949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14457452389049866472917265 10843089291787399854687949)
          ·
            refine ⟨4066158484420274945507981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10843089291787399854687949 4066158484420274945507981)
            ·
              refine ⟨1524809431657603104565493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066158484420274945507981 1524809431657603104565493)
              ·
                refine ⟨142950884217900291053015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524809431657603104565493 142950884217900291053015)
                ·
                  rfl

theorem cell21_1879172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_1879172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879172 prefixEnd_1879172 := by exact prefixLift 1879172
  have htrace : WordTrace (prefixWord ++ tailWord_1879172) baseStart_1879172 baseEnd_1879172 := by
    simpa [prefixWord, tailWord_1879172, baseEnd_1879172] using wordTrace_append hprefix tailTrace_1879172
  have hstable : (prefixWord ++ tailWord_1879172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879172).length < 2 ^ (prefixWord ++ tailWord_1879172).sum := by decide
  have hdescent : baseEnd_1879172 < baseStart_1879172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879200 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1879200 : Nat := 118140960795 + 1879200 * 2 ^ 59
def prefixEnd_1879200 : Nat := 4983230072969 + 3 ^ 40 * 1879200 * 2
def baseEnd_1879200 : Nat := 428859042635179046692321

theorem tailTrace_1879200 : CollatzResearch.WordTrace tailWord_1879200 prefixEnd_1879200 428859042635179046692321 := by
  unfold tailWord_1879200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270027395993408326813527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45693369861324544435751369 34270027395993408326813527)
  ·
    refine ⟨51405041093990112490220291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34270027395993408326813527 51405041093990112490220291)
    ·
      refine ⟨77107561640985168735330437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51405041093990112490220291 77107561640985168735330437)
      ·
        refine ⟨14457667807684719137874457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77107561640985168735330437 14457667807684719137874457)
        ·
          refine ⟨10843250855763539353405843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14457667807684719137874457 10843250855763539353405843)
          ·
            refine ⟨16264876283645309030108765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843250855763539353405843 16264876283645309030108765)
            ·
              refine ⟨6099328606366990886290787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16264876283645309030108765 6099328606366990886290787)
              ·
                refine ⟨9148992909550486329436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099328606366990886290787 9148992909550486329436181)
                ·
                  refine ⟨428859042635179046692321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9148992909550486329436181 428859042635179046692321)
                  ·
                    rfl

theorem cell21_1879200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1879200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879200 prefixEnd_1879200 := by exact prefixLift 1879200
  have htrace : WordTrace (prefixWord ++ tailWord_1879200) baseStart_1879200 baseEnd_1879200 := by
    simpa [prefixWord, tailWord_1879200, baseEnd_1879200] using wordTrace_append hprefix tailTrace_1879200
  have hstable : (prefixWord ++ tailWord_1879200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879200).length < 2 ^ (prefixWord ++ tailWord_1879200).sum := by decide
  have hdescent : baseEnd_1879200 < baseStart_1879200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879231 : List Nat := [1, 1, 2, 2, 2, 2, 6, 5]
def baseStart_1879231 : Nat := 118140960795 + 1879231 * 2 ^ 59
def prefixEnd_1879231 : Nat := 4983230072969 + 3 ^ 40 * 1879231 * 2
def baseEnd_1879231 : Nat := 142955372419176627225197

theorem tailTrace_1879231 : CollatzResearch.WordTrace tailWord_1879231 prefixEnd_1879231 142955372419176627225197 := by
  unfold tailWord_1879231
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541185454874508948005547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694123636583005965337031 68541185454874508948005547)
  ·
    refine ⟨102811778182311763422008321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68541185454874508948005547 102811778182311763422008321)
    ·
      refine ⟨77108833636733822566506241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102811778182311763422008321 77108833636733822566506241)
      ·
        refine ⟨57831625227550366924879681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77108833636733822566506241 57831625227550366924879681)
        ·
          refine ⟨43373718920662775193659761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57831625227550366924879681 43373718920662775193659761)
          ·
            refine ⟨32530289190497081395244821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43373718920662775193659761 32530289190497081395244821)
            ·
              refine ⟨1524857305804550690402101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32530289190497081395244821 1524857305804550690402101)
              ·
                refine ⟨142955372419176627225197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524857305804550690402101 142955372419176627225197)
                ·
                  rfl

theorem cell21_1879231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].length) (baseStart_1879231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879231 prefixEnd_1879231 := by exact prefixLift 1879231
  have htrace : WordTrace (prefixWord ++ tailWord_1879231) baseStart_1879231 baseEnd_1879231 := by
    simpa [prefixWord, tailWord_1879231, baseEnd_1879231] using wordTrace_append hprefix tailTrace_1879231
  have hstable : (prefixWord ++ tailWord_1879231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879231).length < 2 ^ (prefixWord ++ tailWord_1879231).sum := by decide
  have hdescent : baseEnd_1879231 < baseStart_1879231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879254 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1879254 : Nat := 118140960795 + 1879254 * 2 ^ 59
def prefixEnd_1879254 : Nat := 4983230072969 + 3 ^ 40 * 1879254 * 2
def baseEnd_1879254 : Nat := 428871366170886952792211

theorem tailTrace_1879254 : CollatzResearch.WordTrace tailWord_1879254 prefixEnd_1879254 428871366170886952792211 := by
  unfold tailWord_1879254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283876520861948992255801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45694682889194122584061877 4283876520861948992255801)
  ·
    refine ⟨3212907390646461744191851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4283876520861948992255801 3212907390646461744191851)
    ·
      refine ⟨4819361085969692616287777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3212907390646461744191851 4819361085969692616287777)
      ·
        refine ⟨3614520814477269462215833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819361085969692616287777 3614520814477269462215833)
        ·
          refine ⟨2710890610857952096661875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614520814477269462215833 2710890610857952096661875)
          ·
            refine ⟨4066335916286928144992813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710890610857952096661875 4066335916286928144992813)
            ·
              refine ⟨1524875968607598054372305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066335916286928144992813 1524875968607598054372305)
              ·
                refine ⟨1143656976455698540779229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524875968607598054372305 1143656976455698540779229)
                ·
                  refine ⟨428871366170886952792211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143656976455698540779229 428871366170886952792211)
                  ·
                    rfl

theorem cell21_1879254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1879254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879254 prefixEnd_1879254 := by exact prefixLift 1879254
  have htrace : WordTrace (prefixWord ++ tailWord_1879254) baseStart_1879254 baseEnd_1879254 := by
    simpa [prefixWord, tailWord_1879254, baseEnd_1879254] using wordTrace_append hprefix tailTrace_1879254
  have hstable : (prefixWord ++ tailWord_1879254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879254).length < 2 ^ (prefixWord ++ tailWord_1879254).sum := by decide
  have hdescent : baseEnd_1879254 < baseStart_1879254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879259 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_1879259 : Nat := 118140960795 + 1879259 * 2 ^ 59
def prefixEnd_1879259 : Nat := 4983230072969 + 3 ^ 40 * 1879259 * 2
def baseEnd_1879259 : Nat := 428872507239008055208867

theorem tailTrace_1879259 : CollatzResearch.WordTrace tailWord_1879259 prefixEnd_1879259 428872507239008055208867 := by
  unfold tailWord_1879259
  simp only [CollatzResearch.WordTrace]
  refine ⟨68542206698773069730024831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694804465848713153349887 68542206698773069730024831)
  ·
    refine ⟨102813310048159604595037247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68542206698773069730024831 102813310048159604595037247)
    ·
      refine ⟨154219965072239406892555871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102813310048159604595037247 154219965072239406892555871)
      ·
        refine ⟨231329947608359110338833807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154219965072239406892555871 231329947608359110338833807)
        ·
          refine ⟨346994921412538665508250711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231329947608359110338833807 346994921412538665508250711)
          ·
            refine ⟨520492382118807998262376067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346994921412538665508250711 520492382118807998262376067)
            ·
              refine ⟨780738573178211997393564101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520492382118807998262376067 780738573178211997393564101)
              ·
                refine ⟨146388482470914749511293269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780738573178211997393564101 146388482470914749511293269)
                ·
                  refine ⟨428872507239008055208867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146388482470914749511293269 428872507239008055208867)
                  ·
                    rfl

theorem cell21_1879259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_1879259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879259 prefixEnd_1879259 := by exact prefixLift 1879259
  have htrace : WordTrace (prefixWord ++ tailWord_1879259) baseStart_1879259 baseEnd_1879259 := by
    simpa [prefixWord, tailWord_1879259, baseEnd_1879259] using wordTrace_append hprefix tailTrace_1879259
  have hstable : (prefixWord ++ tailWord_1879259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879259).length < 2 ^ (prefixWord ++ tailWord_1879259).sum := by decide
  have hdescent : baseEnd_1879259 < baseStart_1879259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879290 : List Nat := [3, 1, 1, 1, 1, 4, 1, 9]
def baseStart_1879290 : Nat := 118140960795 + 1879290 * 2 ^ 59
def prefixEnd_1879290 : Nat := 4983230072969 + 3 ^ 40 * 1879290 * 2
def baseEnd_1879290 : Nat := 142959860620452963397379

theorem tailTrace_1879290 : CollatzResearch.WordTrace tailWord_1879290 prefixEnd_1879290 142959860620452963397379 := by
  unfold tailWord_1879290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17135834340415190506100831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45695558241107174682935549 17135834340415190506100831)
  ·
    refine ⟨25703751510622785759151247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17135834340415190506100831 25703751510622785759151247)
    ·
      refine ⟨38555627265934178638726871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25703751510622785759151247 38555627265934178638726871)
      ·
        refine ⟨57833440898901267958090307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38555627265934178638726871 57833440898901267958090307)
        ·
          refine ⟨86750161348351901937135461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57833440898901267958090307 86750161348351901937135461)
          ·
            refine ⟨16265655252815981613212899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86750161348351901937135461 16265655252815981613212899)
            ·
              refine ⟨24398482879223972419819349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265655252815981613212899 24398482879223972419819349)
              ·
                refine ⟨142959860620452963397379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24398482879223972419819349 142959860620452963397379)
                ·
                  rfl

theorem cell21_1879290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_1879290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879290 prefixEnd_1879290 := by exact prefixLift 1879290
  have htrace : WordTrace (prefixWord ++ tailWord_1879290) baseStart_1879290 baseEnd_1879290 := by
    simpa [prefixWord, tailWord_1879290, baseEnd_1879290] using wordTrace_append hprefix tailTrace_1879290
  have hstable : (prefixWord ++ tailWord_1879290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879290).length < 2 ^ (prefixWord ++ tailWord_1879290).sum := by decide
  have hdescent : baseEnd_1879290 < baseStart_1879290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879338 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1879338 : Nat := 118140960795 + 1879338 * 2 ^ 59
def prefixEnd_1879338 : Nat := 4983230072969 + 3 ^ 40 * 1879338 * 2
def baseEnd_1879338 : Nat := 428890536115321473392039

theorem tailTrace_1879338 : CollatzResearch.WordTrace tailWord_1879338 prefixEnd_1879338 428890536115321473392039 := by
  unfold tailWord_1879338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136272016371716555537667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45696725376991244148100445 17136272016371716555537667)
  ·
    refine ⟨25704408024557574833306501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17136272016371716555537667 25704408024557574833306501)
    ·
      refine ⟨4819576504604545281244969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25704408024557574833306501 4819576504604545281244969)
      ·
        refine ⟨3614682378453408960933727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819576504604545281244969 3614682378453408960933727)
        ·
          refine ⟨5422023567680113441400591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614682378453408960933727 5422023567680113441400591)
          ·
            refine ⟨8133035351520170162100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422023567680113441400591 8133035351520170162100887)
            ·
              refine ⟨12199553027280255243151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133035351520170162100887 12199553027280255243151331)
              ·
                refine ⟨18299329540920382864726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199553027280255243151331 18299329540920382864726997)
                ·
                  refine ⟨428890536115321473392039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18299329540920382864726997 428890536115321473392039)
                  ·
                    rfl

theorem cell21_1879338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1879338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879338 prefixEnd_1879338 := by exact prefixLift 1879338
  have htrace : WordTrace (prefixWord ++ tailWord_1879338) baseStart_1879338 baseEnd_1879338 := by
    simpa [prefixWord, tailWord_1879338, baseEnd_1879338] using wordTrace_append hprefix tailTrace_1879338
  have hstable : (prefixWord ++ tailWord_1879338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879338).length < 2 ^ (prefixWord ++ tailWord_1879338).sum := by decide
  have hdescent : baseEnd_1879338 < baseStart_1879338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879341 : List Nat := [1, 5, 3, 1, 1, 2, 3, 5]
def baseStart_1879341 : Nat := 118140960795 + 1879341 * 2 ^ 59
def prefixEnd_1879341 : Nat := 4983230072969 + 3 ^ 40 * 1879341 * 2
def baseEnd_1879341 : Nat := 142963740252064711614011

theorem tailTrace_1879341 : CollatzResearch.WordTrace tailWord_1879341 prefixEnd_1879341 142963740252064711614011 := by
  unfold tailWord_1879341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68545197484475997734509877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45696798322983998489673251 68545197484475997734509877)
  ·
    refine ⟨6426112264169624787610301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68545197484475997734509877 6426112264169624787610301)
    ·
      refine ⟨2409792099063609295353863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6426112264169624787610301 2409792099063609295353863)
      ·
        refine ⟨3614688148595413943030795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409792099063609295353863 3614688148595413943030795)
        ·
          refine ⟨5422032222893120914546193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614688148595413943030795 5422032222893120914546193)
          ·
            refine ⟨4066524167169840685909645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5422032222893120914546193 4066524167169840685909645)
            ·
              refine ⟨1524946562688690257216117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066524167169840685909645 1524946562688690257216117)
              ·
                refine ⟨142963740252064711614011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524946562688690257216117 142963740252064711614011)
                ·
                  rfl

theorem cell21_1879341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].length) (baseStart_1879341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879341 prefixEnd_1879341 := by exact prefixLift 1879341
  have htrace : WordTrace (prefixWord ++ tailWord_1879341) baseStart_1879341 baseEnd_1879341 := by
    simpa [prefixWord, tailWord_1879341, baseEnd_1879341] using wordTrace_append hprefix tailTrace_1879341
  have hstable : (prefixWord ++ tailWord_1879341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879341).length < 2 ^ (prefixWord ++ tailWord_1879341).sum := by decide
  have hdescent : baseEnd_1879341 < baseStart_1879341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879397 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1879397 : Nat := 118140960795 + 1879397 * 2 ^ 59
def prefixEnd_1879397 : Nat := 4983230072969 + 3 ^ 40 * 1879397 * 2
def baseEnd_1879397 : Nat := 428904000719150481908585

theorem tailTrace_1879397 : CollatzResearch.WordTrace tailWord_1879397 prefixEnd_1879397 428904000719150481908585 := by
  unfold tailWord_1879397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68547239972273119298548445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45698159981515412865698963 68547239972273119298548445)
  ·
    refine ⟨25705214989602419736955667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68547239972273119298548445 25705214989602419736955667)
    ·
      refine ⟨38557822484403629605433501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25705214989602419736955667 38557822484403629605433501)
      ·
        refine ⟨14459183431651361102037563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38557822484403629605433501 14459183431651361102037563)
        ·
          refine ⟨21688775147477041653056345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459183431651361102037563 21688775147477041653056345)
          ·
            refine ⟨16266581360607781239792259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21688775147477041653056345 16266581360607781239792259)
            ·
              refine ⟨24399872040911671859688389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16266581360607781239792259 24399872040911671859688389)
              ·
                refine ⟨4574976007670938473691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24399872040911671859688389 4574976007670938473691573)
                ·
                  refine ⟨428904000719150481908585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574976007670938473691573 428904000719150481908585)
                  ·
                    rfl

theorem cell21_1879397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1879397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879397 prefixEnd_1879397 := by exact prefixLift 1879397
  have htrace : WordTrace (prefixWord ++ tailWord_1879397) baseStart_1879397 baseEnd_1879397 := by
    simpa [prefixWord, tailWord_1879397, baseEnd_1879397] using wordTrace_append hprefix tailTrace_1879397
  have hstable : (prefixWord ++ tailWord_1879397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879397).length < 2 ^ (prefixWord ++ tailWord_1879397).sum := by decide
  have hdescent : baseEnd_1879397 < baseStart_1879397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879406 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1879406 : Nat := 118140960795 + 1879406 * 2 ^ 59
def prefixEnd_1879406 : Nat := 4983230072969 + 3 ^ 40 * 1879406 * 2
def baseEnd_1879406 : Nat := 428906054641768466258567

theorem tailTrace_1879406 : CollatzResearch.WordTrace tailWord_1879406 prefixEnd_1879406 428906054641768466258567 := by
  unfold tailWord_1879406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568446028655064229453259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45698378819493675890417381 8568446028655064229453259)
  ·
    refine ⟨12852669042982596344179889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568446028655064229453259 12852669042982596344179889)
    ·
      refine ⟨9639501782236947258134917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12852669042982596344179889 9639501782236947258134917)
      ·
        refine ⟨1807406584169427610900297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9639501782236947258134917 1807406584169427610900297)
        ·
          refine ⟨1355554938127070708175223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807406584169427610900297 1355554938127070708175223)
          ·
            refine ⟨2033332407190606062262835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355554938127070708175223 2033332407190606062262835)
            ·
              refine ⟨3049998610785909093394253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033332407190606062262835 3049998610785909093394253)
              ·
                refine ⟨1143749479044715910022845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049998610785909093394253 1143749479044715910022845)
                ·
                  refine ⟨428906054641768466258567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143749479044715910022845 428906054641768466258567)
                  ·
                    rfl

theorem cell21_1879406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1879406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879406 prefixEnd_1879406 := by exact prefixLift 1879406
  have htrace : WordTrace (prefixWord ++ tailWord_1879406) baseStart_1879406 baseEnd_1879406 := by
    simpa [prefixWord, tailWord_1879406, baseEnd_1879406] using wordTrace_append hprefix tailTrace_1879406
  have hstable : (prefixWord ++ tailWord_1879406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879406).length < 2 ^ (prefixWord ++ tailWord_1879406).sum := by decide
  have hdescent : baseEnd_1879406 < baseStart_1879406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879428 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1879428 : Nat := 118140960795 + 1879428 * 2 ^ 59
def prefixEnd_1879428 : Nat := 4983230072969 + 3 ^ 40 * 1879428 * 2
def baseEnd_1879428 : Nat := 428911075341501316891855

theorem tailTrace_1879428 : CollatzResearch.WordTrace tailWord_1879428 prefixEnd_1879428 428911075341501316891855 := by
  unfold tailWord_1879428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34274185317580405796463469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45698913756773874395284625 34274185317580405796463469)
  ·
    refine ⟨12852819494092652173673801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34274185317580405796463469 12852819494092652173673801)
    ·
      refine ⟨9639614620569489130255351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12852819494092652173673801 9639614620569489130255351)
      ·
        refine ⟨14459421930854233695383027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639614620569489130255351 14459421930854233695383027)
        ·
          refine ⟨21689132896281350543074541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459421930854233695383027 21689132896281350543074541)
          ·
            refine ⟨8133424836105506453652953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21689132896281350543074541 8133424836105506453652953)
            ·
              refine ⟨6100068627079129840239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133424836105506453652953 6100068627079129840239715)
              ·
                refine ⟨9150102940618694760359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100068627079129840239715 9150102940618694760359573)
                ·
                  refine ⟨428911075341501316891855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9150102940618694760359573 428911075341501316891855)
                  ·
                    rfl

theorem cell21_1879428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1879428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879428 prefixEnd_1879428 := by exact prefixLift 1879428
  have htrace : WordTrace (prefixWord ++ tailWord_1879428) baseStart_1879428 baseEnd_1879428 := by
    simpa [prefixWord, tailWord_1879428, baseEnd_1879428] using wordTrace_append hprefix tailTrace_1879428
  have hstable : (prefixWord ++ tailWord_1879428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879428).length < 2 ^ (prefixWord ++ tailWord_1879428).sum := by decide
  have hdescent : baseEnd_1879428 < baseStart_1879428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879445 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1879445 : Nat := 118140960795 + 1879445 * 2 ^ 59
def prefixEnd_1879445 : Nat := 4983230072969 + 3 ^ 40 * 1879445 * 2
def baseEnd_1879445 : Nat := 428914954973113065108487

theorem tailTrace_1879445 : CollatzResearch.WordTrace tailWord_1879445 prefixEnd_1879445 428914954973113065108487 := by
  unfold tailWord_1879445
  simp only [CollatzResearch.WordTrace]
  refine ⟨68548990676099223496295789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45699327117399482330863859 68548990676099223496295789)
  ·
    refine ⟨25705871503537208811110921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68548990676099223496295789 25705871503537208811110921)
    ·
      refine ⟨19279403627652906608333191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25705871503537208811110921 19279403627652906608333191)
      ·
        refine ⟨28919105441479359912499787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279403627652906608333191 28919105441479359912499787)
        ·
          refine ⟨43378658162219039868749681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28919105441479359912499787 43378658162219039868749681)
          ·
            refine ⟨32533993621664279901562261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43378658162219039868749681 32533993621664279901562261)
            ·
              refine ⟨1525030951015513120385731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32533993621664279901562261 1525030951015513120385731)
              ·
                refine ⟨2287546426523269680578597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525030951015513120385731 2287546426523269680578597)
                ·
                  refine ⟨428914954973113065108487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287546426523269680578597 428914954973113065108487)
                  ·
                    rfl

theorem cell21_1879445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1879445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879445 prefixEnd_1879445 := by exact prefixLift 1879445
  have htrace : WordTrace (prefixWord ++ tailWord_1879445) baseStart_1879445 baseEnd_1879445 := by
    simpa [prefixWord, tailWord_1879445, baseEnd_1879445] using wordTrace_append hprefix tailTrace_1879445
  have hstable : (prefixWord ++ tailWord_1879445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879445).length < 2 ^ (prefixWord ++ tailWord_1879445).sum := by decide
  have hdescent : baseEnd_1879445 < baseStart_1879445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879487 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_1879487 : Nat := 118140960795 + 1879487 * 2 ^ 59
def prefixEnd_1879487 : Nat := 4983230072969 + 3 ^ 40 * 1879487 * 2
def baseEnd_1879487 : Nat := 428924539945330325408401

theorem tailTrace_1879487 : CollatzResearch.WordTrace tailWord_1879487 prefixEnd_1879487 428924539945330325408401 := by
  unfold tailWord_1879487
  simp only [CollatzResearch.WordTrace]
  refine ⟨68550522541947064669324715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45700348361298043112883143 68550522541947064669324715)
  ·
    refine ⟨102825783812920597003987073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68550522541947064669324715 102825783812920597003987073)
    ·
      refine ⟨77119337859690447752990305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102825783812920597003987073 77119337859690447752990305)
      ·
        refine ⟨57839503394767835814742729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77119337859690447752990305 57839503394767835814742729)
        ·
          refine ⟨43379627546075876861057047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57839503394767835814742729 43379627546075876861057047)
          ·
            refine ⟨65069441319113815291585571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43379627546075876861057047 65069441319113815291585571)
            ·
              refine ⟨97604161978670722937378357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65069441319113815291585571 97604161978670722937378357)
              ·
                refine ⟨9150390185500380275379221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97604161978670722937378357 9150390185500380275379221)
                ·
                  refine ⟨428924539945330325408401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9150390185500380275379221 428924539945330325408401)
                  ·
                    rfl

theorem cell21_1879487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_1879487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879487 prefixEnd_1879487 := by exact prefixLift 1879487
  have htrace : WordTrace (prefixWord ++ tailWord_1879487) baseStart_1879487 baseEnd_1879487 := by
    simpa [prefixWord, tailWord_1879487, baseEnd_1879487] using wordTrace_append hprefix tailTrace_1879487
  have hstable : (prefixWord ++ tailWord_1879487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879487).length < 2 ^ (prefixWord ++ tailWord_1879487).sum := by decide
  have hdescent : baseEnd_1879487 < baseStart_1879487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879538 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1879538 : Nat := 118140960795 + 1879538 * 2 ^ 59
def prefixEnd_1879538 : Nat := 4983230072969 + 3 ^ 40 * 1879538 * 2
def baseEnd_1879538 : Nat := 428936178840165570058297

theorem tailTrace_1879538 : CollatzResearch.WordTrace tailWord_1879538 prefixEnd_1879538 428936178840165570058297 := by
  unfold tailWord_1879538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138095666190575094857817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45701588443174866919620845 17138095666190575094857817)
  ·
    refine ⟨12853571749642931321143363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17138095666190575094857817 12853571749642931321143363)
    ·
      refine ⟨19280357624464396981715045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853571749642931321143363 19280357624464396981715045)
      ·
        refine ⟨3615067054587074434071571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19280357624464396981715045 3615067054587074434071571)
        ·
          refine ⟨5422600581880611651107357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615067054587074434071571 5422600581880611651107357)
          ·
            refine ⟨2033475218205229369165259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5422600581880611651107357 2033475218205229369165259)
            ·
              refine ⟨3050212827307844053747889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033475218205229369165259 3050212827307844053747889)
              ·
                refine ⟨2287659620480883040310917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050212827307844053747889 2287659620480883040310917)
                ·
                  refine ⟨428936178840165570058297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287659620480883040310917 428936178840165570058297)
                  ·
                    rfl

theorem cell21_1879538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1879538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879538 prefixEnd_1879538 := by exact prefixLift 1879538
  have htrace : WordTrace (prefixWord ++ tailWord_1879538) baseStart_1879538 baseEnd_1879538 := by
    simpa [prefixWord, tailWord_1879538, baseEnd_1879538] using wordTrace_append hprefix tailTrace_1879538
  have hstable : (prefixWord ++ tailWord_1879538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879538).length < 2 ^ (prefixWord ++ tailWord_1879538).sum := by decide
  have hdescent : baseEnd_1879538 < baseStart_1879538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879549 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1879549 : Nat := 118140960795 + 1879549 * 2 ^ 59
def prefixEnd_1879549 : Nat := 4983230072969 + 3 ^ 40 * 1879549 * 2
def baseEnd_1879549 : Nat := 428938689190031995374941

theorem tailTrace_1879549 : CollatzResearch.WordTrace tailWord_1879549 prefixEnd_1879549 428938689190031995374941 := by
  unfold tailWord_1879549
  simp only [CollatzResearch.WordTrace]
  refine ⟨68552783867722449258081701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45701855911814966172054467 68552783867722449258081701)
  ·
    refine ⟨12853646975197959235890319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68552783867722449258081701 12853646975197959235890319)
    ·
      refine ⟨19280470462796938853835479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853646975197959235890319 19280470462796938853835479)
      ·
        refine ⟨28920705694195408280753219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19280470462796938853835479 28920705694195408280753219)
        ·
          refine ⟨43381058541293112421129829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920705694195408280753219 43381058541293112421129829)
          ·
            refine ⟨8133948476492458578961843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43381058541293112421129829 8133948476492458578961843)
            ·
              refine ⟨12200922714738687868442765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133948476492458578961843 12200922714738687868442765)
              ·
                refine ⟨4575346018027007950666037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12200922714738687868442765 4575346018027007950666037)
                ·
                  refine ⟨428938689190031995374941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4575346018027007950666037 428938689190031995374941)
                  ·
                    rfl

theorem cell21_1879549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1879549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879549 prefixEnd_1879549 := by exact prefixLift 1879549
  have htrace : WordTrace (prefixWord ++ tailWord_1879549) baseStart_1879549 baseEnd_1879549 := by
    simpa [prefixWord, tailWord_1879549, baseEnd_1879549] using wordTrace_append hprefix tailTrace_1879549
  have hstable : (prefixWord ++ tailWord_1879549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879549).length < 2 ^ (prefixWord ++ tailWord_1879549).sum := by decide
  have hdescent : baseEnd_1879549 < baseStart_1879549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879687 : List Nat := [1, 1, 4, 2, 1, 4, 3, 5]
def baseStart_1879687 : Nat := 118140960795 + 1879687 * 2 ^ 59
def prefixEnd_1879687 : Nat := 4983230072969 + 3 ^ 40 * 1879687 * 2
def baseEnd_1879687 : Nat := 142990060890058140691553

theorem tailTrace_1879687 : CollatzResearch.WordTrace tailWord_1879687 prefixEnd_1879687 142990060890058140691553 := by
  unfold tailWord_1879687
  simp only [CollatzResearch.WordTrace]
  refine ⟨68557817141222498826605315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45705211427481665884403543 68557817141222498826605315)
  ·
    refine ⟨102836725711833748239907973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68557817141222498826605315 102836725711833748239907973)
    ·
      refine ⟨19281886070968827794982745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102836725711833748239907973 19281886070968827794982745)
      ·
        refine ⟨14461414553226620846237059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19281886070968827794982745 14461414553226620846237059)
        ·
          refine ⟨21692121829839931269355589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14461414553226620846237059 21692121829839931269355589)
          ·
            refine ⟨4067272843094987113004173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21692121829839931269355589 4067272843094987113004173)
            ·
              refine ⟨1525227316160620167376565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4067272843094987113004173 1525227316160620167376565)
              ·
                refine ⟨142990060890058140691553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1525227316160620167376565 142990060890058140691553)
                ·
                  rfl

theorem cell21_1879687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].length) (baseStart_1879687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879687 prefixEnd_1879687 := by exact prefixLift 1879687
  have htrace : WordTrace (prefixWord ++ tailWord_1879687) baseStart_1879687 baseEnd_1879687 := by
    simpa [prefixWord, tailWord_1879687, baseEnd_1879687] using wordTrace_append hprefix tailTrace_1879687
  have hstable : (prefixWord ++ tailWord_1879687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879687).length < 2 ^ (prefixWord ++ tailWord_1879687).sum := by decide
  have hdescent : baseEnd_1879687 < baseStart_1879687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879715 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_1879715 : Nat := 118140960795 + 1879715 * 2 ^ 59
def prefixEnd_1879715 : Nat := 4983230072969 + 3 ^ 40 * 1879715 * 2
def baseEnd_1879715 : Nat := 428976572651652595607935

theorem tailTrace_1879715 : CollatzResearch.WordTrace tailWord_1879715 prefixEnd_1879715 428976572651652595607935 := by
  unfold tailWord_1879715
  simp only [CollatzResearch.WordTrace]
  refine ⟨68558838385121059608624599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45705892256747373072416399 68558838385121059608624599)
  ·
    refine ⟨102838257577681589412936899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68558838385121059608624599 102838257577681589412936899)
    ·
      refine ⟨154257386366522384119405349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102838257577681589412936899 154257386366522384119405349)
      ·
        refine ⟨28923259943722947022388503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154257386366522384119405349 28923259943722947022388503)
        ·
          refine ⟨43384889915584420533582755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28923259943722947022388503 43384889915584420533582755)
          ·
            refine ⟨65077334873376630800374133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43384889915584420533582755 65077334873376630800374133)
            ·
              refine ⟨6101000144379059137535075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65077334873376630800374133 6101000144379059137535075)
              ·
                refine ⟨9151500216568588706302613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101000144379059137535075 9151500216568588706302613)
                ·
                  refine ⟨428976572651652595607935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9151500216568588706302613 428976572651652595607935)
                  ·
                    rfl

theorem cell21_1879715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_1879715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879715 prefixEnd_1879715 := by exact prefixLift 1879715
  have htrace : WordTrace (prefixWord ++ tailWord_1879715) baseStart_1879715 baseEnd_1879715 := by
    simpa [prefixWord, tailWord_1879715, baseEnd_1879715] using wordTrace_append hprefix tailTrace_1879715
  have hstable : (prefixWord ++ tailWord_1879715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879715).length < 2 ^ (prefixWord ++ tailWord_1879715).sum := by decide
  have hdescent : baseEnd_1879715 < baseStart_1879715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879783 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 4]
def baseStart_1879783 : Nat := 118140960795 + 1879783 * 2 ^ 59
def prefixEnd_1879783 : Nat := 4983230072969 + 3 ^ 40 * 1879783 * 2
def baseEnd_1879783 : Nat := 428992091178099588474463

theorem tailTrace_1879783 : CollatzResearch.WordTrace tailWord_1879783 prefixEnd_1879783 428992091178099588474463 := by
  unfold tailWord_1879783
  simp only [CollatzResearch.WordTrace]
  refine ⟨68561318548874707222100003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45707545699249804814733335 68561318548874707222100003)
  ·
    refine ⟨102841977823312060833150005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68561318548874707222100003 102841977823312060833150005)
    ·
      refine ⟨9641435420935505703107813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102841977823312060833150005 9641435420935505703107813)
      ·
        refine ⟨1807769141425407319332715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9641435420935505703107813 1807769141425407319332715)
        ·
          refine ⟨2711653712138110978999073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807769141425407319332715 2711653712138110978999073)
          ·
            refine ⟨2033740284103583234249305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711653712138110978999073 2033740284103583234249305)
            ·
              refine ⟨1525305213077687425686979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033740284103583234249305 1525305213077687425686979)
              ·
                refine ⟨2287957819616531138530469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525305213077687425686979 2287957819616531138530469)
                ·
                  refine ⟨428992091178099588474463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287957819616531138530469 428992091178099588474463)
                  ·
                    rfl

theorem cell21_1879783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_1879783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879783 prefixEnd_1879783 := by exact prefixLift 1879783
  have htrace : WordTrace (prefixWord ++ tailWord_1879783) baseStart_1879783 baseEnd_1879783 := by
    simpa [prefixWord, tailWord_1879783, baseEnd_1879783] using wordTrace_append hprefix tailTrace_1879783
  have hstable : (prefixWord ++ tailWord_1879783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879783).length < 2 ^ (prefixWord ++ tailWord_1879783).sum := by decide
  have hdescent : baseEnd_1879783 < baseStart_1879783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879814 : List Nat := [6, 2, 2, 1, 1, 9]
def baseStart_1879814 : Nat := 118140960795 + 1879814 * 2 ^ 59
def prefixEnd_1879814 : Nat := 4983230072969 + 3 ^ 40 * 1879814 * 2
def baseEnd_1879814 : Nat := 15888857992609274942879

theorem tailTrace_1879814 : CollatzResearch.WordTrace tailWord_1879814 prefixEnd_1879814 15888857992609274942879 := by
  unfold tailWord_1879814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142576537867574984889953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45708299474508266344318997 2142576537867574984889953)
  ·
    refine ⟨1606932403400681238667465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2142576537867574984889953 1606932403400681238667465)
    ·
      refine ⟨1205199302550510929000599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1606932403400681238667465 1205199302550510929000599)
      ·
        refine ⟨1807798953825766393500899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205199302550510929000599 1807798953825766393500899)
        ·
          refine ⟨2711698430738649590251349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807798953825766393500899 2711698430738649590251349)
          ·
            refine ⟨15888857992609274942879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2711698430738649590251349 15888857992609274942879)
            ·
              rfl

theorem cell21_1879814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 9].length) (baseStart_1879814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879814 prefixEnd_1879814 := by exact prefixLift 1879814
  have htrace : WordTrace (prefixWord ++ tailWord_1879814) baseStart_1879814 baseEnd_1879814 := by
    simpa [prefixWord, tailWord_1879814, baseEnd_1879814] using wordTrace_append hprefix tailTrace_1879814
  have hstable : (prefixWord ++ tailWord_1879814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879814).length < 2 ^ (prefixWord ++ tailWord_1879814).sum := by decide
  have hdescent : baseEnd_1879814 < baseStart_1879814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879881 : List Nat := [1, 2, 1, 1, 2, 4, 10]
def baseStart_1879881 : Nat := 118140960795 + 1879881 * 2 ^ 59
def prefixEnd_1879881 : Nat := 4983230072969 + 3 ^ 40 * 1879881 * 2
def baseEnd_1879881 : Nat := 47668272901474799537881

theorem tailTrace_1879881 : CollatzResearch.WordTrace tailWord_1879881 prefixEnd_1879881 47668272901474799537881 := by
  unfold tailWord_1879881
  simp only [CollatzResearch.WordTrace]
  refine ⟨68564892902519669959167497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45709928601679779972778331 68564892902519669959167497)
  ·
    refine ⟨51423669676889752469375623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68564892902519669959167497 51423669676889752469375623)
    ·
      refine ⟨77135504515334628704063435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51423669676889752469375623 77135504515334628704063435)
      ·
        refine ⟨115703256773001943056095153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77135504515334628704063435 115703256773001943056095153)
        ·
          refine ⟨86777442579751457292071365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115703256773001943056095153 86777442579751457292071365)
          ·
            refine ⟨16270770483703398242263381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86777442579751457292071365 16270770483703398242263381)
            ·
              refine ⟨47668272901474799537881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16270770483703398242263381 47668272901474799537881)
              ·
                rfl

theorem cell21_1879881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 10].length) (baseStart_1879881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879881 prefixEnd_1879881 := by exact prefixLift 1879881
  have htrace : WordTrace (prefixWord ++ tailWord_1879881) baseStart_1879881 baseEnd_1879881 := by
    simpa [prefixWord, tailWord_1879881, baseEnd_1879881] using wordTrace_append hprefix tailTrace_1879881
  have hstable : (prefixWord ++ tailWord_1879881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879881).length < 2 ^ (prefixWord ++ tailWord_1879881).sum := by decide
  have hdescent : baseEnd_1879881 < baseStart_1879881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879884 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_1879884 : Nat := 118140960795 + 1879884 * 2 ^ 59
def prefixEnd_1879884 : Nat := 4983230072969 + 3 ^ 40 * 1879884 * 2
def baseEnd_1879884 : Nat := 429015140754145857290923

theorem tailTrace_1879884 : CollatzResearch.WordTrace tailWord_1879884 prefixEnd_1879884 429015140754145857290923 := by
  unfold tailWord_1879884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34282501160754400735763353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45710001547672534314351137 34282501160754400735763353)
  ·
    refine ⟨25711875870565800551822515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34282501160754400735763353 25711875870565800551822515)
    ·
      refine ⟨38567813805848700827733773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25711875870565800551822515 38567813805848700827733773)
      ·
        refine ⟨14462930177193262810400165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38567813805848700827733773 14462930177193262810400165)
        ·
          refine ⟨2711799408223736776950031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14462930177193262810400165 2711799408223736776950031)
          ·
            refine ⟨4067699112335605165425047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711799408223736776950031 4067699112335605165425047)
            ·
              refine ⟨6101548668503407748137571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067699112335605165425047 6101548668503407748137571)
              ·
                refine ⟨9152323002755111622206357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101548668503407748137571 9152323002755111622206357)
                ·
                  refine ⟨429015140754145857290923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9152323002755111622206357 429015140754145857290923)
                  ·
                    rfl

theorem cell21_1879884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_1879884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1879884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1879884 prefixEnd_1879884 := by exact prefixLift 1879884
  have htrace : WordTrace (prefixWord ++ tailWord_1879884) baseStart_1879884 baseEnd_1879884 := by
    simpa [prefixWord, tailWord_1879884, baseEnd_1879884] using wordTrace_append hprefix tailTrace_1879884
  have hstable : (prefixWord ++ tailWord_1879884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879884).length < 2 ^ (prefixWord ++ tailWord_1879884).sum := by decide
  have hdescent : baseEnd_1879884 < baseStart_1879884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880033 : List Nat := [1, 2, 3, 1, 2, 1, 2, 9]
def baseStart_1880033 : Nat := 118140960795 + 1880033 * 2 ^ 59
def prefixEnd_1880033 : Nat := 4983230072969 + 3 ^ 40 * 1880033 * 2
def baseEnd_1880033 : Nat := 143016381528051569769095

theorem tailTrace_1880033 : CollatzResearch.WordTrace tailWord_1880033 prefixEnd_1880033 143016381528051569769095 := by
  unfold tailWord_1880033
  simp only [CollatzResearch.WordTrace]
  refine ⟨68570436797968999918700753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45713624531979333279133835 68570436797968999918700753)
  ·
    refine ⟨51427827598476749939025565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68570436797968999918700753 51427827598476749939025565)
    ·
      refine ⟨19285435349428781227134587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51427827598476749939025565 19285435349428781227134587)
      ·
        refine ⟨28928153024143171840701881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19285435349428781227134587 28928153024143171840701881)
        ·
          refine ⟨21696114768107378880526411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28928153024143171840701881 21696114768107378880526411)
          ·
            refine ⟨32544172152161068320789617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21696114768107378880526411 32544172152161068320789617)
            ·
              refine ⟨24408129114120801240592213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32544172152161068320789617 24408129114120801240592213)
              ·
                refine ⟨143016381528051569769095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24408129114120801240592213 143016381528051569769095)
                ·
                  rfl

theorem cell21_1880033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_1880033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880033 prefixEnd_1880033 := by exact prefixLift 1880033
  have htrace : WordTrace (prefixWord ++ tailWord_1880033) baseStart_1880033 baseEnd_1880033 := by
    simpa [prefixWord, tailWord_1880033, baseEnd_1880033] using wordTrace_append hprefix tailTrace_1880033
  have hstable : (prefixWord ++ tailWord_1880033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880033).length < 2 ^ (prefixWord ++ tailWord_1880033).sum := by decide
  have hdescent : baseEnd_1880033 < baseStart_1880033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880039 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 3]
def baseStart_1880039 : Nat := 118140960795 + 1880039 * 2 ^ 59
def prefixEnd_1880039 : Nat := 4983230072969 + 3 ^ 40 * 1880039 * 2
def baseEnd_1880039 : Nat := 429050513865900032207273

theorem tailTrace_1880039 : CollatzResearch.WordTrace tailWord_1880039 prefixEnd_1880039 429050513865900032207273 := by
  unfold tailWord_1880039
  simp only [CollatzResearch.WordTrace]
  refine ⟨68570655635947262943419171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45713770423964841962279447 68570655635947262943419171)
  ·
    refine ⟨102855983453920894415128757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68570655635947262943419171 102855983453920894415128757)
    ·
      refine ⟨9642748448805083851418321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102855983453920894415128757 9642748448805083851418321)
      ·
        refine ⟨7232061336603812888563741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9642748448805083851418321 7232061336603812888563741)
        ·
          refine ⟨2712023001226429833211403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7232061336603812888563741 2712023001226429833211403)
          ·
            refine ⟨4068034501839644749817105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712023001226429833211403 4068034501839644749817105)
            ·
              refine ⟨3051025876379733562362829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068034501839644749817105 3051025876379733562362829)
              ·
                refine ⟨1144134703642400085886061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051025876379733562362829 1144134703642400085886061)
                ·
                  refine ⟨429050513865900032207273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144134703642400085886061 429050513865900032207273)
                  ·
                    rfl

theorem cell21_1880039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].length) (baseStart_1880039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880039 prefixEnd_1880039 := by exact prefixLift 1880039
  have htrace : WordTrace (prefixWord ++ tailWord_1880039) baseStart_1880039 baseEnd_1880039 := by
    simpa [prefixWord, tailWord_1880039, baseEnd_1880039] using wordTrace_append hprefix tailTrace_1880039
  have hstable : (prefixWord ++ tailWord_1880039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880039).length < 2 ^ (prefixWord ++ tailWord_1880039).sum := by decide
  have hdescent : baseEnd_1880039 < baseStart_1880039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880084 : List Nat := [2, 4, 3, 2, 1, 1, 1, 7]
def baseStart_1880084 : Nat := 118140960795 + 1880084 * 2 ^ 59
def prefixEnd_1880084 : Nat := 4983230072969 + 3 ^ 40 * 1880084 * 2
def baseEnd_1880084 : Nat := 143020261159663317985727

theorem tailTrace_1880084 : CollatzResearch.WordTrace tailWord_1880084 prefixEnd_1880084 143020261159663317985727 := by
  unfold tailWord_1880084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34286148460392117814403653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45714864613856157085871537 34286148460392117814403653)
  ·
    refine ⟨6428652836323522090200685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34286148460392117814403653 6428652836323522090200685)
    ·
      refine ⟨2410744813621320783825257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6428652836323522090200685 2410744813621320783825257)
      ·
        refine ⟨1808058610215990587868943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410744813621320783825257 1808058610215990587868943)
        ·
          refine ⟨2712087915323985881803415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808058610215990587868943 2712087915323985881803415)
          ·
            refine ⟨4068131872985978822705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712087915323985881803415 4068131872985978822705123)
            ·
              refine ⟨6102197809478968234057685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068131872985978822705123 6102197809478968234057685)
              ·
                refine ⟨143020261159663317985727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6102197809478968234057685 143020261159663317985727)
                ·
                  rfl

theorem cell21_1880084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_1880084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880084 prefixEnd_1880084 := by exact prefixLift 1880084
  have htrace : WordTrace (prefixWord ++ tailWord_1880084) baseStart_1880084 baseEnd_1880084 := by
    simpa [prefixWord, tailWord_1880084, baseEnd_1880084] using wordTrace_append hprefix tailTrace_1880084
  have hstable : (prefixWord ++ tailWord_1880084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880084).length < 2 ^ (prefixWord ++ tailWord_1880084).sum := by decide
  have hdescent : baseEnd_1880084 < baseStart_1880084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880129 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 4]
def baseStart_1880129 : Nat := 118140960795 + 1880129 * 2 ^ 59
def prefixEnd_1880129 : Nat := 4983230072969 + 3 ^ 40 * 1880129 * 2
def baseEnd_1880129 : Nat := 429071053092079875707089

theorem tailTrace_1880129 : CollatzResearch.WordTrace tailWord_1880129 prefixEnd_1880129 429071053092079875707089 := by
  unfold tailWord_1880129
  simp only [CollatzResearch.WordTrace]
  refine ⟨68573938205621208314195441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45715958803747472209463627 68573938205621208314195441)
  ·
    refine ⟨51430453654215906235646581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68573938205621208314195441 51430453654215906235646581)
    ·
      refine ⟨4821605030082741209591867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51430453654215906235646581 4821605030082741209591867)
      ·
        refine ⟨7232407545124111814387801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821605030082741209591867 7232407545124111814387801)
        ·
          refine ⟨5424305658843083860790851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232407545124111814387801 5424305658843083860790851)
          ·
            refine ⟨8136458488264625791186277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424305658843083860790851 8136458488264625791186277)
            ·
              refine ⟨1525585966549617335847427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8136458488264625791186277 1525585966549617335847427)
              ·
                refine ⟨2288378949824426003771141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525585966549617335847427 2288378949824426003771141)
                ·
                  refine ⟨429071053092079875707089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288378949824426003771141 429071053092079875707089)
                  ·
                    rfl

theorem cell21_1880129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_1880129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880129 prefixEnd_1880129 := by exact prefixLift 1880129
  have htrace : WordTrace (prefixWord ++ tailWord_1880129) baseStart_1880129 baseEnd_1880129 := by
    simpa [prefixWord, tailWord_1880129, baseEnd_1880129] using wordTrace_append hprefix tailTrace_1880129
  have hstable : (prefixWord ++ tailWord_1880129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880129).length < 2 ^ (prefixWord ++ tailWord_1880129).sum := by decide
  have hdescent : baseEnd_1880129 < baseStart_1880129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880140 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1880140 : Nat := 118140960795 + 1880140 * 2 ^ 59
def prefixEnd_1880140 : Nat := 4983230072969 + 3 ^ 40 * 1880140 * 2
def baseEnd_1880140 : Nat := 429073563441946301023733

theorem tailTrace_1880140 : CollatzResearch.WordTrace tailWord_1880140 prefixEnd_1880140 429073563441946301023733 := by
  unfold tailWord_1880140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287169704290678596422937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45716226272387571461897249 34287169704290678596422937)
  ·
    refine ⟨25715377278218008947317203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34287169704290678596422937 25715377278218008947317203)
    ·
      refine ⟨38573065917327013420975805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25715377278218008947317203 38573065917327013420975805)
      ·
        refine ⟨14464899718997630032865927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38573065917327013420975805 14464899718997630032865927)
        ·
          refine ⟨21697349578496445049298891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464899718997630032865927 21697349578496445049298891)
          ·
            refine ⟨32546024367744667573948337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697349578496445049298891 32546024367744667573948337)
            ·
              refine ⟨24409518275808500680461253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32546024367744667573948337 24409518275808500680461253)
              ·
                refine ⟨4576784676714093877586485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24409518275808500680461253 4576784676714093877586485)
                ·
                  refine ⟨429073563441946301023733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4576784676714093877586485 429073563441946301023733)
                  ·
                    rfl

theorem cell21_1880140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1880140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880140 prefixEnd_1880140 := by exact prefixLift 1880140
  have htrace : WordTrace (prefixWord ++ tailWord_1880140) baseStart_1880140 baseEnd_1880140 := by
    simpa [prefixWord, tailWord_1880140, baseEnd_1880140] using wordTrace_append hprefix tailTrace_1880140
  have hstable : (prefixWord ++ tailWord_1880140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880140).length < 2 ^ (prefixWord ++ tailWord_1880140).sum := by decide
  have hdescent : baseEnd_1880140 < baseStart_1880140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880174 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_1880174 : Nat := 118140960795 + 1880174 * 2 ^ 59
def prefixEnd_1880174 : Nat := 4983230072969 + 3 ^ 40 * 1880174 * 2
def baseEnd_1880174 : Nat := 429081322705169797456997

theorem tailTrace_1880174 : CollatzResearch.WordTrace tailWord_1880174 prefixEnd_1880174 429081322705169797456997 := by
  unfold tailWord_1880174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571947436307272624947947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45717052993638787333055717 8571947436307272624947947)
  ·
    refine ⟨12857921154460908937421921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8571947436307272624947947 12857921154460908937421921)
    ·
      refine ⟨9643440865845681703066441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12857921154460908937421921 9643440865845681703066441)
      ·
        refine ⟨7232580649384261277299831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9643440865845681703066441 7232580649384261277299831)
        ·
          refine ⟨10848870974076391915949747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232580649384261277299831 10848870974076391915949747)
          ·
            refine ⟨16273306461114587873924621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848870974076391915949747 16273306461114587873924621)
            ·
              refine ⟨6102489922917970452721733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16273306461114587873924621 6102489922917970452721733)
              ·
                refine ⟨1144216860547119459885325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6102489922917970452721733 1144216860547119459885325)
                ·
                  refine ⟨429081322705169797456997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144216860547119459885325 429081322705169797456997)
                  ·
                    rfl

theorem cell21_1880174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_1880174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880174 prefixEnd_1880174 := by exact prefixLift 1880174
  have htrace : WordTrace (prefixWord ++ tailWord_1880174) baseStart_1880174 baseEnd_1880174 := by
    simpa [prefixWord, tailWord_1880174, baseEnd_1880174] using wordTrace_append hprefix tailTrace_1880174
  have hstable : (prefixWord ++ tailWord_1880174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880174).length < 2 ^ (prefixWord ++ tailWord_1880174).sum := by decide
  have hdescent : baseEnd_1880174 < baseStart_1880174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880222 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1880222 : Nat := 118140960795 + 1880222 * 2 ^ 59
def prefixEnd_1880222 : Nat := 4983230072969 + 3 ^ 40 * 1880222 * 2
def baseEnd_1880222 : Nat := 429092276959132380656899

theorem tailTrace_1880222 : CollatzResearch.WordTrace tailWord_1880222 prefixEnd_1880222 429092276959132380656899 := by
  unfold tailWord_1880222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572166274285535649666365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45718220129522856798220613 8572166274285535649666365)
  ·
    refine ⟨3214562352857075868624887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8572166274285535649666365 3214562352857075868624887)
    ·
      refine ⟨4821843529285613802937331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214562352857075868624887 4821843529285613802937331)
      ·
        refine ⟨7232765293928420704405997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821843529285613802937331 7232765293928420704405997)
        ·
          refine ⟨2712286985223157764152249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7232765293928420704405997 2712286985223157764152249)
          ·
            refine ⟨2034215238917368323114187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712286985223157764152249 2034215238917368323114187)
            ·
              refine ⟨3051322858376052484671281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034215238917368323114187 3051322858376052484671281)
              ·
                refine ⟨2288492143782039363503461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051322858376052484671281 2288492143782039363503461)
                ·
                  refine ⟨429092276959132380656899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288492143782039363503461 429092276959132380656899)
                  ·
                    rfl

theorem cell21_1880222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1880222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880222 prefixEnd_1880222 := by exact prefixLift 1880222
  have htrace : WordTrace (prefixWord ++ tailWord_1880222) baseStart_1880222 baseEnd_1880222 := by
    simpa [prefixWord, tailWord_1880222, baseEnd_1880222] using wordTrace_append hprefix tailTrace_1880222
  have hstable : (prefixWord ++ tailWord_1880222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880222).length < 2 ^ (prefixWord ++ tailWord_1880222).sum := by decide
  have hdescent : baseEnd_1880222 < baseStart_1880222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880284 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_1880284 : Nat := 118140960795 + 1880284 * 2 ^ 59
def prefixEnd_1880284 : Nat := 4983230072969 + 3 ^ 40 * 1880284 * 2
def baseEnd_1880284 : Nat := 429106426203834050623439

theorem tailTrace_1880284 : CollatzResearch.WordTrace tailWord_1880284 prefixEnd_1880284 429106426203834050623439 := by
  unfold tailWord_1880284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34289795760029834893043953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45719727680039779857391937 34289795760029834893043953)
  ·
    refine ⟨25717346820022376169782965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34289795760029834893043953 25717346820022376169782965)
    ·
      refine ⟨2411001264377097765917153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25717346820022376169782965 2411001264377097765917153)
      ·
        refine ⟨1808250948282823324437865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2411001264377097765917153 1808250948282823324437865)
        ·
          refine ⟨1356188211212117493328399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808250948282823324437865 1356188211212117493328399)
          ·
            refine ⟨2034282316818176239992599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356188211212117493328399 2034282316818176239992599)
            ·
              refine ⟨3051423475227264359988899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034282316818176239992599 3051423475227264359988899)
              ·
                refine ⟨4577135212840896539983349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051423475227264359988899 4577135212840896539983349)
                ·
                  refine ⟨429106426203834050623439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577135212840896539983349 429106426203834050623439)
                  ·
                    rfl

theorem cell21_1880284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_1880284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880284 prefixEnd_1880284 := by exact prefixLift 1880284
  have htrace : WordTrace (prefixWord ++ tailWord_1880284) baseStart_1880284 baseEnd_1880284 := by
    simpa [prefixWord, tailWord_1880284, baseEnd_1880284] using wordTrace_append hprefix tailTrace_1880284
  have hstable : (prefixWord ++ tailWord_1880284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880284).length < 2 ^ (prefixWord ++ tailWord_1880284).sum := by decide
  have hdescent : baseEnd_1880284 < baseStart_1880284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880343 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 3]
def baseStart_1880343 : Nat := 118140960795 + 1880343 * 2 ^ 59
def prefixEnd_1880343 : Nat := 4983230072969 + 3 ^ 40 * 1880343 * 2
def baseEnd_1880343 : Nat := 429119890807663059139985

theorem tailTrace_1880343 : CollatzResearch.WordTrace tailWord_1880343 prefixEnd_1880343 429119890807663059139985 := by
  unfold tailWord_1880343
  simp only [CollatzResearch.WordTrace]
  refine ⟨68581743426845922862485683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45721162284563948574990455 68581743426845922862485683)
  ·
    refine ⟨102872615140268884293728525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68581743426845922862485683 102872615140268884293728525)
    ·
      refine ⟨38577230677600831610148197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102872615140268884293728525 38577230677600831610148197)
      ·
        refine ⟨7233230752050155926902787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38577230677600831610148197 7233230752050155926902787)
        ·
          refine ⟨10849846128075233890354181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233230752050155926902787 10849846128075233890354181)
          ·
            refine ⟨2034346149014106354441409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10849846128075233890354181 2034346149014106354441409)
            ·
              refine ⟨1525759611760579765831057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034346149014106354441409 1525759611760579765831057)
              ·
                refine ⟨1144319708820434824373293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525759611760579765831057 1144319708820434824373293)
                ·
                  refine ⟨429119890807663059139985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144319708820434824373293 429119890807663059139985)
                  ·
                    rfl

theorem cell21_1880343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].length) (baseStart_1880343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880343 prefixEnd_1880343 := by exact prefixLift 1880343
  have htrace : WordTrace (prefixWord ++ tailWord_1880343) baseStart_1880343 baseEnd_1880343 := by
    simpa [prefixWord, tailWord_1880343, baseEnd_1880343] using wordTrace_append hprefix tailTrace_1880343
  have hstable : (prefixWord ++ tailWord_1880343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880343).length < 2 ^ (prefixWord ++ tailWord_1880343).sum := by decide
  have hdescent : baseEnd_1880343 < baseStart_1880343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880354 : List Nat := [3, 3, 1, 1, 3, 1, 3, 6]
def baseStart_1880354 : Nat := 118140960795 + 1880354 * 2 ^ 59
def prefixEnd_1880354 : Nat := 4983230072969 + 3 ^ 40 * 1880354 * 2
def baseEnd_1880354 : Nat := 143040800385843161485543

theorem tailTrace_1880354 : CollatzResearch.WordTrace tailWord_1880354 prefixEnd_1880354 143040800385843161485543 := by
  unfold tailWord_1880354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145536157451517935284029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45721429753204047827424077 17145536157451517935284029)
  ·
    refine ⟨6429576059044319225731511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17145536157451517935284029 6429576059044319225731511)
    ·
      refine ⟨9644364088566478838597267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429576059044319225731511 9644364088566478838597267)
      ·
        refine ⟨14466546132849718257895901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644364088566478838597267 14466546132849718257895901)
        ·
          refine ⟨5424954799818644346710963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14466546132849718257895901 5424954799818644346710963)
          ·
            refine ⟨8137432199727966520066445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424954799818644346710963 8137432199727966520066445)
            ·
              refine ⟨3051537074897987445024917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8137432199727966520066445 3051537074897987445024917)
              ·
                refine ⟨143040800385843161485543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3051537074897987445024917 143040800385843161485543)
                ·
                  rfl

theorem cell21_1880354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_1880354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880354 prefixEnd_1880354 := by exact prefixLift 1880354
  have htrace : WordTrace (prefixWord ++ tailWord_1880354) baseStart_1880354 baseEnd_1880354 := by
    simpa [prefixWord, tailWord_1880354, baseEnd_1880354] using wordTrace_append hprefix tailTrace_1880354
  have hstable : (prefixWord ++ tailWord_1880354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880354).length < 2 ^ (prefixWord ++ tailWord_1880354).sum := by decide
  have hdescent : baseEnd_1880354 < baseStart_1880354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880554 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1880554 : Nat := 118140960795 + 1880554 * 2 ^ 59
def prefixEnd_1880554 : Nat := 4983230072969 + 3 ^ 40 * 1880554 * 2
def baseEnd_1880554 : Nat := 429168043882373581122887

theorem tailTrace_1880554 : CollatzResearch.WordTrace tailWord_1880554 prefixEnd_1880554 429168043882373581122887 := by
  unfold tailWord_1880554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147359807270376474604179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45726292819387670598944477 17147359807270376474604179)
  ·
    refine ⟨25721039710905564711906269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147359807270376474604179 25721039710905564711906269)
    ·
      refine ⟨9645389891589586766964851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25721039710905564711906269 9645389891589586766964851)
      ·
        refine ⟨14468084837384380150447277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9645389891589586766964851 14468084837384380150447277)
        ·
          refine ⟨5425531814019142556417729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14468084837384380150447277 5425531814019142556417729)
          ·
            refine ⟨4069148860514356917313297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425531814019142556417729 4069148860514356917313297)
            ·
              refine ⟨3051861645385767687984973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4069148860514356917313297 3051861645385767687984973)
              ·
                refine ⟨1144448117019662882994365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051861645385767687984973 1144448117019662882994365)
                ·
                  refine ⟨429168043882373581122887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144448117019662882994365 429168043882373581122887)
                  ·
                    rfl

theorem cell21_1880554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1880554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880554 prefixEnd_1880554 := by exact prefixLift 1880554
  have htrace : WordTrace (prefixWord ++ tailWord_1880554) baseStart_1880554 baseEnd_1880554 := by
    simpa [prefixWord, tailWord_1880554, baseEnd_1880554] using wordTrace_append hprefix tailTrace_1880554
  have hstable : (prefixWord ++ tailWord_1880554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880554).length < 2 ^ (prefixWord ++ tailWord_1880554).sum := by decide
  have hdescent : baseEnd_1880554 < baseStart_1880554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880613 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 3]
def baseStart_1880613 : Nat := 118140960795 + 1880613 * 2 ^ 59
def prefixEnd_1880613 : Nat := 4983230072969 + 3 ^ 40 * 1880613 * 2
def baseEnd_1880613 : Nat := 429181508486202589639433

theorem tailTrace_1880613 : CollatzResearch.WordTrace tailWord_1880613 prefixEnd_1880613 429181508486202589639433 := by
  unfold tailWord_1880613
  simp only [CollatzResearch.WordTrace]
  refine ⟨68591591135867758974814493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45727727423911839316542995 68591591135867758974814493)
  ·
    refine ⟨25721846675950409615555435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68591591135867758974814493 25721846675950409615555435)
    ·
      refine ⟨38582770013925614423333153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25721846675950409615555435 38582770013925614423333153)
      ·
        refine ⟨28937077510444210817499865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38582770013925614423333153 28937077510444210817499865)
        ·
          refine ⟨21702808132833158113124899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28937077510444210817499865 21702808132833158113124899)
          ·
            refine ⟨32554212199249737169687349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21702808132833158113124899 32554212199249737169687349)
            ·
              refine ⟨3051957393679662859658189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32554212199249737169687349 3051957393679662859658189)
              ·
                refine ⟨1144484022629873572371821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051957393679662859658189 1144484022629873572371821)
                ·
                  refine ⟨429181508486202589639433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144484022629873572371821 429181508486202589639433)
                  ·
                    rfl

theorem cell21_1880613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_1880613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880613 prefixEnd_1880613 := by exact prefixLift 1880613
  have htrace : WordTrace (prefixWord ++ tailWord_1880613) baseStart_1880613 baseEnd_1880613 := by
    simpa [prefixWord, tailWord_1880613, baseEnd_1880613] using wordTrace_append hprefix tailTrace_1880613
  have hstable : (prefixWord ++ tailWord_1880613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880613).length < 2 ^ (prefixWord ++ tailWord_1880613).sum := by decide
  have hdescent : baseEnd_1880613 < baseStart_1880613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880624 : List Nat := [2, 1, 1, 1, 2, 3, 11]
def baseStart_1880624 : Nat := 118140960795 + 1880624 * 2 ^ 59
def prefixEnd_1880624 : Nat := 4983230072969 + 3 ^ 40 * 1880624 * 2
def baseEnd_1880624 : Nat := 47687113204007668328453

theorem tailTrace_1880624 : CollatzResearch.WordTrace tailWord_1880624 prefixEnd_1880624 47687113204007668328453 := by
  unfold tailWord_1880624
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295996169413953926732463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45727994892551938568976617 34295996169413953926732463)
  ·
    refine ⟨51443994254120930890098695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34295996169413953926732463 51443994254120930890098695)
    ·
      refine ⟨77165991381181396335148043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51443994254120930890098695 77165991381181396335148043)
      ·
        refine ⟨115748987071772094502722065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77165991381181396335148043 115748987071772094502722065)
        ·
          refine ⟨86811740303829070877041549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115748987071772094502722065 86811740303829070877041549)
          ·
            refine ⟨32554402613935901578890581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86811740303829070877041549 32554402613935901578890581)
            ·
              refine ⟨47687113204007668328453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32554402613935901578890581 47687113204007668328453)
              ·
                rfl

theorem cell21_1880624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 11].length) (baseStart_1880624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880624 prefixEnd_1880624 := by exact prefixLift 1880624
  have htrace : WordTrace (prefixWord ++ tailWord_1880624) baseStart_1880624 baseEnd_1880624 := by
    simpa [prefixWord, tailWord_1880624, baseEnd_1880624] using wordTrace_append hprefix tailTrace_1880624
  have hstable : (prefixWord ++ tailWord_1880624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880624).length < 2 ^ (prefixWord ++ tailWord_1880624).sum := by decide
  have hdescent : baseEnd_1880624 < baseStart_1880624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880630 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1880630 : Nat := 118140960795 + 1880630 * 2 ^ 59
def prefixEnd_1880630 : Nat := 4983230072969 + 3 ^ 40 * 1880630 * 2
def baseEnd_1880630 : Nat := 429185388117814337856065

theorem tailTrace_1880630 : CollatzResearch.WordTrace tailWord_1880630 prefixEnd_1880630 429185388117814337856065 := by
  unfold tailWord_1880630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287013198550385679886459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45728140784537447252122229 4287013198550385679886459)
  ·
    refine ⟨6430519797825578519829689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4287013198550385679886459 6430519797825578519829689)
    ·
      refine ⟨4822889848369183889872267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430519797825578519829689 4822889848369183889872267)
      ·
        refine ⟨7234334772553775834808401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822889848369183889872267 7234334772553775834808401)
        ·
          refine ⟨5425751079415331876106301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7234334772553775834808401 5425751079415331876106301)
          ·
            refine ⟨2034656654780749453539863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5425751079415331876106301 2034656654780749453539863)
            ·
              refine ⟨3051984982171124180309795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034656654780749453539863 3051984982171124180309795)
              ·
                refine ⟨4577977473256686270464693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051984982171124180309795 4577977473256686270464693)
                ·
                  refine ⟨429185388117814337856065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577977473256686270464693 429185388117814337856065)
                  ·
                    rfl

theorem cell21_1880630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1880630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880630 prefixEnd_1880630 := by exact prefixLift 1880630
  have htrace : WordTrace (prefixWord ++ tailWord_1880630) baseStart_1880630 baseEnd_1880630 := by
    simpa [prefixWord, tailWord_1880630, baseEnd_1880630] using wordTrace_append hprefix tailTrace_1880630
  have hstable : (prefixWord ++ tailWord_1880630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880630).length < 2 ^ (prefixWord ++ tailWord_1880630).sum := by decide
  have hdescent : baseEnd_1880630 < baseStart_1880630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880641 : List Nat := [1, 2, 5, 1, 1, 2, 1, 8]
def baseStart_1880641 : Nat := 118140960795 + 1880641 * 2 ^ 59
def prefixEnd_1880641 : Nat := 4983230072969 + 3 ^ 40 * 1880641 * 2
def baseEnd_1880641 : Nat := 143062632822560254390903

theorem tailTrace_1880641 : CollatzResearch.WordTrace tailWord_1880641 prefixEnd_1880641 143062632822560254390903 := by
  unfold tailWord_1880641
  simp only [CollatzResearch.WordTrace]
  refine ⟨68592612379766319756833777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45728408253177546504555851 68592612379766319756833777)
  ·
    refine ⟨51444459284824739817625333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68592612379766319756833777 51444459284824739817625333)
    ·
      refine ⟨4822918057952319357902375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51444459284824739817625333 4822918057952319357902375)
      ·
        refine ⟨7234377086928479036853563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822918057952319357902375 7234377086928479036853563)
        ·
          refine ⟨10851565630392718555280345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234377086928479036853563 10851565630392718555280345)
          ·
            refine ⟨8138674222794538916460259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851565630392718555280345 8138674222794538916460259)
            ·
              refine ⟨12208011334191808374690389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138674222794538916460259 12208011334191808374690389)
              ·
                refine ⟨143062632822560254390903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12208011334191808374690389 143062632822560254390903)
                ·
                  rfl

theorem cell21_1880641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_1880641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880641 prefixEnd_1880641 := by exact prefixLift 1880641
  have htrace : WordTrace (prefixWord ++ tailWord_1880641) baseStart_1880641 baseEnd_1880641 := by
    simpa [prefixWord, tailWord_1880641, baseEnd_1880641] using wordTrace_append hprefix tailTrace_1880641
  have hstable : (prefixWord ++ tailWord_1880641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880641).length < 2 ^ (prefixWord ++ tailWord_1880641).sum := by decide
  have hdescent : baseEnd_1880641 < baseStart_1880641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880655 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_1880655 : Nat := 118140960795 + 1880655 * 2 ^ 59
def prefixEnd_1880655 : Nat := 4983230072969 + 3 ^ 40 * 1880655 * 2
def baseEnd_1880655 : Nat := 429191093458419849939347

theorem tailTrace_1880655 : CollatzResearch.WordTrace tailWord_1880655 prefixEnd_1880655 429191093458419849939347 := by
  unfold tailWord_1880655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68593123001715600147843419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45728748667810400098562279 68593123001715600147843419)
  ·
    refine ⟨102889684502573400221765129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68593123001715600147843419 102889684502573400221765129)
    ·
      refine ⟨77167263376930050166323847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102889684502573400221765129 77167263376930050166323847)
      ·
        refine ⟨115750895065395075249485771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77167263376930050166323847 115750895065395075249485771)
        ·
          refine ⟨173626342598092612874228657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115750895065395075249485771 173626342598092612874228657)
          ·
            refine ⟨130219756948569459655671493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173626342598092612874228657 130219756948569459655671493)
            ·
              refine ⟨24416204427856773685438405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130219756948569459655671493 24416204427856773685438405)
              ·
                refine ⟨4578038330223145066019701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24416204427856773685438405 4578038330223145066019701)
                ·
                  refine ⟨429191093458419849939347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4578038330223145066019701 429191093458419849939347)
                  ·
                    rfl

theorem cell21_1880655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_1880655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880655 prefixEnd_1880655 := by exact prefixLift 1880655
  have htrace : WordTrace (prefixWord ++ tailWord_1880655) baseStart_1880655 baseEnd_1880655 := by
    simpa [prefixWord, tailWord_1880655, baseEnd_1880655] using wordTrace_append hprefix tailTrace_1880655
  have hstable : (prefixWord ++ tailWord_1880655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880655).length < 2 ^ (prefixWord ++ tailWord_1880655).sum := by decide
  have hdescent : baseEnd_1880655 < baseStart_1880655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880737 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 4]
def baseStart_1880737 : Nat := 118140960795 + 1880737 * 2 ^ 59
def prefixEnd_1880737 : Nat := 4983230072969 + 3 ^ 40 * 1880737 * 2
def baseEnd_1880737 : Nat := 429209806975605929572513

theorem tailTrace_1880737 : CollatzResearch.WordTrace tailWord_1880737 prefixEnd_1880737 429209806975605929572513 := by
  unfold tailWord_1880737
  simp only [CollatzResearch.WordTrace]
  refine ⟨68596113787418528152328465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45730742524945685434885643 68596113787418528152328465)
  ·
    refine ⟨51447085340563896114246349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68596113787418528152328465 51447085340563896114246349)
    ·
      refine ⟨19292657002711461042842381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51447085340563896114246349 19292657002711461042842381)
      ·
        refine ⟨7234746376016797891065893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19292657002711461042842381 7234746376016797891065893)
        ·
          refine ⟨1356514945503149604574855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7234746376016797891065893 1356514945503149604574855)
          ·
            refine ⟨2034772418254724406862283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356514945503149604574855 2034772418254724406862283)
            ·
              refine ⟨3052158627382086610293425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034772418254724406862283 3052158627382086610293425)
              ·
                refine ⟨2289118970536564957720069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052158627382086610293425 2289118970536564957720069)
                ·
                  refine ⟨429209806975605929572513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289118970536564957720069 429209806975605929572513)
                  ·
                    rfl

theorem cell21_1880737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_1880737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880737 prefixEnd_1880737 := by exact prefixLift 1880737
  have htrace : WordTrace (prefixWord ++ tailWord_1880737) baseStart_1880737 baseEnd_1880737 := by
    simpa [prefixWord, tailWord_1880737, baseEnd_1880737] using wordTrace_append hprefix tailTrace_1880737
  have hstable : (prefixWord ++ tailWord_1880737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880737).length < 2 ^ (prefixWord ++ tailWord_1880737).sum := by decide
  have hdescent : baseEnd_1880737 < baseStart_1880737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880782 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1880782 : Nat := 118140960795 + 1880782 * 2 ^ 59
def prefixEnd_1880782 : Nat := 4983230072969 + 3 ^ 40 * 1880782 * 2
def baseEnd_1880782 : Nat := 429220076588695851322421

theorem tailTrace_1880782 : CollatzResearch.WordTrace tailWord_1880782 prefixEnd_1880782 429220076588695851322421 := by
  unfold tailWord_1880782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574719384031937604714575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45731836714837000558477733 8574719384031937604714575)
  ·
    refine ⟨12862079076047906407071863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8574719384031937604714575 12862079076047906407071863)
    ·
      refine ⟨19293118614071859610607795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12862079076047906407071863 19293118614071859610607795)
      ·
        refine ⟨28939677921107789415911693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19293118614071859610607795 28939677921107789415911693)
        ·
          refine ⟨10852379220415421030966885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28939677921107789415911693 10852379220415421030966885)
          ·
            refine ⟨2034821103827891443306291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10852379220415421030966885 2034821103827891443306291)
            ·
              refine ⟨3052231655741837164959437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034821103827891443306291 3052231655741837164959437)
              ·
                refine ⟨1144586870903188936859789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3052231655741837164959437 1144586870903188936859789)
                ·
                  refine ⟨429220076588695851322421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144586870903188936859789 429220076588695851322421)
                  ·
                    rfl

theorem cell21_1880782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1880782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880782 prefixEnd_1880782 := by exact prefixLift 1880782
  have htrace : WordTrace (prefixWord ++ tailWord_1880782) baseStart_1880782 baseEnd_1880782 := by
    simpa [prefixWord, tailWord_1880782, baseEnd_1880782] using wordTrace_append hprefix tailTrace_1880782
  have hstable : (prefixWord ++ tailWord_1880782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880782).length < 2 ^ (prefixWord ++ tailWord_1880782).sum := by decide
  have hdescent : baseEnd_1880782 < baseStart_1880782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880883 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_1880883 : Nat := 118140960795 + 1880883 * 2 ^ 59
def prefixEnd_1880883 : Nat := 4983230072969 + 3 ^ 40 * 1880883 * 2
def baseEnd_1880883 : Nat := 429243126164742120138881

theorem tailTrace_1880883 : CollatzResearch.WordTrace tailWord_1880883 prefixEnd_1880883 429243126164742120138881 := by
  unfold tailWord_1880883
  simp only [CollatzResearch.WordTrace]
  refine ⟨68601438844889595087143303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45734292563259730058095535 68601438844889595087143303)
  ·
    refine ⟨102902158267334392630714955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68601438844889595087143303 102902158267334392630714955)
    ·
      refine ⟨154353237401001588946072433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102902158267334392630714955 154353237401001588946072433)
      ·
        refine ⟨115764928050751191709554325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154353237401001588946072433 115764928050751191709554325)
        ·
          refine ⟨5426481002378962111385359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115764928050751191709554325 5426481002378962111385359)
          ·
            refine ⟨8139721503568443167078039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426481002378962111385359 8139721503568443167078039)
            ·
              refine ⟨12209582255352664750617059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139721503568443167078039 12209582255352664750617059)
              ·
                refine ⟨18314373383028997125925589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209582255352664750617059 18314373383028997125925589)
                ·
                  refine ⟨429243126164742120138881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18314373383028997125925589 429243126164742120138881)
                  ·
                    rfl

theorem cell21_1880883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_1880883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880883 prefixEnd_1880883 := by exact prefixLift 1880883
  have htrace : WordTrace (prefixWord ++ tailWord_1880883) baseStart_1880883 baseEnd_1880883 := by
    simpa [prefixWord, tailWord_1880883, baseEnd_1880883] using wordTrace_append hprefix tailTrace_1880883
  have hstable : (prefixWord ++ tailWord_1880883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880883).length < 2 ^ (prefixWord ++ tailWord_1880883).sum := by decide
  have hdescent : baseEnd_1880883 < baseStart_1880883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880914 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1880914 : Nat := 118140960795 + 1880914 * 2 ^ 59
def prefixEnd_1880914 : Nat := 4983230072969 + 3 ^ 40 * 1880914 * 2
def baseEnd_1880914 : Nat := 429250200787092955122151

theorem tailTrace_1880914 : CollatzResearch.WordTrace tailWord_1880914 prefixEnd_1880914 429250200787092955122151 := by
  unfold tailWord_1880914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150642376944321845380449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45735046338518191587681197 17150642376944321845380449)
  ·
    refine ⟨12862981782708241384035337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17150642376944321845380449 12862981782708241384035337)
    ·
      refine ⟨9647236337031181038026503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12862981782708241384035337 9647236337031181038026503)
      ·
        refine ⟨14470854505546771557039755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647236337031181038026503 14470854505546771557039755)
        ·
          refine ⟨21706281758320157335559633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14470854505546771557039755 21706281758320157335559633)
          ·
            refine ⟨16279711318740118001669725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21706281758320157335559633 16279711318740118001669725)
            ·
              refine ⟨6104891744527544250626147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16279711318740118001669725 6104891744527544250626147)
              ·
                refine ⟨9157337616791316375939221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104891744527544250626147 9157337616791316375939221)
                ·
                  refine ⟨429250200787092955122151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157337616791316375939221 429250200787092955122151)
                  ·
                    rfl

theorem cell21_1880914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1880914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880914 prefixEnd_1880914 := by exact prefixLift 1880914
  have htrace : WordTrace (prefixWord ++ tailWord_1880914) baseStart_1880914 baseEnd_1880914 := by
    simpa [prefixWord, tailWord_1880914, baseEnd_1880914] using wordTrace_append hprefix tailTrace_1880914
  have hstable : (prefixWord ++ tailWord_1880914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880914).length < 2 ^ (prefixWord ++ tailWord_1880914).sum := by decide
  have hdescent : baseEnd_1880914 < baseStart_1880914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880928 : List Nat := [2, 1, 1, 3, 3, 1, 2, 8]
def baseStart_1880928 : Nat := 118140960795 + 1880928 * 2 ^ 59
def prefixEnd_1880928 : Nat := 4983230072969 + 3 ^ 40 * 1880928 * 2
def baseEnd_1880928 : Nat := 143084465259277347296263

theorem tailTrace_1880928 : CollatzResearch.WordTrace tailWord_1880928 prefixEnd_1880928 143084465259277347296263 := by
  unfold tailWord_1880928
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301540064863283886265719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45735386753151045181687625 34301540064863283886265719)
  ·
    refine ⟨51452310097294925829398579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34301540064863283886265719 51452310097294925829398579)
    ·
      refine ⟨77178465145942388744097869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51452310097294925829398579 77178465145942388744097869)
      ·
        refine ⟨28941924429728395779036701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77178465145942388744097869 28941924429728395779036701)
        ·
          refine ⟨10853221661148148417138763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28941924429728395779036701 10853221661148148417138763)
          ·
            refine ⟨16279832491722222625708145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853221661148148417138763 16279832491722222625708145)
            ·
              refine ⟨12209874368791666969281109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16279832491722222625708145 12209874368791666969281109)
              ·
                refine ⟨143084465259277347296263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12209874368791666969281109 143084465259277347296263)
                ·
                  rfl

theorem cell21_1880928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_1880928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880928 prefixEnd_1880928 := by exact prefixLift 1880928
  have htrace : WordTrace (prefixWord ++ tailWord_1880928) baseStart_1880928 baseEnd_1880928 := by
    simpa [prefixWord, tailWord_1880928, baseEnd_1880928] using wordTrace_append hprefix tailTrace_1880928
  have hstable : (prefixWord ++ tailWord_1880928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880928).length < 2 ^ (prefixWord ++ tailWord_1880928).sum := by decide
  have hdescent : baseEnd_1880928 < baseStart_1880928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880945 : List Nat := [1, 2, 2, 2, 1, 4, 4, 5]
def baseStart_1880945 : Nat := 118140960795 + 1880945 * 2 ^ 59
def prefixEnd_1880945 : Nat := 4983230072969 + 3 ^ 40 * 1880945 * 2
def baseEnd_1880945 : Nat := 143085758469814596701807

theorem tailTrace_1880945 : CollatzResearch.WordTrace tailWord_1880945 prefixEnd_1880945 143085758469814596701807 := by
  unfold tailWord_1880945
  simp only [CollatzResearch.WordTrace]
  refine ⟨68603700170664979675900289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735800113776653117266859 68603700170664979675900289)
  ·
    refine ⟨51452775127998734756925217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68603700170664979675900289 51452775127998734756925217)
    ·
      refine ⟨38589581345999051067693913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51452775127998734756925217 38589581345999051067693913)
      ·
        refine ⟨28942186009499288300770435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38589581345999051067693913 28942186009499288300770435)
        ·
          refine ⟨43413279014248932451155653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28942186009499288300770435 43413279014248932451155653)
          ·
            refine ⟨8139989815171674834591685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43413279014248932451155653 8139989815171674834591685)
            ·
              refine ⟨1526248090344689031485941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8139989815171674834591685 1526248090344689031485941)
              ·
                refine ⟨143085758469814596701807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1526248090344689031485941 143085758469814596701807)
                ·
                  rfl

theorem cell21_1880945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].length) (baseStart_1880945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880945 prefixEnd_1880945 := by exact prefixLift 1880945
  have htrace : WordTrace (prefixWord ++ tailWord_1880945) baseStart_1880945 baseEnd_1880945 := by
    simpa [prefixWord, tailWord_1880945, baseEnd_1880945] using wordTrace_append hprefix tailTrace_1880945
  have hstable : (prefixWord ++ tailWord_1880945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880945).length < 2 ^ (prefixWord ++ tailWord_1880945).sum := by decide
  have hdescent : baseEnd_1880945 < baseStart_1880945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880982 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1880982 : Nat := 118140960795 + 1880982 * 2 ^ 59
def prefixEnd_1880982 : Nat := 4983230072969 + 3 ^ 40 * 1880982 * 2
def baseEnd_1880982 : Nat := 429265719313539947988679

theorem tailTrace_1880982 : CollatzResearch.WordTrace tailWord_1880982 prefixEnd_1880982 429265719313539947988679 := by
  unfold tailWord_1880982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287815604470683437187325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45736699781020623329998133 4287815604470683437187325)
  ·
    refine ⟨1607930851676506288945247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4287815604470683437187325 1607930851676506288945247)
    ·
      refine ⟨2411896277514759433417871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607930851676506288945247 2411896277514759433417871)
      ·
        refine ⟨3617844416272139150126807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411896277514759433417871 3617844416272139150126807)
        ·
          refine ⟨5426766624408208725190211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617844416272139150126807 5426766624408208725190211)
          ·
            refine ⟨8140149936612313087785317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426766624408208725190211 8140149936612313087785317)
            ·
              refine ⟨1526278113114808703959747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8140149936612313087785317 1526278113114808703959747)
              ·
                refine ⟨2289417169672213055939621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526278113114808703959747 2289417169672213055939621)
                ·
                  refine ⟨429265719313539947988679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289417169672213055939621 429265719313539947988679)
                  ·
                    rfl

theorem cell21_1880982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1880982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1880982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1880982 prefixEnd_1880982 := by exact prefixLift 1880982
  have htrace : WordTrace (prefixWord ++ tailWord_1880982) baseStart_1880982 baseEnd_1880982 := by
    simpa [prefixWord, tailWord_1880982, baseEnd_1880982] using wordTrace_append hprefix tailTrace_1880982
  have hstable : (prefixWord ++ tailWord_1880982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880982).length < 2 ^ (prefixWord ++ tailWord_1880982).sum := by decide
  have hdescent : baseEnd_1880982 < baseStart_1880982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881021 : List Nat := [1, 4, 1, 2, 5, 8]
def baseStart_1881021 : Nat := 118140960795 + 1881021 * 2 ^ 59
def prefixEnd_1881021 : Nat := 4983230072969 + 3 ^ 40 * 1881021 * 2
def baseEnd_1881021 : Nat := 15899059986847575808837

theorem tailTrace_1881021 : CollatzResearch.WordTrace tailWord_1881021 prefixEnd_1881021 15899059986847575808837 := by
  unfold tailWord_1881021
  simp only [CollatzResearch.WordTrace]
  refine ⟨68606472118389644655666917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45737648078926429770444611 68606472118389644655666917)
  ·
    refine ⟨12863713522198058372937547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68606472118389644655666917 12863713522198058372937547)
    ·
      refine ⟨19295570283297087559406321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12863713522198058372937547 19295570283297087559406321)
      ·
        refine ⟨14471677712472815669554741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19295570283297087559406321 14471677712472815669554741)
        ·
          refine ⟨1356719785544326469020757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14471677712472815669554741 1356719785544326469020757)
          ·
            refine ⟨15899059986847575808837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1356719785544326469020757 15899059986847575808837)
            ·
              rfl

theorem cell21_1881021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 8].length) (baseStart_1881021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881021 prefixEnd_1881021 := by exact prefixLift 1881021
  have htrace : WordTrace (prefixWord ++ tailWord_1881021) baseStart_1881021 baseEnd_1881021 := by
    simpa [prefixWord, tailWord_1881021, baseEnd_1881021] using wordTrace_append hprefix tailTrace_1881021
  have hstable : (prefixWord ++ tailWord_1881021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881021).length < 2 ^ (prefixWord ++ tailWord_1881021).sum := by decide
  have hdescent : baseEnd_1881021 < baseStart_1881021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881030 : List Nat := [6, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1881030 : Nat := 118140960795 + 1881030 * 2 ^ 59
def prefixEnd_1881030 : Nat := 4983230072969 + 3 ^ 40 * 1881030 * 2
def baseEnd_1881030 : Nat := 143092224522500843729527

theorem tailTrace_1881030 : CollatzResearch.WordTrace tailWord_1881030 prefixEnd_1881030 143092224522500843729527 := by
  unfold tailWord_1881030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143962511729907474773267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45737866916904692795163029 2143962511729907474773267)
  ·
    refine ⟨3215943767594861212159901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2143962511729907474773267 3215943767594861212159901)
    ·
      refine ⟨1205978912848072954559963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3215943767594861212159901 1205978912848072954559963)
      ·
        refine ⟨1808968369272109431839945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205978912848072954559963 1808968369272109431839945)
        ·
          refine ⟨1356726276954082073879959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808968369272109431839945 1356726276954082073879959)
          ·
            refine ⟨2035089415431123110819939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356726276954082073879959 2035089415431123110819939)
            ·
              refine ⟨3052634123146684666229909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035089415431123110819939 3052634123146684666229909)
              ·
                refine ⟨143092224522500843729527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3052634123146684666229909 143092224522500843729527)
                ·
                  rfl

theorem cell21_1881030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1881030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881030 prefixEnd_1881030 := by exact prefixLift 1881030
  have htrace : WordTrace (prefixWord ++ tailWord_1881030) baseStart_1881030 baseEnd_1881030 := by
    simpa [prefixWord, tailWord_1881030, baseEnd_1881030] using wordTrace_append hprefix tailTrace_1881030
  have hstable : (prefixWord ++ tailWord_1881030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881030).length < 2 ^ (prefixWord ++ tailWord_1881030).sum := by decide
  have hdescent : baseEnd_1881030 < baseStart_1881030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881125 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1881125 : Nat := 118140960795 + 1881125 * 2 ^ 59
def prefixEnd_1881125 : Nat := 4983230072969 + 3 ^ 40 * 1881125 * 2
def baseEnd_1881125 : Nat := 429298353861803477105053

theorem tailTrace_1881125 : CollatzResearch.WordTrace tailWord_1881125 prefixEnd_1881125 429298353861803477105053 := by
  unfold tailWord_1881125
  simp only [CollatzResearch.WordTrace]
  refine ⟨68610265310012870417452829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45740176873341913611635219 68610265310012870417452829)
  ·
    refine ⟨25728849491254826406544811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68610265310012870417452829 25728849491254826406544811)
    ·
      refine ⟨38593274236882239609817217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25728849491254826406544811 38593274236882239609817217)
      ·
        refine ⟨28944955677661679707362913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38593274236882239609817217 28944955677661679707362913)
        ·
          refine ⟨21708716758246259780522185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28944955677661679707362913 21708716758246259780522185)
          ·
            refine ⟨16281537568684694835391639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21708716758246259780522185 16281537568684694835391639)
            ·
              refine ⟨24422306353027042253087459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281537568684694835391639 24422306353027042253087459)
              ·
                refine ⟨36633459529540563379631189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24422306353027042253087459 36633459529540563379631189)
                ·
                  refine ⟨429298353861803477105053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36633459529540563379631189 429298353861803477105053)
                  ·
                    rfl

theorem cell21_1881125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1881125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881125 prefixEnd_1881125 := by exact prefixLift 1881125
  have htrace : WordTrace (prefixWord ++ tailWord_1881125) baseStart_1881125 baseEnd_1881125 := by
    simpa [prefixWord, tailWord_1881125, baseEnd_1881125] using wordTrace_append hprefix tailTrace_1881125
  have hstable : (prefixWord ++ tailWord_1881125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881125).length < 2 ^ (prefixWord ++ tailWord_1881125).sum := by decide
  have hdescent : baseEnd_1881125 < baseStart_1881125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881159 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 4]
def baseStart_1881159 : Nat := 118140960795 + 1881159 * 2 ^ 59
def prefixEnd_1881159 : Nat := 4983230072969 + 3 ^ 40 * 1881159 * 2
def baseEnd_1881159 : Nat := 429306113125026973538317

theorem tailTrace_1881159 : CollatzResearch.WordTrace tailWord_1881159 prefixEnd_1881159 429306113125026973538317 := by
  unfold tailWord_1881159
  simp only [CollatzResearch.WordTrace]
  refine ⟨68611505391889694224190531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45741003594593129482793687 68611505391889694224190531)
  ·
    refine ⟨102917258087834541336285797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68611505391889694224190531 102917258087834541336285797)
    ·
      refine ⟨19296985891468976500553587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102917258087834541336285797 19296985891468976500553587)
      ·
        refine ⟨28945478837203464750830381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19296985891468976500553587 28945478837203464750830381)
        ·
          refine ⟨10854554563951299281561393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28945478837203464750830381 10854554563951299281561393)
          ·
            refine ⟨8140915922963474461171045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10854554563951299281561393 8140915922963474461171045)
            ·
              refine ⟨1526421735555651461469571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8140915922963474461171045 1526421735555651461469571)
              ·
                refine ⟨2289632603333477192204357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526421735555651461469571 2289632603333477192204357)
                ·
                  refine ⟨429306113125026973538317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289632603333477192204357 429306113125026973538317)
                  ·
                    rfl

theorem cell21_1881159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_1881159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881159 prefixEnd_1881159 := by exact prefixLift 1881159
  have htrace : WordTrace (prefixWord ++ tailWord_1881159) baseStart_1881159 baseEnd_1881159 := by
    simpa [prefixWord, tailWord_1881159, baseEnd_1881159] using wordTrace_append hprefix tailTrace_1881159
  have hstable : (prefixWord ++ tailWord_1881159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881159).length < 2 ^ (prefixWord ++ tailWord_1881159).sum := by decide
  have hdescent : baseEnd_1881159 < baseStart_1881159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881325 : List Nat := [1, 5, 1, 2, 2, 2, 2, 6]
def baseStart_1881325 : Nat := 118140960795 + 1881325 * 2 ^ 59
def prefixEnd_1881325 : Nat := 4983230072969 + 3 ^ 40 * 1881325 * 2
def baseEnd_1881325 : Nat := 143114665528882524590437

theorem tailTrace_1881325 : CollatzResearch.WordTrace tailWord_1881325 prefixEnd_1881325 143114665528882524590437 := by
  unfold tailWord_1881325
  simp only [CollatzResearch.WordTrace]
  refine ⟨68617559909288304574733429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45745039939525536383155619 68617559909288304574733429)
  ·
    refine ⟨6432896241495778553881259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68617559909288304574733429 6432896241495778553881259)
    ·
      refine ⟨9649344362243667830821889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432896241495778553881259 9649344362243667830821889)
      ·
        refine ⟨7237008271682750873116417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9649344362243667830821889 7237008271682750873116417)
        ·
          refine ⟨5427756203762063154837313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7237008271682750873116417 5427756203762063154837313)
          ·
            refine ⟨4070817152821547366127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5427756203762063154837313 4070817152821547366127985)
            ·
              refine ⟨3053112864616160524595989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070817152821547366127985 3053112864616160524595989)
              ·
                refine ⟨143114665528882524590437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3053112864616160524595989 143114665528882524590437)
                ·
                  rfl

theorem cell21_1881325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_1881325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881325 prefixEnd_1881325 := by exact prefixLift 1881325
  have htrace : WordTrace (prefixWord ++ tailWord_1881325) baseStart_1881325 baseEnd_1881325 := by
    simpa [prefixWord, tailWord_1881325, baseEnd_1881325] using wordTrace_append hprefix tailTrace_1881325
  have hstable : (prefixWord ++ tailWord_1881325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881325).length < 2 ^ (prefixWord ++ tailWord_1881325).sum := by decide
  have hdescent : baseEnd_1881325 < baseStart_1881325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881370 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1881370 : Nat := 118140960795 + 1881370 * 2 ^ 59
def prefixEnd_1881370 : Nat := 4983230072969 + 3 ^ 40 * 1881370 * 2
def baseEnd_1881370 : Nat := 429354266199737495521219

theorem tailTrace_1881370 : CollatzResearch.WordTrace tailWord_1881370 prefixEnd_1881370 429354266199737495521219 := by
  unfold tailWord_1881370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17154800298531319315030391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45746134129416851506747709 17154800298531319315030391)
  ·
    refine ⟨25732200447796978972545587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17154800298531319315030391 25732200447796978972545587)
    ·
      refine ⟨38598300671695468458818381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25732200447796978972545587 38598300671695468458818381)
      ·
        refine ⟨14474362751885800672056893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38598300671695468458818381 14474362751885800672056893)
        ·
          refine ⟨5427886031957175252021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14474362751885800672056893 5427886031957175252021335)
          ·
            refine ⟨8141829047935762878032003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427886031957175252021335 8141829047935762878032003)
            ·
              refine ⟨12212743571903644317048005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141829047935762878032003 12212743571903644317048005)
              ·
                refine ⟨2289889419731933309446501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12212743571903644317048005 2289889419731933309446501)
                ·
                  refine ⟨429354266199737495521219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289889419731933309446501 429354266199737495521219)
                  ·
                    rfl

theorem cell21_1881370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1881370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881370 prefixEnd_1881370 := by exact prefixLift 1881370
  have htrace : WordTrace (prefixWord ++ tailWord_1881370) baseStart_1881370 baseEnd_1881370 := by
    simpa [prefixWord, tailWord_1881370, baseEnd_1881370] using wordTrace_append hprefix tailTrace_1881370
  have hstable : (prefixWord ++ tailWord_1881370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881370).length < 2 ^ (prefixWord ++ tailWord_1881370).sum := by decide
  have hdescent : baseEnd_1881370 < baseStart_1881370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881373 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 3]
def baseStart_1881373 : Nat := 118140960795 + 1881373 * 2 ^ 59
def prefixEnd_1881373 : Nat := 4983230072969 + 3 ^ 40 * 1881373 * 2
def baseEnd_1881373 : Nat := 429354950840610156971213

theorem tailTrace_1881373 : CollatzResearch.WordTrace tailWord_1881373 prefixEnd_1881373 429354950840610156971213 := by
  unfold tailWord_1881373
  simp only [CollatzResearch.WordTrace]
  refine ⟨68619310613114408772480773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45746207075409605848320515 68619310613114408772480773)
  ·
    refine ⟨12866120739958951644840145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68619310613114408772480773 12866120739958951644840145)
    ·
      refine ⟨9649590554969213733630109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12866120739958951644840145 9649590554969213733630109)
      ·
        refine ⟨3618596458113455150111291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9649590554969213733630109 3618596458113455150111291)
        ·
          refine ⟨5427894687170182725166937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618596458113455150111291 5427894687170182725166937)
          ·
            refine ⟨4070921015377637043875203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5427894687170182725166937 4070921015377637043875203)
            ·
              refine ⟨6106381523066455565812805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070921015377637043875203 6106381523066455565812805)
              ·
                refine ⟨1144946535574960418589901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6106381523066455565812805 1144946535574960418589901)
                ·
                  refine ⟨429354950840610156971213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144946535574960418589901 429354950840610156971213)
                  ·
                    rfl

theorem cell21_1881373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_1881373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881373 prefixEnd_1881373 := by exact prefixLift 1881373
  have htrace : WordTrace (prefixWord ++ tailWord_1881373) baseStart_1881373 baseEnd_1881373 := by
    simpa [prefixWord, tailWord_1881373, baseEnd_1881373] using wordTrace_append hprefix tailTrace_1881373
  have hstable : (prefixWord ++ tailWord_1881373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881373).length < 2 ^ (prefixWord ++ tailWord_1881373).sum := by decide
  have hdescent : baseEnd_1881373 < baseStart_1881373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881421 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1881421 : Nat := 118140960795 + 1881421 * 2 ^ 59
def prefixEnd_1881421 : Nat := 4983230072969 + 3 ^ 40 * 1881421 * 2
def baseEnd_1881421 : Nat := 429365905094572740171115

theorem tailTrace_1881421 : CollatzResearch.WordTrace tailWord_1881421 prefixEnd_1881421 429365905094572740171115 := by
  unfold tailWord_1881421
  simp only [CollatzResearch.WordTrace]
  refine ⟨68621061316940512970228117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45747374211293675313485411 68621061316940512970228117)
  ·
    refine ⟨3216612249231586545479443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68621061316940512970228117 3216612249231586545479443)
    ·
      refine ⟨4824918373847379818219165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3216612249231586545479443 4824918373847379818219165)
      ·
        refine ⟨1809344390192767431832187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4824918373847379818219165 1809344390192767431832187)
        ·
          refine ⟨2714016585289151147748281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809344390192767431832187 2714016585289151147748281)
          ·
            refine ⟨2035512438966863360811211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714016585289151147748281 2035512438966863360811211)
            ·
              refine ⟨3053268658450295041216817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035512438966863360811211 3053268658450295041216817)
              ·
                refine ⟨2289951493837721280912613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053268658450295041216817 2289951493837721280912613)
                ·
                  refine ⟨429365905094572740171115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289951493837721280912613 429365905094572740171115)
                  ·
                    rfl

theorem cell21_1881421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1881421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881421 prefixEnd_1881421 := by exact prefixLift 1881421
  have htrace : WordTrace (prefixWord ++ tailWord_1881421) baseStart_1881421 baseEnd_1881421 := by
    simpa [prefixWord, tailWord_1881421, baseEnd_1881421] using wordTrace_append hprefix tailTrace_1881421
  have hstable : (prefixWord ++ tailWord_1881421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881421).length < 2 ^ (prefixWord ++ tailWord_1881421).sum := by decide
  have hdescent : baseEnd_1881421 < baseStart_1881421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881584 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_1881584 : Nat := 118140960795 + 1881584 * 2 ^ 59
def prefixEnd_1881584 : Nat := 4983230072969 + 3 ^ 40 * 1881584 * 2
def baseEnd_1881584 : Nat := 429403103915320678954115

theorem tailTrace_1881584 : CollatzResearch.WordTrace tailWord_1881584 prefixEnd_1881584 429403103915320678954115 := by
  unfold tailWord_1881584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34313503207674995904205903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45751337610233327872274537 34313503207674995904205903)
  ·
    refine ⟨51470254811512493856308855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34313503207674995904205903 51470254811512493856308855)
    ·
      refine ⟨77205382217268740784463283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51470254811512493856308855 77205382217268740784463283)
      ·
        refine ⟨115808073325903111176694925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77205382217268740784463283 115808073325903111176694925)
        ·
          refine ⟨43428027497213666691260597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115808073325903111176694925 43428027497213666691260597)
          ·
            refine ⟨4071377577863781252305681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43428027497213666691260597 4071377577863781252305681)
            ·
              refine ⟨3053533183397835939229261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071377577863781252305681 3053533183397835939229261)
              ·
                refine ⟨1145074943774188477210973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3053533183397835939229261 1145074943774188477210973)
                ·
                  refine ⟨429403103915320678954115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145074943774188477210973 429403103915320678954115)
                  ·
                    rfl

theorem cell21_1881584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_1881584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881584 prefixEnd_1881584 := by exact prefixLift 1881584
  have htrace : WordTrace (prefixWord ++ tailWord_1881584) baseStart_1881584 baseEnd_1881584 := by
    simpa [prefixWord, tailWord_1881584, baseEnd_1881584] using wordTrace_append hprefix tailTrace_1881584
  have hstable : (prefixWord ++ tailWord_1881584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881584).length < 2 ^ (prefixWord ++ tailWord_1881584).sum := by decide
  have hdescent : baseEnd_1881584 < baseStart_1881584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881657 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_1881657 : Nat := 118140960795 + 1881657 * 2 ^ 59
def prefixEnd_1881657 : Nat := 4983230072969 + 3 ^ 40 * 1881657 * 2
def baseEnd_1881657 : Nat := 429419763509888774237299

theorem tailTrace_1881657 : CollatzResearch.WordTrace tailWord_1881657 prefixEnd_1881657 429419763509888774237299 := by
  unfold tailWord_1881657
  simp only [CollatzResearch.WordTrace]
  refine ⟨68629668944085525275819225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45753112629390350183879483 68629668944085525275819225)
  ·
    refine ⟨51472251708064143956864419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68629668944085525275819225 51472251708064143956864419)
    ·
      refine ⟨77208377562096215935296629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51472251708064143956864419 77208377562096215935296629)
      ·
        refine ⟨7238285396446520243934059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77208377562096215935296629 7238285396446520243934059)
        ·
          refine ⟨10857428094669780365901089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7238285396446520243934059 10857428094669780365901089)
          ·
            refine ⟨8143071071002335274425817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10857428094669780365901089 8143071071002335274425817)
            ·
              refine ⟨6107303303251751455819363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143071071002335274425817 6107303303251751455819363)
              ·
                refine ⟨9160954954877627183729045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107303303251751455819363 9160954954877627183729045)
                ·
                  refine ⟨429419763509888774237299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9160954954877627183729045 429419763509888774237299)
                  ·
                    rfl

theorem cell21_1881657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_1881657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881657 prefixEnd_1881657 := by exact prefixLift 1881657
  have htrace : WordTrace (prefixWord ++ tailWord_1881657) baseStart_1881657 baseEnd_1881657 := by
    simpa [prefixWord, tailWord_1881657, baseEnd_1881657] using wordTrace_append hprefix tailTrace_1881657
  have hstable : (prefixWord ++ tailWord_1881657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881657).length < 2 ^ (prefixWord ++ tailWord_1881657).sum := by decide
  have hdescent : baseEnd_1881657 < baseStart_1881657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881660 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1881660 : Nat := 118140960795 + 1881660 * 2 ^ 59
def prefixEnd_1881660 : Nat := 4983230072969 + 3 ^ 40 * 1881660 * 2
def baseEnd_1881660 : Nat := 429420448150761435687293

theorem tailTrace_1881660 : CollatzResearch.WordTrace tailWord_1881660 prefixEnd_1881660 429420448150761435687293 := by
  unfold tailWord_1881660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34314889181537328394089217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45753185575383104525452289 34314889181537328394089217)
  ·
    refine ⟨25736166886152996295566913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34314889181537328394089217 25736166886152996295566913)
    ·
      refine ⟨19302125164614747221675185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25736166886152996295566913 19302125164614747221675185)
      ·
        refine ⟨14476593873461060416256389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19302125164614747221675185 14476593873461060416256389)
        ·
          refine ⟨2714361351273948828048073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14476593873461060416256389 2714361351273948828048073)
          ·
            refine ⟨2035771013455461621036055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714361351273948828048073 2035771013455461621036055)
            ·
              refine ⟨3053656520183192431554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035771013455461621036055 3053656520183192431554083)
              ·
                refine ⟨4580484780274788647331125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053656520183192431554083 4580484780274788647331125)
                ·
                  refine ⟨429420448150761435687293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580484780274788647331125 429420448150761435687293)
                  ·
                    rfl

theorem cell21_1881660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1881660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881660 prefixEnd_1881660 := by exact prefixLift 1881660
  have htrace : WordTrace (prefixWord ++ tailWord_1881660) baseStart_1881660 baseEnd_1881660 := by
    simpa [prefixWord, tailWord_1881660, baseEnd_1881660] using wordTrace_append hprefix tailTrace_1881660
  have hstable : (prefixWord ++ tailWord_1881660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881660).length < 2 ^ (prefixWord ++ tailWord_1881660).sum := by decide
  have hdescent : baseEnd_1881660 < baseStart_1881660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881733 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_1881733 : Nat := 118140960795 + 1881733 * 2 ^ 59
def prefixEnd_1881733 : Nat := 4983230072969 + 3 ^ 40 * 1881733 * 2
def baseEnd_1881733 : Nat := 429437107745329530970477

theorem tailTrace_1881733 : CollatzResearch.WordTrace tailWord_1881733 prefixEnd_1881733 429437107745329530970477 := by
  unfold tailWord_1881733
  simp only [CollatzResearch.WordTrace]
  refine ⟨68632440891810190255585853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45754960594540126837057235 68632440891810190255585853)
  ·
    refine ⟨25737165334428821345844695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68632440891810190255585853 25737165334428821345844695)
    ·
      refine ⟨38605748001643232018767043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25737165334428821345844695 38605748001643232018767043)
      ·
        refine ⟨57908622002464848028150565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38605748001643232018767043 57908622002464848028150565)
        ·
          refine ⟨10857866625462159005278231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57908622002464848028150565 10857866625462159005278231)
          ·
            refine ⟨16286799938193238507917347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10857866625462159005278231 16286799938193238507917347)
            ·
              refine ⟨24430199907289857761876021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16286799938193238507917347 24430199907289857761876021)
              ·
                refine ⟨2290331241308424165175877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24430199907289857761876021 2290331241308424165175877)
                ·
                  refine ⟨429437107745329530970477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290331241308424165175877 429437107745329530970477)
                  ·
                    rfl

theorem cell21_1881733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_1881733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881733 prefixEnd_1881733 := by exact prefixLift 1881733
  have htrace : WordTrace (prefixWord ++ tailWord_1881733) baseStart_1881733 baseEnd_1881733 := by
    simpa [prefixWord, tailWord_1881733, baseEnd_1881733] using wordTrace_append hprefix tailTrace_1881733
  have hstable : (prefixWord ++ tailWord_1881733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881733).length < 2 ^ (prefixWord ++ tailWord_1881733).sum := by decide
  have hdescent : baseEnd_1881733 < baseStart_1881733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881736 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_1881736 : Nat := 118140960795 + 1881736 * 2 ^ 59
def prefixEnd_1881736 : Nat := 4983230072969 + 3 ^ 40 * 1881736 * 2
def baseEnd_1881736 : Nat := 429437792386202192420471

theorem tailTrace_1881736 : CollatzResearch.WordTrace tailWord_1881736 prefixEnd_1881736 429437792386202192420471 := by
  unfold tailWord_1881736
  simp only [CollatzResearch.WordTrace]
  refine ⟨34316275155399660883972531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45755033540532881178630041 34316275155399660883972531)
  ·
    refine ⟨51474412733099491325958797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34316275155399660883972531 51474412733099491325958797)
    ·
      refine ⟨19302904774912309247234549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51474412733099491325958797 19302904774912309247234549)
      ·
        refine ⟨1809647322648028991928239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19302904774912309247234549 1809647322648028991928239)
        ·
          refine ⟨2714470983972043487892359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809647322648028991928239 2714470983972043487892359)
          ·
            refine ⟨4071706475958065231838539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714470983972043487892359 4071706475958065231838539)
            ·
              refine ⟨6107559713937097847757809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071706475958065231838539 6107559713937097847757809)
              ·
                refine ⟨4580669785452823385818357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107559713937097847757809 4580669785452823385818357)
                ·
                  refine ⟨429437792386202192420471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580669785452823385818357 429437792386202192420471)
                  ·
                    rfl

theorem cell21_1881736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_1881736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881736 prefixEnd_1881736 := by exact prefixLift 1881736
  have htrace : WordTrace (prefixWord ++ tailWord_1881736) baseStart_1881736 baseEnd_1881736 := by
    simpa [prefixWord, tailWord_1881736, baseEnd_1881736] using wordTrace_append hprefix tailTrace_1881736
  have hstable : (prefixWord ++ tailWord_1881736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881736).length < 2 ^ (prefixWord ++ tailWord_1881736).sum := by decide
  have hdescent : baseEnd_1881736 < baseStart_1881736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881778 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1881778 : Nat := 118140960795 + 1881778 * 2 ^ 59
def prefixEnd_1881778 : Nat := 4983230072969 + 3 ^ 40 * 1881778 * 2
def baseEnd_1881778 : Nat := 429447377358419452720385

theorem tailTrace_1881778 : CollatzResearch.WordTrace tailWord_1881778 prefixEnd_1881778 429447377358419452720385 := by
  unfold tailWord_1881778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158520544161790735243497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45756054784431441960649325 17158520544161790735243497)
  ·
    refine ⟨12868890408121343051432623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17158520544161790735243497 12868890408121343051432623)
    ·
      refine ⟨19303335612182014577148935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12868890408121343051432623 19303335612182014577148935)
      ·
        refine ⟨28955003418273021865723403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19303335612182014577148935 28955003418273021865723403)
        ·
          refine ⟨43432505127409532798585105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28955003418273021865723403 43432505127409532798585105)
          ·
            refine ⟨32574378845557149598938829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43432505127409532798585105 32574378845557149598938829)
            ·
              refine ⟨12215392067083931099602061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32574378845557149598938829 12215392067083931099602061)
              ·
                refine ⟨4580772025156474162350773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12215392067083931099602061 4580772025156474162350773)
                ·
                  refine ⟨429447377358419452720385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580772025156474162350773 429447377358419452720385)
                  ·
                    rfl

theorem cell21_1881778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1881778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881778 prefixEnd_1881778 := by exact prefixLift 1881778
  have htrace : WordTrace (prefixWord ++ tailWord_1881778) baseStart_1881778 baseEnd_1881778 := by
    simpa [prefixWord, tailWord_1881778, baseEnd_1881778] using wordTrace_append hprefix tailTrace_1881778
  have hstable : (prefixWord ++ tailWord_1881778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881778).length < 2 ^ (prefixWord ++ tailWord_1881778).sum := by decide
  have hdescent : baseEnd_1881778 < baseStart_1881778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881798 : List Nat := [6, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1881798 : Nat := 118140960795 + 1881798 * 2 ^ 59
def prefixEnd_1881798 : Nat := 4983230072969 + 3 ^ 40 * 1881798 * 2
def baseEnd_1881798 : Nat := 143150647210301287462337

theorem tailTrace_1881798 : CollatzResearch.WordTrace tailWord_1881798 prefixEnd_1881798 143150647210301287462337 := by
  unfold tailWord_1881798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144837863642959573646939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45756541091049804237801365 2144837863642959573646939)
  ·
    refine ⟨3217256795464439360470409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144837863642959573646939 3217256795464439360470409)
    ·
      refine ⟨2412942596598329520352807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3217256795464439360470409 2412942596598329520352807)
      ·
        refine ⟨3619413894897494280529211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412942596598329520352807 3619413894897494280529211)
        ·
          refine ⟨5429120842346241420793817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619413894897494280529211 5429120842346241420793817)
          ·
            refine ⟨4071840631759681065595363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429120842346241420793817 4071840631759681065595363)
            ·
              refine ⟨6107760947639521598393045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071840631759681065595363 6107760947639521598393045)
              ·
                refine ⟨143150647210301287462337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6107760947639521598393045 143150647210301287462337)
                ·
                  rfl

theorem cell21_1881798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1881798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881798 prefixEnd_1881798 := by exact prefixLift 1881798
  have htrace : WordTrace (prefixWord ++ tailWord_1881798) baseStart_1881798 baseEnd_1881798 := by
    simpa [prefixWord, tailWord_1881798, baseEnd_1881798] using wordTrace_append hprefix tailTrace_1881798
  have hstable : (prefixWord ++ tailWord_1881798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881798).length < 2 ^ (prefixWord ++ tailWord_1881798).sum := by decide
  have hdescent : baseEnd_1881798 < baseStart_1881798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881868 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1881868 : Nat := 118140960795 + 1881868 * 2 ^ 59
def prefixEnd_1881868 : Nat := 4983230072969 + 3 ^ 40 * 1881868 * 2
def baseEnd_1881868 : Nat := 429467916584599296220201

theorem tailTrace_1881868 : CollatzResearch.WordTrace tailWord_1881868 prefixEnd_1881868 429467916584599296220201 := by
  unfold tailWord_1881868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318682373160554155875129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45758243164214072207833505 34318682373160554155875129)
  ·
    refine ⟨25739011779870415616906347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34318682373160554155875129 25739011779870415616906347)
    ·
      refine ⟨38608517669805623425359521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25739011779870415616906347 38608517669805623425359521)
      ·
        refine ⟨28956388252354217569019641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38608517669805623425359521 28956388252354217569019641)
        ·
          refine ⟨21717291189265663176764731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28956388252354217569019641 21717291189265663176764731)
          ·
            refine ⟨32575936783898494765147097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717291189265663176764731 32575936783898494765147097)
            ·
              refine ⟨24431952587923871073860323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32575936783898494765147097 24431952587923871073860323)
              ·
                refine ⟨36647928881885806610790485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24431952587923871073860323 36647928881885806610790485)
                ·
                  refine ⟨429467916584599296220201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36647928881885806610790485 429467916584599296220201)
                  ·
                    rfl

theorem cell21_1881868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1881868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881868 prefixEnd_1881868 := by exact prefixLift 1881868
  have htrace : WordTrace (prefixWord ++ tailWord_1881868) baseStart_1881868 baseEnd_1881868 := by
    simpa [prefixWord, tailWord_1881868, baseEnd_1881868] using wordTrace_append hprefix tailTrace_1881868
  have hstable : (prefixWord ++ tailWord_1881868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881868).length < 2 ^ (prefixWord ++ tailWord_1881868).sum := by decide
  have hdescent : baseEnd_1881868 < baseStart_1881868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881992 : List Nat := [2, 1, 3, 3, 3, 2, 7]
def baseStart_1881992 : Nat := 118140960795 + 1881992 * 2 ^ 59
def prefixEnd_1881992 : Nat := 4983230072969 + 3 ^ 40 * 1881992 * 2
def baseEnd_1881992 : Nat := 47721801674889181794809

theorem tailTrace_1881992 : CollatzResearch.WordTrace tailWord_1881992 prefixEnd_1881992 47721801674889181794809 := by
  unfold tailWord_1881992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34320943698935938744632115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45761258265247918326176153 34320943698935938744632115)
  ·
    refine ⟨51481415548403908116948173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34320943698935938744632115 51481415548403908116948173)
    ·
      refine ⟨19305530830651465543855565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51481415548403908116948173 19305530830651465543855565)
      ·
        refine ⟨7239574061494299578945837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19305530830651465543855565 7239574061494299578945837)
        ·
          refine ⟨2714840273060362342104689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7239574061494299578945837 2714840273060362342104689)
          ·
            refine ⟨2036130204795271756578517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714840273060362342104689 2036130204795271756578517)
            ·
              refine ⟨47721801674889181794809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2036130204795271756578517 47721801674889181794809)
              ·
                rfl

theorem cell21_1881992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 7].length) (baseStart_1881992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881992 prefixEnd_1881992 := by exact prefixLift 1881992
  have htrace : WordTrace (prefixWord ++ tailWord_1881992) baseStart_1881992 baseEnd_1881992 := by
    simpa [prefixWord, tailWord_1881992, baseEnd_1881992] using wordTrace_append hprefix tailTrace_1881992
  have hstable : (prefixWord ++ tailWord_1881992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881992).length < 2 ^ (prefixWord ++ tailWord_1881992).sum := by decide
  have hdescent : baseEnd_1881992 < baseStart_1881992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881998 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1881998 : Nat := 118140960795 + 1881998 * 2 ^ 59
def prefixEnd_1881998 : Nat := 4983230072969 + 3 ^ 40 * 1881998 * 2
def baseEnd_1881998 : Nat := 429497584355747959053269

theorem tailTrace_1881998 : CollatzResearch.WordTrace tailWord_1881998 prefixEnd_1881998 429497584355747959053269 := by
  unfold tailWord_1881998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580263279481267564247831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45761404157233427009321765 8580263279481267564247831)
  ·
    refine ⟨12870394919221901346371747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8580263279481267564247831 12870394919221901346371747)
    ·
      refine ⟨19305592378832852019557621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870394919221901346371747 19305592378832852019557621)
      ·
        refine ⟨1809899285515579876833527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19305592378832852019557621 1809899285515579876833527)
        ·
          refine ⟨2714848928273369815250291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809899285515579876833527 2714848928273369815250291)
          ·
            refine ⟨4072273392410054722875437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714848928273369815250291 4072273392410054722875437)
            ·
              refine ⟨1527102522153770521078289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4072273392410054722875437 1527102522153770521078289)
              ·
                refine ⟨1145326891615327890808717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527102522153770521078289 1145326891615327890808717)
                ·
                  refine ⟨429497584355747959053269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145326891615327890808717 429497584355747959053269)
                  ·
                    rfl

theorem cell21_1881998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1881998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1881998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1881998 prefixEnd_1881998 := by exact prefixLift 1881998
  have htrace : WordTrace (prefixWord ++ tailWord_1881998) baseStart_1881998 baseEnd_1881998 := by
    simpa [prefixWord, tailWord_1881998, baseEnd_1881998] using wordTrace_append hprefix tailTrace_1881998
  have hstable : (prefixWord ++ tailWord_1881998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881998).length < 2 ^ (prefixWord ++ tailWord_1881998).sum := by decide
  have hdescent : baseEnd_1881998 < baseStart_1881998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882116 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1882116 : Nat := 118140960795 + 1882116 * 2 ^ 59
def prefixEnd_1882116 : Nat := 4983230072969 + 3 ^ 40 * 1882116 * 2
def baseEnd_1882116 : Nat := 429524513563405976086361

theorem tailTrace_1882116 : CollatzResearch.WordTrace tailWord_1882116 prefixEnd_1882116 429524513563405976086361 := by
  unfold tailWord_1882116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323205024711323333389101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45764273366281764444518801 34323205024711323333389101)
  ·
    refine ⟨12871201884266746250020913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34323205024711323333389101 12871201884266746250020913)
    ·
      refine ⟨9653401413200059687515685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12871201884266746250020913 9653401413200059687515685)
      ·
        refine ⟨1810012764975011191409191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9653401413200059687515685 1810012764975011191409191)
        ·
          refine ⟨2715019147462516787113787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810012764975011191409191 2715019147462516787113787)
          ·
            refine ⟨4072528721193775180670681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715019147462516787113787 4072528721193775180670681)
            ·
              refine ⟨3054396540895331385503011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072528721193775180670681 3054396540895331385503011)
              ·
                refine ⟨4581594811342997078254517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054396540895331385503011 4581594811342997078254517)
                ·
                  refine ⟨429524513563405976086361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581594811342997078254517 429524513563405976086361)
                  ·
                    rfl

theorem cell21_1882116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1882116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882116 prefixEnd_1882116 := by exact prefixLift 1882116
  have htrace : WordTrace (prefixWord ++ tailWord_1882116) baseStart_1882116 baseEnd_1882116 := by
    simpa [prefixWord, tailWord_1882116, baseEnd_1882116] using wordTrace_append hprefix tailTrace_1882116
  have hstable : (prefixWord ++ tailWord_1882116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882116).length < 2 ^ (prefixWord ++ tailWord_1882116).sum := by decide
  have hdescent : baseEnd_1882116 < baseStart_1882116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882172 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1882172 : Nat := 118140960795 + 1882172 * 2 ^ 59
def prefixEnd_1882172 : Nat := 4983230072969 + 3 ^ 40 * 1882172 * 2
def baseEnd_1882172 : Nat := 429537293526362323152913

theorem tailTrace_1882172 : CollatzResearch.WordTrace tailWord_1882172 prefixEnd_1882172 429537293526362323152913 := by
  unfold tailWord_1882172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34324226268609884115408385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45765635024813178820544513 34324226268609884115408385)
  ·
    refine ⟨25743169701457413086556289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34324226268609884115408385 25743169701457413086556289)
    ·
      refine ⟨19307377276093059814917217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25743169701457413086556289 19307377276093059814917217)
      ·
        refine ⟨14480532957069794861187913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19307377276093059814917217 14480532957069794861187913)
        ·
          refine ⟨10860399717802346145890935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14480532957069794861187913 10860399717802346145890935)
          ·
            refine ⟨16290599576703519218836403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860399717802346145890935 16290599576703519218836403)
            ·
              refine ⟨24435899365055278828254605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16290599576703519218836403 24435899365055278828254605)
              ·
                refine ⟨9163462261895729560595477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24435899365055278828254605 9163462261895729560595477)
                ·
                  refine ⟨429537293526362323152913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9163462261895729560595477 429537293526362323152913)
                  ·
                    rfl

theorem cell21_1882172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1882172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882172 prefixEnd_1882172 := by exact prefixLift 1882172
  have htrace : WordTrace (prefixWord ++ tailWord_1882172) baseStart_1882172 baseEnd_1882172 := by
    simpa [prefixWord, tailWord_1882172, baseEnd_1882172] using wordTrace_append hprefix tailTrace_1882172
  have hstable : (prefixWord ++ tailWord_1882172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882172).length < 2 ^ (prefixWord ++ tailWord_1882172).sum := by decide
  have hdescent : baseEnd_1882172 < baseStart_1882172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882282 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1882282 : Nat := 118140960795 + 1882282 * 2 ^ 59
def prefixEnd_1882282 : Nat := 4983230072969 + 3 ^ 40 * 1882282 * 2
def baseEnd_1882282 : Nat := 429562397025026576319355

theorem tailTrace_1882282 : CollatzResearch.WordTrace tailWord_1882282 prefixEnd_1882282 429562397025026576319355 := by
  unfold tailWord_1882282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163116141705314254330275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45768309711214171344880733 17163116141705314254330275)
  ·
    refine ⟨25744674212557971381495413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17163116141705314254330275 25744674212557971381495413)
    ·
      refine ⟨2413563207427309817015195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25744674212557971381495413 2413563207427309817015195)
      ·
        refine ⟨3620344811140964725522793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413563207427309817015195 3620344811140964725522793)
        ·
          refine ⟨2715258608355723544142095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620344811140964725522793 2715258608355723544142095)
          ·
            refine ⟨4072887912533585316213143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715258608355723544142095 4072887912533585316213143)
            ·
              refine ⟨6109331868800377974319715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072887912533585316213143 6109331868800377974319715)
              ·
                refine ⟨9163997803200566961479573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109331868800377974319715 9163997803200566961479573)
                ·
                  refine ⟨429562397025026576319355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9163997803200566961479573 429562397025026576319355)
                  ·
                    rfl

theorem cell21_1882282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1882282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882282 prefixEnd_1882282 := by exact prefixLift 1882282
  have htrace : WordTrace (prefixWord ++ tailWord_1882282) baseStart_1882282 baseEnd_1882282 := by
    simpa [prefixWord, tailWord_1882282, baseEnd_1882282] using wordTrace_append hprefix tailTrace_1882282
  have hstable : (prefixWord ++ tailWord_1882282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882282).length < 2 ^ (prefixWord ++ tailWord_1882282).sum := by decide
  have hdescent : baseEnd_1882282 < baseStart_1882282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882344 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_1882344 : Nat := 118140960795 + 1882344 * 2 ^ 59
def prefixEnd_1882344 : Nat := 4983230072969 + 3 ^ 40 * 1882344 * 2
def baseEnd_1882344 : Nat := 429576546269728246285895

theorem tailTrace_1882344 : CollatzResearch.WordTrace tailWord_1882344 prefixEnd_1882344 429576546269728246285895 := by
  unfold tailWord_1882344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327362946298320803039043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45769817261731094404052057 34327362946298320803039043)
  ·
    refine ⟨51491044419447481204558565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34327362946298320803039043 51491044419447481204558565)
    ·
      refine ⟨9654570828646402725854731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51491044419447481204558565 9654570828646402725854731)
      ·
        refine ⟨14481856242969604088782097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654570828646402725854731 14481856242969604088782097)
        ·
          refine ⟨10861392182227203066586573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14481856242969604088782097 10861392182227203066586573)
          ·
            refine ⟨4073022068335201149969965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10861392182227203066586573 4073022068335201149969965)
            ·
              refine ⟨1527383275625700431238737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4073022068335201149969965 1527383275625700431238737)
              ·
                refine ⟨1145537456719275323429053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527383275625700431238737 1145537456719275323429053)
                ·
                  refine ⟨429576546269728246285895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145537456719275323429053 429576546269728246285895)
                  ·
                    rfl

theorem cell21_1882344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_1882344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882344 prefixEnd_1882344 := by exact prefixLift 1882344
  have htrace : WordTrace (prefixWord ++ tailWord_1882344) baseStart_1882344 baseEnd_1882344 := by
    simpa [prefixWord, tailWord_1882344, baseEnd_1882344] using wordTrace_append hprefix tailTrace_1882344
  have hstable : (prefixWord ++ tailWord_1882344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882344).length < 2 ^ (prefixWord ++ tailWord_1882344).sum := by decide
  have hdescent : baseEnd_1882344 < baseStart_1882344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882358 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1882358 : Nat := 118140960795 + 1882358 * 2 ^ 59
def prefixEnd_1882358 : Nat := 4983230072969 + 3 ^ 40 * 1882358 * 2
def baseEnd_1882358 : Nat := 429579741260467333052533

theorem tailTrace_1882358 : CollatzResearch.WordTrace tailWord_1882358 prefixEnd_1882358 429579741260467333052533 := by
  unfold tailWord_1882358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290952282159120124817983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45770157676363947998058485 4290952282159120124817983)
  ·
    refine ⟨6436428423238680187226975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290952282159120124817983 6436428423238680187226975)
    ·
      refine ⟨9654642634858020280840463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436428423238680187226975 9654642634858020280840463)
      ·
        refine ⟨14481963952287030421260695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654642634858020280840463 14481963952287030421260695)
        ·
          refine ⟨21722945928430545631891043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481963952287030421260695 21722945928430545631891043)
          ·
            refine ⟨32584418892645818447836565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722945928430545631891043 32584418892645818447836565)
            ·
              refine ⟨1527394635592772739742339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32584418892645818447836565 1527394635592772739742339)
              ·
                refine ⟨2291091953389159109613509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527394635592772739742339 2291091953389159109613509)
                ·
                  refine ⟨429579741260467333052533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291091953389159109613509 429579741260467333052533)
                  ·
                    rfl

theorem cell21_1882358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1882358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882358 prefixEnd_1882358 := by exact prefixLift 1882358
  have htrace : WordTrace (prefixWord ++ tailWord_1882358) baseStart_1882358 baseEnd_1882358 := by
    simpa [prefixWord, tailWord_1882358, baseEnd_1882358] using wordTrace_append hprefix tailTrace_1882358
  have hstable : (prefixWord ++ tailWord_1882358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882358).length < 2 ^ (prefixWord ++ tailWord_1882358).sum := by decide
  have hdescent : baseEnd_1882358 < baseStart_1882358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882369 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_1882369 : Nat := 118140960795 + 1882369 * 2 ^ 59
def prefixEnd_1882369 : Nat := 4983230072969 + 3 ^ 40 * 1882369 * 2
def baseEnd_1882369 : Nat := 429582251610333758369177

theorem tailTrace_1882369 : CollatzResearch.WordTrace tailWord_1882369 prefixEnd_1882369 429582251610333758369177 := by
  unfold tailWord_1882369
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655637717506070875738161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45770425145004047250492107 68655637717506070875738161)
  ·
    refine ⟨51491728288129553156803621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68655637717506070875738161 51491728288129553156803621)
    ·
      refine ⟨9654699054024291216900679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51491728288129553156803621 9654699054024291216900679)
      ·
        refine ⟨14482048581036436825351019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654699054024291216900679 14482048581036436825351019)
        ·
          refine ⟨21723072871554655238026529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482048581036436825351019 21723072871554655238026529)
          ·
            refine ⟨16292304653665991428519897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723072871554655238026529 16292304653665991428519897)
            ·
              refine ⟨12219228490249493571389923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16292304653665991428519897 12219228490249493571389923)
              ·
                refine ⟨18328842735374240357084885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12219228490249493571389923 18328842735374240357084885)
                ·
                  refine ⟨429582251610333758369177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18328842735374240357084885 429582251610333758369177)
                  ·
                    rfl

theorem cell21_1882369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_1882369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882369 prefixEnd_1882369 := by exact prefixLift 1882369
  have htrace : WordTrace (prefixWord ++ tailWord_1882369) baseStart_1882369 baseEnd_1882369 := by
    simpa [prefixWord, tailWord_1882369, baseEnd_1882369] using wordTrace_append hprefix tailTrace_1882369
  have hstable : (prefixWord ++ tailWord_1882369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882369).length < 2 ^ (prefixWord ++ tailWord_1882369).sum := by decide
  have hdescent : baseEnd_1882369 < baseStart_1882369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882383 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_1882383 : Nat := 118140960795 + 1882383 * 2 ^ 59
def prefixEnd_1882383 : Nat := 4983230072969 + 3 ^ 40 * 1882383 * 2
def baseEnd_1882383 : Nat := 429585446601072845135815

theorem tailTrace_1882383 : CollatzResearch.WordTrace tailWord_1882383 prefixEnd_1882383 429585446601072845135815 := by
  unfold tailWord_1882383
  simp only [CollatzResearch.WordTrace]
  refine ⟨68656148339455351266747803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45770765559636900844498535 68656148339455351266747803)
  ·
    refine ⟨102984222509183026900121705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68656148339455351266747803 102984222509183026900121705)
    ·
      refine ⟨77238166881887270175091279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102984222509183026900121705 77238166881887270175091279)
      ·
        refine ⟨115857250322830905262636919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77238166881887270175091279 115857250322830905262636919)
        ·
          refine ⟨173785875484246357893955379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115857250322830905262636919 173785875484246357893955379)
          ·
            refine ⟨260678813226369536840933069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173785875484246357893955379 260678813226369536840933069)
            ·
              refine ⟨97754554959888576315349901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260678813226369536840933069 97754554959888576315349901)
              ·
                refine ⟨36657958109958216118256213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97754554959888576315349901 36657958109958216118256213)
                ·
                  refine ⟨429585446601072845135815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36657958109958216118256213 429585446601072845135815)
                  ·
                    rfl

theorem cell21_1882383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_1882383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882383 prefixEnd_1882383 := by exact prefixLift 1882383
  have htrace : WordTrace (prefixWord ++ tailWord_1882383) baseStart_1882383 baseEnd_1882383 := by
    simpa [prefixWord, tailWord_1882383, baseEnd_1882383] using wordTrace_append hprefix tailTrace_1882383
  have hstable : (prefixWord ++ tailWord_1882383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882383).length < 2 ^ (prefixWord ++ tailWord_1882383).sum := by decide
  have hdescent : baseEnd_1882383 < baseStart_1882383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882431 : List Nat := [1, 1, 2, 2, 4, 1, 5, 5]
def baseStart_1882431 : Nat := 118140960795 + 1882431 * 2 ^ 59
def prefixEnd_1882431 : Nat := 4983230072969 + 3 ^ 40 * 1882431 * 2
def baseEnd_1882431 : Nat := 143198800285011809445239

theorem tailTrace_1882431 : CollatzResearch.WordTrace tailWord_1882431 prefixEnd_1882431 143198800285011809445239 := by
  unfold tailWord_1882431
  simp only [CollatzResearch.WordTrace]
  refine ⟨68657899043281455464495147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45771932695520970309663431 68657899043281455464495147)
  ·
    refine ⟨102986848564922183196742721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68657899043281455464495147 102986848564922183196742721)
    ·
      refine ⟨77240136423691637397557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102986848564922183196742721 77240136423691637397557041)
      ·
        refine ⟨57930102317768728048167781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77240136423691637397557041 57930102317768728048167781)
        ·
          refine ⟨10861894184581636509031459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57930102317768728048167781 10861894184581636509031459)
          ·
            refine ⟨16292841276872454763547189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861894184581636509031459 16292841276872454763547189)
            ·
              refine ⟨1527453869706792634082549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16292841276872454763547189 1527453869706792634082549)
              ·
                refine ⟨143198800285011809445239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1527453869706792634082549 143198800285011809445239)
                ·
                  rfl

theorem cell21_1882431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].length) (baseStart_1882431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882431 prefixEnd_1882431 := by exact prefixLift 1882431
  have htrace : WordTrace (prefixWord ++ tailWord_1882431) baseStart_1882431 baseEnd_1882431 := by
    simpa [prefixWord, tailWord_1882431, baseEnd_1882431] using wordTrace_append hprefix tailTrace_1882431
  have hstable : (prefixWord ++ tailWord_1882431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882431).length < 2 ^ (prefixWord ++ tailWord_1882431).sum := by decide
  have hdescent : baseEnd_1882431 < baseStart_1882431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882611 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_1882611 : Nat := 118140960795 + 1882611 * 2 ^ 59
def prefixEnd_1882611 : Nat := 4983230072969 + 3 ^ 40 * 1882611 * 2
def baseEnd_1882611 : Nat := 429637479307395115335349

theorem tailTrace_1882611 : CollatzResearch.WordTrace tailWord_1882611 prefixEnd_1882611 429637479307395115335349 := by
  unfold tailWord_1882611
  simp only [CollatzResearch.WordTrace]
  refine ⟨68664464182629346206047687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45776309455086230804031791 68664464182629346206047687)
  ·
    refine ⟨102996696273944019309071531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68664464182629346206047687 102996696273944019309071531)
    ·
      refine ⟨154495044410916028963607297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102996696273944019309071531 154495044410916028963607297)
      ·
        refine ⟨115871283308187021722705473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154495044410916028963607297 115871283308187021722705473)
        ·
          refine ⟨86903462481140266292029105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115871283308187021722705473 86903462481140266292029105)
          ·
            refine ⟨65177596860855199719021829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86903462481140266292029105 65177596860855199719021829)
            ·
              refine ⟨12220799411410349947316593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65177596860855199719021829 12220799411410349947316593)
              ·
                refine ⟨9165599558557762460487445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220799411410349947316593 9165599558557762460487445)
                ·
                  refine ⟨429637479307395115335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9165599558557762460487445 429637479307395115335349)
                  ·
                    rfl

theorem cell21_1882611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_1882611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882611 prefixEnd_1882611 := by exact prefixLift 1882611
  have htrace : WordTrace (prefixWord ++ tailWord_1882611) baseStart_1882611 baseEnd_1882611 := by
    simpa [prefixWord, tailWord_1882611, baseEnd_1882611] using wordTrace_append hprefix tailTrace_1882611
  have hstable : (prefixWord ++ tailWord_1882611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882611).length < 2 ^ (prefixWord ++ tailWord_1882611).sum := by decide
  have hdescent : baseEnd_1882611 < baseStart_1882611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882645 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 4]
def baseStart_1882645 : Nat := 118140960795 + 1882645 * 2 ^ 59
def prefixEnd_1882645 : Nat := 4983230072969 + 3 ^ 40 * 1882645 * 2
def baseEnd_1882645 : Nat := 429645238570618611768613

theorem tailTrace_1882645 : CollatzResearch.WordTrace tailWord_1882645 prefixEnd_1882645 429645238570618611768613 := by
  unfold tailWord_1882645
  simp only [CollatzResearch.WordTrace]
  refine ⟨68665704264506170012785389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45777136176337446675190259 68665704264506170012785389)
  ·
    refine ⟨25749639099189813754794521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68665704264506170012785389 25749639099189813754794521)
    ·
      refine ⟨19312229324392360316095891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25749639099189813754794521 19312229324392360316095891)
      ·
        refine ⟨28968343986588540474143837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19312229324392360316095891 28968343986588540474143837)
        ·
          refine ⟨10863128994970702677803939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28968343986588540474143837 10863128994970702677803939)
          ·
            refine ⟨16294693492456054016705909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863128994970702677803939 16294693492456054016705909)
            ·
              refine ⟨1527627514917755064066179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16294693492456054016705909 1527627514917755064066179)
              ·
                refine ⟨2291441272376632596099269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527627514917755064066179 2291441272376632596099269)
                ·
                  refine ⟨429645238570618611768613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291441272376632596099269 429645238570618611768613)
                  ·
                    rfl

theorem cell21_1882645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_1882645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882645 prefixEnd_1882645 := by exact prefixLift 1882645
  have htrace : WordTrace (prefixWord ++ tailWord_1882645) baseStart_1882645 baseEnd_1882645 := by
    simpa [prefixWord, tailWord_1882645, baseEnd_1882645] using wordTrace_append hprefix tailTrace_1882645
  have hstable : (prefixWord ++ tailWord_1882645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882645).length < 2 ^ (prefixWord ++ tailWord_1882645).sum := by decide
  have hdescent : baseEnd_1882645 < baseStart_1882645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882659 : List Nat := [1, 1, 1, 4, 4, 1, 4, 5]
def baseStart_1882659 : Nat := 118140960795 + 1882659 * 2 ^ 59
def prefixEnd_1882659 : Nat := 4983230072969 + 3 ^ 40 * 1882659 * 2
def baseEnd_1882659 : Nat := 143216144520452566178417

theorem tailTrace_1882659 : CollatzResearch.WordTrace tailWord_1882659 prefixEnd_1882659 143216144520452566178417 := by
  unfold tailWord_1882659
  simp only [CollatzResearch.WordTrace]
  refine ⟨68666214886455450403795031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45777476590970300269196687 68666214886455450403795031)
  ·
    refine ⟨102999322329683175605692547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68666214886455450403795031 102999322329683175605692547)
    ·
      refine ⟨154498983494524763408538821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102999322329683175605692547 154498983494524763408538821)
      ·
        refine ⟨28968559405223393139101029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154498983494524763408538821 28968559405223393139101029)
        ·
          refine ⟨5431604888479386213581443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28968559405223393139101029 5431604888479386213581443)
          ·
            refine ⟨8147407332719079320372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431604888479386213581443 8147407332719079320372165)
            ·
              refine ⟨1527638874884827372569781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8147407332719079320372165 1527638874884827372569781)
              ·
                refine ⟨143216144520452566178417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1527638874884827372569781 143216144520452566178417)
                ·
                  rfl

theorem cell21_1882659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].length) (baseStart_1882659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882659 prefixEnd_1882659 := by exact prefixLift 1882659
  have htrace : WordTrace (prefixWord ++ tailWord_1882659) baseStart_1882659 baseEnd_1882659 := by
    simpa [prefixWord, tailWord_1882659, baseEnd_1882659] using wordTrace_append hprefix tailTrace_1882659
  have hstable : (prefixWord ++ tailWord_1882659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882659).length < 2 ^ (prefixWord ++ tailWord_1882659).sum := by decide
  have hdescent : baseEnd_1882659 < baseStart_1882659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882687 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_1882687 : Nat := 118140960795 + 1882687 * 2 ^ 59
def prefixEnd_1882687 : Nat := 4983230072969 + 3 ^ 40 * 1882687 * 2
def baseEnd_1882687 : Nat := 429654823542835872068527

theorem tailTrace_1882687 : CollatzResearch.WordTrace tailWord_1882687 prefixEnd_1882687 429654823542835872068527 := by
  unfold tailWord_1882687
  simp only [CollatzResearch.WordTrace]
  refine ⟨68667236130354011185814315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45778157420236007457209543 68667236130354011185814315)
  ·
    refine ⟨103000854195531016778721473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68667236130354011185814315 103000854195531016778721473)
    ·
      refine ⟨77250640646648262584041105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103000854195531016778721473 77250640646648262584041105)
      ·
        refine ⟨57937980484986196938030829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77250640646648262584041105 57937980484986196938030829)
        ·
          refine ⟨21726742681869823851761561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57937980484986196938030829 21726742681869823851761561)
          ·
            refine ⟨16295057011402367888821171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21726742681869823851761561 16295057011402367888821171)
            ·
              refine ⟨24442585517103551833231757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295057011402367888821171 24442585517103551833231757)
              ·
                refine ⟨9165969568913831937461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24442585517103551833231757 9165969568913831937461909)
                ·
                  refine ⟨429654823542835872068527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9165969568913831937461909 429654823542835872068527)
                  ·
                    rfl

theorem cell21_1882687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_1882687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882687 prefixEnd_1882687 := by exact prefixLift 1882687
  have htrace : WordTrace (prefixWord ++ tailWord_1882687) baseStart_1882687 baseEnd_1882687 := by
    simpa [prefixWord, tailWord_1882687, baseEnd_1882687] using wordTrace_append hprefix tailTrace_1882687
  have hstable : (prefixWord ++ tailWord_1882687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882687).length < 2 ^ (prefixWord ++ tailWord_1882687).sum := by decide
  have hdescent : baseEnd_1882687 < baseStart_1882687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882741 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 3]
def baseStart_1882741 : Nat := 118140960795 + 1882741 * 2 ^ 59
def prefixEnd_1882741 : Nat := 4983230072969 + 3 ^ 40 * 1882741 * 2
def baseEnd_1882741 : Nat := 429667147078543778168417

theorem tailTrace_1882741 : CollatzResearch.WordTrace tailWord_1882741 prefixEnd_1882741 429667147078543778168417 := by
  unfold tailWord_1882741
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669205672158378408280077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45779470448105585605520051 68669205672158378408280077)
  ·
    refine ⟨25750952127059391903105029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68669205672158378408280077 25750952127059391903105029)
    ·
      refine ⟨4828303523823635981832193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25750952127059391903105029 4828303523823635981832193)
      ·
        refine ⟨3621227642867726986374145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828303523823635981832193 3621227642867726986374145)
        ·
          refine ⟨2715920732150795239780609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621227642867726986374145 2715920732150795239780609)
          ·
            refine ⟨2036940549113096429835457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715920732150795239780609 2036940549113096429835457)
            ·
              refine ⟨1527705411834822322376593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036940549113096429835457 1527705411834822322376593)
              ·
                refine ⟨1145779058876116741782445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527705411834822322376593 1145779058876116741782445)
                ·
                  refine ⟨429667147078543778168417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145779058876116741782445 429667147078543778168417)
                  ·
                    rfl

theorem cell21_1882741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_1882741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882741 prefixEnd_1882741 := by exact prefixLift 1882741
  have htrace : WordTrace (prefixWord ++ tailWord_1882741) baseStart_1882741 baseEnd_1882741 := by
    simpa [prefixWord, tailWord_1882741, baseEnd_1882741] using wordTrace_append hprefix tailTrace_1882741
  have hstable : (prefixWord ++ tailWord_1882741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882741).length < 2 ^ (prefixWord ++ tailWord_1882741).sum := by decide
  have hdescent : baseEnd_1882741 < baseStart_1882741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882797 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1882797 : Nat := 118140960795 + 1882797 * 2 ^ 59
def prefixEnd_1882797 : Nat := 4983230072969 + 3 ^ 40 * 1882797 * 2
def baseEnd_1882797 : Nat := 429679927041500125234969

theorem tailTrace_1882797 : CollatzResearch.WordTrace tailWord_1882797 prefixEnd_1882797 429679927041500125234969 := by
  unfold tailWord_1882797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68671248159955499972318645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45780832106636999981545763 68671248159955499972318645)
  ·
    refine ⟨6437929514995828122404873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68671248159955499972318645 6437929514995828122404873)
    ·
      refine ⟨4828447136246871091803655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6437929514995828122404873 4828447136246871091803655)
      ·
        refine ⟨7242670704370306637705483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828447136246871091803655 7242670704370306637705483)
        ·
          refine ⟨10864006056555459956558225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242670704370306637705483 10864006056555459956558225)
          ·
            refine ⟨8148004542416594967418669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10864006056555459956558225 8148004542416594967418669)
            ·
              refine ⟨3055501703406223112782001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148004542416594967418669 3055501703406223112782001)
              ·
                refine ⟨2291626277554667334586501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055501703406223112782001 2291626277554667334586501)
                ·
                  refine ⟨429679927041500125234969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291626277554667334586501 429679927041500125234969)
                  ·
                    rfl

theorem cell21_1882797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1882797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882797 prefixEnd_1882797 := by exact prefixLift 1882797
  have htrace : WordTrace (prefixWord ++ tailWord_1882797) baseStart_1882797 baseEnd_1882797 := by
    simpa [prefixWord, tailWord_1882797, baseEnd_1882797] using wordTrace_append hprefix tailTrace_1882797
  have hstable : (prefixWord ++ tailWord_1882797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882797).length < 2 ^ (prefixWord ++ tailWord_1882797).sum := by decide
  have hdescent : baseEnd_1882797 < baseStart_1882797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882828 : List Nat := [2, 2, 1, 5, 1, 3, 2, 5]
def baseStart_1882828 : Nat := 118140960795 + 1882828 * 2 ^ 59
def prefixEnd_1882828 : Nat := 4983230072969 + 3 ^ 40 * 1882828 * 2
def baseEnd_1882828 : Nat := 143229000554616986739413

theorem tailTrace_1882828 : CollatzResearch.WordTrace tailWord_1882828 prefixEnd_1882828 143229000554616986739413 := by
  unfold tailWord_1882828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34336189411421596133348569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45781585881895461511131425 34336189411421596133348569)
  ·
    refine ⟨25752142058566197100011427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34336189411421596133348569 25752142058566197100011427)
    ·
      refine ⟨38628213087849295650017141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25752142058566197100011427 38628213087849295650017141)
      ·
        refine ⟨3621394976985871467189107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38628213087849295650017141 3621394976985871467189107)
        ·
          refine ⟨5432092465478807200783661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621394976985871467189107 5432092465478807200783661)
          ·
            refine ⟨2037034674554552700293873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432092465478807200783661 2037034674554552700293873)
            ·
              refine ⟨1527776005915914525220405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037034674554552700293873 1527776005915914525220405)
              ·
                refine ⟨143229000554616986739413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1527776005915914525220405 143229000554616986739413)
                ·
                  rfl

theorem cell21_1882828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_1882828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882828 prefixEnd_1882828 := by exact prefixLift 1882828
  have htrace : WordTrace (prefixWord ++ tailWord_1882828) baseStart_1882828 baseEnd_1882828 := by
    simpa [prefixWord, tailWord_1882828, baseEnd_1882828] using wordTrace_append hprefix tailTrace_1882828
  have hstable : (prefixWord ++ tailWord_1882828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882828).length < 2 ^ (prefixWord ++ tailWord_1882828).sum := by decide
  have hdescent : baseEnd_1882828 < baseStart_1882828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882839 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_1882839 : Nat := 118140960795 + 1882839 * 2 ^ 59
def prefixEnd_1882839 : Nat := 4983230072969 + 3 ^ 40 * 1882839 * 2
def baseEnd_1882839 : Nat := 429689512013717385534883

theorem tailTrace_1882839 : CollatzResearch.WordTrace tailWord_1882839 prefixEnd_1882839 429689512013717385534883 := by
  unfold tailWord_1882839
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672780025803341145347571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45781853350535560763565047 68672780025803341145347571)
  ·
    refine ⟨103009170038705011718021357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672780025803341145347571 103009170038705011718021357)
    ·
      refine ⟨38628438764514379394258009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103009170038705011718021357 38628438764514379394258009)
      ·
        refine ⟨28971329073385784545693507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38628438764514379394258009 28971329073385784545693507)
        ·
          refine ⟨43456993610078676818540261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28971329073385784545693507 43456993610078676818540261)
          ·
            refine ⟨8148186301889751903476299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43456993610078676818540261 8148186301889751903476299)
            ·
              refine ⟨12222279452834627855214449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148186301889751903476299 12222279452834627855214449)
              ·
                refine ⟨9166709589625970891410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222279452834627855214449 9166709589625970891410837)
                ·
                  refine ⟨429689512013717385534883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9166709589625970891410837 429689512013717385534883)
                  ·
                    rfl

theorem cell21_1882839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_1882839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882839 prefixEnd_1882839 := by exact prefixLift 1882839
  have htrace : WordTrace (prefixWord ++ tailWord_1882839) baseStart_1882839 baseEnd_1882839 := by
    simpa [prefixWord, tailWord_1882839, baseEnd_1882839] using wordTrace_append hprefix tailTrace_1882839
  have hstable : (prefixWord ++ tailWord_1882839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882839).length < 2 ^ (prefixWord ++ tailWord_1882839).sum := by decide
  have hdescent : baseEnd_1882839 < baseStart_1882839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882991 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_1882991 : Nat := 118140960795 + 1882991 * 2 ^ 59
def prefixEnd_1882991 : Nat := 4983230072969 + 3 ^ 40 * 1882991 * 2
def baseEnd_1882991 : Nat := 429724200484598899001239

theorem tailTrace_1882991 : CollatzResearch.WordTrace tailWord_1882991 prefixEnd_1882991 429724200484598899001239 := by
  unfold tailWord_1882991
  simp only [CollatzResearch.WordTrace]
  refine ⟨68678323921252671104880827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45785549280835114069920551 68678323921252671104880827)
  ·
    refine ⟨103017485881879006657321241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68678323921252671104880827 103017485881879006657321241)
    ·
      refine ⟨77263114411409254992990931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103017485881879006657321241 77263114411409254992990931)
      ·
        refine ⟨115894671617113882489486397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77263114411409254992990931 115894671617113882489486397)
        ·
          refine ⟨43460501856417705933557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115894671617113882489486397 43460501856417705933557399)
          ·
            refine ⟨65190752784626558900336099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43460501856417705933557399 65190752784626558900336099)
            ·
              refine ⟨97786129176939838350504149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65190752784626558900336099 97786129176939838350504149)
              ·
                refine ⟨2291862402584527461339941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97786129176939838350504149 2291862402584527461339941)
                ·
                  refine ⟨429724200484598899001239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291862402584527461339941 429724200484598899001239)
                  ·
                    rfl

theorem cell21_1882991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_1882991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1882991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1882991 prefixEnd_1882991 := by exact prefixLift 1882991
  have htrace : WordTrace (prefixWord ++ tailWord_1882991) baseStart_1882991 baseEnd_1882991 := by
    simpa [prefixWord, tailWord_1882991, baseEnd_1882991] using wordTrace_append hprefix tailTrace_1882991
  have hstable : (prefixWord ++ tailWord_1882991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882991).length < 2 ^ (prefixWord ++ tailWord_1882991).sum := by decide
  have hdescent : baseEnd_1882991 < baseStart_1882991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883042 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1883042 : Nat := 118140960795 + 1883042 * 2 ^ 59
def prefixEnd_1883042 : Nat := 4983230072969 + 3 ^ 40 * 1883042 * 2
def baseEnd_1883042 : Nat := 429735839379434143651135

theorem tailTrace_1883042 : CollatzResearch.WordTrace tailWord_1883042 prefixEnd_1883042 429735839379434143651135 := by
  unfold tailWord_1883042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170046011016976703746845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45786789362711937876658253 17170046011016976703746845)
  ·
    refine ⟨6438767254131366263905067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17170046011016976703746845 6438767254131366263905067)
    ·
      refine ⟨9658150881197049395857601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438767254131366263905067 9658150881197049395857601)
      ·
        refine ⟨7243613160897787046893201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658150881197049395857601 7243613160897787046893201)
        ·
          refine ⟨5432709870673340285169901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7243613160897787046893201 5432709870673340285169901)
          ·
            refine ⟨2037266201502502606938713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432709870673340285169901 2037266201502502606938713)
            ·
              refine ⟨1527949651126876955204035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037266201502502606938713 1527949651126876955204035)
              ·
                refine ⟨2291924476690315432806053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527949651126876955204035 2291924476690315432806053)
                ·
                  refine ⟨429735839379434143651135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291924476690315432806053 429735839379434143651135)
                  ·
                    rfl

theorem cell21_1883042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1883042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883042 prefixEnd_1883042 := by exact prefixLift 1883042
  have htrace : WordTrace (prefixWord ++ tailWord_1883042) baseStart_1883042 baseEnd_1883042 := by
    simpa [prefixWord, tailWord_1883042, baseEnd_1883042] using wordTrace_append hprefix tailTrace_1883042
  have hstable : (prefixWord ++ tailWord_1883042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883042).length < 2 ^ (prefixWord ++ tailWord_1883042).sum := by decide
  have hdescent : baseEnd_1883042 < baseStart_1883042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883070 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1883070 : Nat := 118140960795 + 1883070 * 2 ^ 59
def prefixEnd_1883070 : Nat := 4983230072969 + 3 ^ 40 * 1883070 * 2
def baseEnd_1883070 : Nat := 429742229360912317184411

theorem tailTrace_1883070 : CollatzResearch.WordTrace tailWord_1883070 prefixEnd_1883070 429742229360912317184411 := by
  unfold tailWord_1883070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585150660995808449625833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45787470191977645064671109 8585150660995808449625833)
  ·
    refine ⟨6438862995746856337219375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8585150660995808449625833 6438862995746856337219375)
    ·
      refine ⟨9658294493620284505829063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438862995746856337219375 9658294493620284505829063)
      ·
        refine ⟨14487441740430426758743595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658294493620284505829063 14487441740430426758743595)
        ·
          refine ⟨21731162610645640138115393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487441740430426758743595 21731162610645640138115393)
          ·
            refine ⟨16298371957984230103586545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21731162610645640138115393 16298371957984230103586545)
            ·
              refine ⟨12223778968488172577689909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16298371957984230103586545 12223778968488172577689909)
              ·
                refine ⟨1145979278295766179158429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12223778968488172577689909 1145979278295766179158429)
                ·
                  refine ⟨429742229360912317184411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145979278295766179158429 429742229360912317184411)
                  ·
                    rfl

theorem cell21_1883070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1883070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883070 prefixEnd_1883070 := by exact prefixLift 1883070
  have htrace : WordTrace (prefixWord ++ tailWord_1883070) baseStart_1883070 baseEnd_1883070 := by
    simpa [prefixWord, tailWord_1883070, baseEnd_1883070] using wordTrace_append hprefix tailTrace_1883070
  have hstable : (prefixWord ++ tailWord_1883070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883070).length < 2 ^ (prefixWord ++ tailWord_1883070).sum := by decide
  have hdescent : baseEnd_1883070 < baseStart_1883070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883084 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1883084 : Nat := 118140960795 + 1883084 * 2 ^ 59
def prefixEnd_1883084 : Nat := 4983230072969 + 3 ^ 40 * 1883084 * 2
def baseEnd_1883084 : Nat := 429745424351651403951049

theorem tailTrace_1883084 : CollatzResearch.WordTrace tailWord_1883084 prefixEnd_1883084 429745424351651403951049 := by
  unfold tailWord_1883084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340857954957873994008153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45787810606610498658677537 34340857954957873994008153)
  ·
    refine ⟨25755643466218405495506115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34340857954957873994008153 25755643466218405495506115)
    ·
      refine ⟨38633465199327608243259173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25755643466218405495506115 38633465199327608243259173)
      ·
        refine ⟨7243774724873926545611095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38633465199327608243259173 7243774724873926545611095)
        ·
          refine ⟨10865662087310889818416643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243774724873926545611095 10865662087310889818416643)
          ·
            refine ⟨16298493130966334727624965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10865662087310889818416643 16298493130966334727624965)
            ·
              refine ⟨3055967462056187761429681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16298493130966334727624965 3055967462056187761429681)
              ·
                refine ⟨2291975596542140821072261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055967462056187761429681 2291975596542140821072261)
                ·
                  refine ⟨429745424351651403951049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291975596542140821072261 429745424351651403951049)
                  ·
                    rfl

theorem cell21_1883084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1883084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883084 prefixEnd_1883084 := by exact prefixLift 1883084
  have htrace : WordTrace (prefixWord ++ tailWord_1883084) baseStart_1883084 baseEnd_1883084 := by
    simpa [prefixWord, tailWord_1883084, baseEnd_1883084] using wordTrace_append hprefix tailTrace_1883084
  have hstable : (prefixWord ++ tailWord_1883084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883084).length < 2 ^ (prefixWord ++ tailWord_1883084).sum := by decide
  have hdescent : baseEnd_1883084 < baseStart_1883084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883087 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 3]
def baseStart_1883087 : Nat := 118140960795 + 1883087 * 2 ^ 59
def prefixEnd_1883087 : Nat := 4983230072969 + 3 ^ 40 * 1883087 * 2
def baseEnd_1883087 : Nat := 429746108992524065401043

theorem tailTrace_1883087 : CollatzResearch.WordTrace tailWord_1883087 prefixEnd_1883087 429746108992524065401043 := by
  unfold tailWord_1883087
  simp only [CollatzResearch.WordTrace]
  refine ⟨68681825328904879500375515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45787883552603253000250343 68681825328904879500375515)
  ·
    refine ⟨103022737993357319250563273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68681825328904879500375515 103022737993357319250563273)
    ·
      refine ⟨77267053495017989437922455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103022737993357319250563273 77267053495017989437922455)
      ·
        refine ⟨115900580242526984156883683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77267053495017989437922455 115900580242526984156883683)
        ·
          refine ⟨173850870363790476235325525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115900580242526984156883683 173850870363790476235325525)
          ·
            refine ⟨2037314887075669643382721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 173850870363790476235325525 2037314887075669643382721)
            ·
              refine ⟨1527986165306752232537041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037314887075669643382721 1527986165306752232537041)
              ·
                refine ⟨1145989623980064174402781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527986165306752232537041 1145989623980064174402781)
                ·
                  refine ⟨429746108992524065401043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145989623980064174402781 429746108992524065401043)
                  ·
                    rfl

theorem cell21_1883087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].length) (baseStart_1883087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883087 prefixEnd_1883087 := by exact prefixLift 1883087
  have htrace : WordTrace (prefixWord ++ tailWord_1883087) baseStart_1883087 baseEnd_1883087 := by
    simpa [prefixWord, tailWord_1883087, baseEnd_1883087] using wordTrace_append hprefix tailTrace_1883087
  have hstable : (prefixWord ++ tailWord_1883087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883087).length < 2 ^ (prefixWord ++ tailWord_1883087).sum := by decide
  have hdescent : baseEnd_1883087 < baseStart_1883087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883098 : List Nat := [3, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1883098 : Nat := 118140960795 + 1883098 * 2 ^ 59
def prefixEnd_1883098 : Nat := 4983230072969 + 3 ^ 40 * 1883098 * 2
def baseEnd_1883098 : Nat := 143249539780796830239229

theorem tailTrace_1883098 : CollatzResearch.WordTrace tailWord_1883098 prefixEnd_1883098 143249539780796830239229 := by
  unfold tailWord_1883098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170556632966257094756487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45788151021243352252683965 17170556632966257094756487)
  ·
    refine ⟨25755834949449385642134731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17170556632966257094756487 25755834949449385642134731)
    ·
      refine ⟨38633752424174078463202097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25755834949449385642134731 38633752424174078463202097)
      ·
        refine ⟨28975314318130558847401573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38633752424174078463202097 28975314318130558847401573)
        ·
          refine ⟨5432871434649479783887795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28975314318130558847401573 5432871434649479783887795)
          ·
            refine ⟨8149307151974219675831693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432871434649479783887795 8149307151974219675831693)
            ·
              refine ⟨3055990181990332378436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8149307151974219675831693 3055990181990332378436885)
              ·
                refine ⟨143249539780796830239229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3055990181990332378436885 143249539780796830239229)
                ·
                  rfl

theorem cell21_1883098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1883098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883098 prefixEnd_1883098 := by exact prefixLift 1883098
  have htrace : WordTrace (prefixWord ++ tailWord_1883098) baseStart_1883098 baseEnd_1883098 := by
    simpa [prefixWord, tailWord_1883098, baseEnd_1883098] using wordTrace_append hprefix tailTrace_1883098
  have hstable : (prefixWord ++ tailWord_1883098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883098).length < 2 ^ (prefixWord ++ tailWord_1883098).sum := by decide
  have hdescent : baseEnd_1883098 < baseStart_1883098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883112 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1883112 : Nat := 118140960795 + 1883112 * 2 ^ 59
def prefixEnd_1883112 : Nat := 4983230072969 + 3 ^ 40 * 1883112 * 2
def baseEnd_1883112 : Nat := 429751814333129577484325

theorem tailTrace_1883112 : CollatzResearch.WordTrace tailWord_1883112 prefixEnd_1883112 429751814333129577484325 := by
  unfold tailWord_1883112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34341368576907154385017795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45788491435876205846690393 34341368576907154385017795)
  ·
    refine ⟨51512052865360731577526693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34341368576907154385017795 51512052865360731577526693)
    ·
      refine ⟨9658509912255137170786255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51512052865360731577526693 9658509912255137170786255)
      ·
        refine ⟨14487764868382705756179383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658509912255137170786255 14487764868382705756179383)
        ·
          refine ⟨21731647302574058634269075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487764868382705756179383 21731647302574058634269075)
          ·
            refine ⟨32597470953861087951403613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21731647302574058634269075 32597470953861087951403613)
            ·
              refine ⟨12224051607697907981776355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32597470953861087951403613 12224051607697907981776355)
              ·
                refine ⟨18336077411546861972664533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224051607697907981776355 18336077411546861972664533)
                ·
                  refine ⟨429751814333129577484325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18336077411546861972664533 429751814333129577484325)
                  ·
                    rfl

theorem cell21_1883112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1883112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883112 prefixEnd_1883112 := by exact prefixLift 1883112
  have htrace : WordTrace (prefixWord ++ tailWord_1883112) baseStart_1883112 baseEnd_1883112 := by
    simpa [prefixWord, tailWord_1883112, baseEnd_1883112] using wordTrace_append hprefix tailTrace_1883112
  have hstable : (prefixWord ++ tailWord_1883112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883112).length < 2 ^ (prefixWord ++ tailWord_1883112).sum := by decide
  have hdescent : baseEnd_1883112 < baseStart_1883112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883143 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_1883143 : Nat := 118140960795 + 1883143 * 2 ^ 59
def prefixEnd_1883143 : Nat := 4983230072969 + 3 ^ 40 * 1883143 * 2
def baseEnd_1883143 : Nat := 429758888955480412467595

theorem tailTrace_1883143 : CollatzResearch.WordTrace tailWord_1883143 prefixEnd_1883143 429758888955480412467595 := by
  unfold tailWord_1883143
  simp only [CollatzResearch.WordTrace]
  refine ⟨68683867816702001064414083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45789245211134667376276055 68683867816702001064414083)
  ·
    refine ⟨103025801725053001596621125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68683867816702001064414083 103025801725053001596621125)
    ·
      refine ⟨19317337823447437799366461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103025801725053001596621125 19317337823447437799366461)
      ·
        refine ⟨7244001683792789174762423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19317337823447437799366461 7244001683792789174762423)
        ·
          refine ⟨10866002525689183762143635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244001683792789174762423 10866002525689183762143635)
          ·
            refine ⟨16299003788533775643215453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866002525689183762143635 16299003788533775643215453)
            ·
              refine ⟨6112126420700165866205795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16299003788533775643215453 6112126420700165866205795)
              ·
                refine ⟨9168189631050248799308693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112126420700165866205795 9168189631050248799308693)
                ·
                  refine ⟨429758888955480412467595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9168189631050248799308693 429758888955480412467595)
                  ·
                    rfl

theorem cell21_1883143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_1883143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883143 prefixEnd_1883143 := by exact prefixLift 1883143
  have htrace : WordTrace (prefixWord ++ tailWord_1883143) baseStart_1883143 baseEnd_1883143 := by
    simpa [prefixWord, tailWord_1883143, baseEnd_1883143] using wordTrace_append hprefix tailTrace_1883143
  have hstable : (prefixWord ++ tailWord_1883143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883143).length < 2 ^ (prefixWord ++ tailWord_1883143).sum := by decide
  have hdescent : baseEnd_1883143 < baseStart_1883143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883146 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1883146 : Nat := 118140960795 + 1883146 * 2 ^ 59
def prefixEnd_1883146 : Nat := 4983230072969 + 3 ^ 40 * 1883146 * 2
def baseEnd_1883146 : Nat := 429759573596353073917589

theorem tailTrace_1883146 : CollatzResearch.WordTrace tailWord_1883146 prefixEnd_1883146 429759573596353073917589 := by
  unfold tailWord_1883146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170994308922783144193323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45789318157127421717848861 17170994308922783144193323)
  ·
    refine ⟨25756491463384174716289985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17170994308922783144193323 25756491463384174716289985)
    ·
      refine ⟨19317368597538131037217489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25756491463384174716289985 19317368597538131037217489)
      ·
        refine ⟨14488026448153598277913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19317368597538131037217489 14488026448153598277913117)
        ·
          refine ⟨5433009918057599354217419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14488026448153598277913117 5433009918057599354217419)
          ·
            refine ⟨8149514877086399031326129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433009918057599354217419 8149514877086399031326129)
            ·
              refine ⟨6112136157814799273494597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149514877086399031326129 6112136157814799273494597)
              ·
                refine ⟨1146025529590274863780237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112136157814799273494597 1146025529590274863780237)
                ·
                  refine ⟨429759573596353073917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146025529590274863780237 429759573596353073917589)
                  ·
                    rfl

theorem cell21_1883146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1883146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883146 prefixEnd_1883146 := by exact prefixLift 1883146
  have htrace : WordTrace (prefixWord ++ tailWord_1883146) baseStart_1883146 baseEnd_1883146 := by
    simpa [prefixWord, tailWord_1883146, baseEnd_1883146] using wordTrace_append hprefix tailTrace_1883146
  have hstable : (prefixWord ++ tailWord_1883146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883146).length < 2 ^ (prefixWord ++ tailWord_1883146).sum := by decide
  have hdescent : baseEnd_1883146 < baseStart_1883146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883205 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 3]
def baseStart_1883205 : Nat := 118140960795 + 1883205 * 2 ^ 59
def prefixEnd_1883205 : Nat := 4983230072969 + 3 ^ 40 * 1883205 * 2
def baseEnd_1883205 : Nat := 429773038200182082434135

theorem tailTrace_1883205 : CollatzResearch.WordTrace tailWord_1883205 prefixEnd_1883205 429773038200182082434135 := by
  unfold tailWord_1883205
  simp only [CollatzResearch.WordTrace]
  refine ⟨68686129142477385653171069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45790752761651590435447379 68686129142477385653171069)
  ·
    refine ⟨25757298428429019619939151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68686129142477385653171069 25757298428429019619939151)
    ·
      refine ⟨38635947642643529429908727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25757298428429019619939151 38635947642643529429908727)
      ·
        refine ⟨57953921463965294144863091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38635947642643529429908727 57953921463965294144863091)
        ·
          refine ⟨86930882195947941217294637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57953921463965294144863091 86930882195947941217294637)
          ·
            refine ⟨32599080823480477956485489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86930882195947941217294637 32599080823480477956485489)
            ·
              refine ⟨24449310617610358467364117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32599080823480477956485489 24449310617610358467364117)
              ·
                refine ⟨1146061435200485553157693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24449310617610358467364117 1146061435200485553157693)
                ·
                  refine ⟨429773038200182082434135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146061435200485553157693 429773038200182082434135)
                  ·
                    rfl

theorem cell21_1883205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_1883205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883205 prefixEnd_1883205 := by exact prefixLift 1883205
  have htrace : WordTrace (prefixWord ++ tailWord_1883205) baseStart_1883205 baseEnd_1883205 := by
    simpa [prefixWord, tailWord_1883205, baseEnd_1883205] using wordTrace_append hprefix tailTrace_1883205
  have hstable : (prefixWord ++ tailWord_1883205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883205).length < 2 ^ (prefixWord ++ tailWord_1883205).sum := by decide
  have hdescent : baseEnd_1883205 < baseStart_1883205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883233 : List Nat := [1, 2, 3, 1, 1, 2, 4, 7]
def baseStart_1883233 : Nat := 118140960795 + 1883233 * 2 ^ 59
def prefixEnd_1883233 : Nat := 4983230072969 + 3 ^ 40 * 1883233 * 2
def baseEnd_1883233 : Nat := 143259809393886751989137

theorem tailTrace_1883233 : CollatzResearch.WordTrace tailWord_1883233 prefixEnd_1883233 143259809393886751989137 := by
  unfold tailWord_1883233
  simp only [CollatzResearch.WordTrace]
  refine ⟨68687150386375946435190353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45791433590917297623460235 68687150386375946435190353)
  ·
    refine ⟨51515362789781959826392765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68687150386375946435190353 51515362789781959826392765)
    ·
      refine ⟨19318261046168234934897287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51515362789781959826392765 19318261046168234934897287)
      ·
        refine ⟨28977391569252352402345931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318261046168234934897287 28977391569252352402345931)
        ·
          refine ⟨43466087353878528603518897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28977391569252352402345931 43466087353878528603518897)
          ·
            refine ⟨32599565515408896452639173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43466087353878528603518897 32599565515408896452639173)
            ·
              refine ⟨6112418534139168084869845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32599565515408896452639173 6112418534139168084869845)
              ·
                refine ⟨143259809393886751989137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6112418534139168084869845 143259809393886751989137)
                ·
                  rfl

theorem cell21_1883233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_1883233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883233 prefixEnd_1883233 := by exact prefixLift 1883233
  have htrace : WordTrace (prefixWord ++ tailWord_1883233) baseStart_1883233 baseEnd_1883233 := by
    simpa [prefixWord, tailWord_1883233, baseEnd_1883233] using wordTrace_append hprefix tailTrace_1883233
  have hstable : (prefixWord ++ tailWord_1883233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883233).length < 2 ^ (prefixWord ++ tailWord_1883233).sum := by decide
  have hdescent : baseEnd_1883233 < baseStart_1883233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883380 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1883380 : Nat := 118140960795 + 1883380 * 2 ^ 59
def prefixEnd_1883380 : Nat := 4983230072969 + 3 ^ 40 * 1883380 * 2
def baseEnd_1883380 : Nat := 429812975584420667017111

theorem tailTrace_1883380 : CollatzResearch.WordTrace tailWord_1883380 prefixEnd_1883380 429812975584420667017111 := by
  unfold tailWord_1883380
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346255958421695270395797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45795007944562260360527729 34346255958421695270395797)
  ·
    refine ⟨1609980748051016965799803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34346255958421695270395797 1609980748051016965799803)
    ·
      refine ⟨2414971122076525448699705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609980748051016965799803 2414971122076525448699705)
      ·
        refine ⟨1811228341557394086524779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2414971122076525448699705 1811228341557394086524779)
        ·
          refine ⟨2716842512336091129787169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811228341557394086524779 2716842512336091129787169)
          ·
            refine ⟨2037631884252068347340377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716842512336091129787169 2037631884252068347340377)
            ·
              refine ⟨1528223913189051260505283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037631884252068347340377 1528223913189051260505283)
              ·
                refine ⟨2292335869783576890757925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528223913189051260505283 2292335869783576890757925)
                ·
                  refine ⟨429812975584420667017111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292335869783576890757925 429812975584420667017111)
                  ·
                    rfl

theorem cell21_1883380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1883380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883380 prefixEnd_1883380 := by exact prefixLift 1883380
  have htrace : WordTrace (prefixWord ++ tailWord_1883380) baseStart_1883380 baseEnd_1883380 := by
    simpa [prefixWord, tailWord_1883380, baseEnd_1883380] using wordTrace_append hprefix tailTrace_1883380
  have hstable : (prefixWord ++ tailWord_1883380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883380).length < 2 ^ (prefixWord ++ tailWord_1883380).sum := by decide
  have hdescent : baseEnd_1883380 < baseStart_1883380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883385 : List Nat := [1, 2, 1, 3, 1, 1, 6, 6]
def baseStart_1883385 : Nat := 118140960795 + 1883385 * 2 ^ 59
def prefixEnd_1883385 : Nat := 4983230072969 + 3 ^ 40 * 1883385 * 2
def baseEnd_1883385 : Nat := 143271372217513923144589

theorem tailTrace_1883385 : CollatzResearch.WordTrace tailWord_1883385 prefixEnd_1883385 143271372217513923144589 := by
  unfold tailWord_1883385
  simp only [CollatzResearch.WordTrace]
  refine ⟨68692694281825276394723609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45795129521216850929815739 68692694281825276394723609)
  ·
    refine ⟨51519520711368957296042707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68692694281825276394723609 51519520711368957296042707)
    ·
      refine ⟨77279281067053435944064061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51519520711368957296042707 77279281067053435944064061)
      ·
        refine ⟨28979730400145038479024023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77279281067053435944064061 28979730400145038479024023)
        ·
          refine ⟨43469595600217557718536035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28979730400145038479024023 43469595600217557718536035)
          ·
            refine ⟨65204393400326336577804053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43469595600217557718536035 65204393400326336577804053)
            ·
              refine ⟨3056455940640297027084565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65204393400326336577804053 3056455940640297027084565)
              ·
                refine ⟨143271372217513923144589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3056455940640297027084565 143271372217513923144589)
                ·
                  rfl

theorem cell21_1883385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_1883385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883385 prefixEnd_1883385 := by exact prefixLift 1883385
  have htrace : WordTrace (prefixWord ++ tailWord_1883385) baseStart_1883385 baseEnd_1883385 := by
    simpa [prefixWord, tailWord_1883385, baseEnd_1883385] using wordTrace_append hprefix tailTrace_1883385
  have hstable : (prefixWord ++ tailWord_1883385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883385).length < 2 ^ (prefixWord ++ tailWord_1883385).sum := by decide
  have hdescent : baseEnd_1883385 < baseStart_1883385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883388 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1883388 : Nat := 118140960795 + 1883388 * 2 ^ 59
def prefixEnd_1883388 : Nat := 4983230072969 + 3 ^ 40 * 1883388 * 2
def baseEnd_1883388 : Nat := 429814801293414430883761

theorem tailTrace_1883388 : CollatzResearch.WordTrace tailWord_1883388 prefixEnd_1883388 429814801293414430883761 := by
  unfold tailWord_1883388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346401850407203953541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45795202467209605271388545 34346401850407203953541409)
  ·
    refine ⟨25759801387805402965156057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34346401850407203953541409 25759801387805402965156057)
    ·
      refine ⟨19319851040854052223867043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25759801387805402965156057 19319851040854052223867043)
      ·
        refine ⟨28979776561281078335800565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19319851040854052223867043 28979776561281078335800565)
        ·
          refine ⟨2716854052620101093981303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28979776561281078335800565 2716854052620101093981303)
          ·
            refine ⟨4075281078930151640971955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716854052620101093981303 4075281078930151640971955)
            ·
              refine ⟨6112921618395227461457933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075281078930151640971955 6112921618395227461457933)
              ·
                refine ⟨2292345606898210298046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6112921618395227461457933 2292345606898210298046725)
                ·
                  refine ⟨429814801293414430883761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292345606898210298046725 429814801293414430883761)
                  ·
                    rfl

theorem cell21_1883388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1883388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883388 prefixEnd_1883388 := by exact prefixLift 1883388
  have htrace : WordTrace (prefixWord ++ tailWord_1883388) baseStart_1883388 baseEnd_1883388 := by
    simpa [prefixWord, tailWord_1883388, baseEnd_1883388] using wordTrace_append hprefix tailTrace_1883388
  have hstable : (prefixWord ++ tailWord_1883388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883388).length < 2 ^ (prefixWord ++ tailWord_1883388).sum := by decide
  have hdescent : baseEnd_1883388 < baseStart_1883388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883422 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1883422 : Nat := 118140960795 + 1883422 * 2 ^ 59
def prefixEnd_1883422 : Nat := 4983230072969 + 3 ^ 40 * 1883422 * 2
def baseEnd_1883422 : Nat := 429822560556637927317025

theorem tailTrace_1883422 : CollatzResearch.WordTrace tailWord_1883422 prefixEnd_1883422 429822560556637927317025 := by
  unfold tailWord_1883422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586755472836403964227565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45796029188460821142547013 8586755472836403964227565)
  ·
    refine ⟨3220033302313651486585337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8586755472836403964227565 3220033302313651486585337)
    ·
      refine ⟨2415024976735238614939003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220033302313651486585337 2415024976735238614939003)
      ·
        refine ⟨3622537465102857922408505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415024976735238614939003 3622537465102857922408505)
        ·
          refine ⟨2716903098827143441806379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3622537465102857922408505 2716903098827143441806379)
          ·
            refine ⟨4075354648240715162709569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716903098827143441806379 4075354648240715162709569)
            ·
              refine ⟨3056515986180536372032177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075354648240715162709569 3056515986180536372032177)
              ·
                refine ⟨2292386989635402279024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056515986180536372032177 2292386989635402279024133)
                ·
                  refine ⟨429822560556637927317025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292386989635402279024133 429822560556637927317025)
                  ·
                    rfl

theorem cell21_1883422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1883422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883422 prefixEnd_1883422 := by exact prefixLift 1883422
  have htrace : WordTrace (prefixWord ++ tailWord_1883422) baseStart_1883422 baseEnd_1883422 := by
    simpa [prefixWord, tailWord_1883422, baseEnd_1883422] using wordTrace_append hprefix tailTrace_1883422
  have hstable : (prefixWord ++ tailWord_1883422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883422).length < 2 ^ (prefixWord ++ tailWord_1883422).sum := by decide
  have hdescent : baseEnd_1883422 < baseStart_1883422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883475 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_1883475 : Nat := 118140960795 + 1883475 * 2 ^ 59
def prefixEnd_1883475 : Nat := 4983230072969 + 3 ^ 40 * 1883475 * 2
def baseEnd_1883475 : Nat := 429834655878721612933583

theorem tailTrace_1883475 : CollatzResearch.WordTrace tailWord_1883475 prefixEnd_1883475 429834655878721612933583 := by
  unfold tailWord_1883475
  simp only [CollatzResearch.WordTrace]
  refine ⟨68695976851499221765499879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45797317900999481176999919 68695976851499221765499879)
  ·
    refine ⟨103043965277248832648249819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68695976851499221765499879 103043965277248832648249819)
    ·
      refine ⟨154565947915873248972374729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103043965277248832648249819 154565947915873248972374729)
      ·
        refine ⟨115924460936904936729281047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154565947915873248972374729 115924460936904936729281047)
        ·
          refine ⟨173886691405357405093921571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115924460936904936729281047 173886691405357405093921571)
          ·
            refine ⟨260830037108036107640882357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173886691405357405093921571 260830037108036107640882357)
            ·
              refine ⟨24452815978878385091332721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260830037108036107640882357 24452815978878385091332721)
              ·
                refine ⟨18339611984158788818499541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24452815978878385091332721 18339611984158788818499541)
                ·
                  refine ⟨429834655878721612933583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18339611984158788818499541 429834655878721612933583)
                  ·
                    rfl

theorem cell21_1883475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_1883475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883475 prefixEnd_1883475 := by exact prefixLift 1883475
  have htrace : WordTrace (prefixWord ++ tailWord_1883475) baseStart_1883475 baseEnd_1883475 := by
    simpa [prefixWord, tailWord_1883475, baseEnd_1883475] using wordTrace_append hprefix tailTrace_1883475
  have hstable : (prefixWord ++ tailWord_1883475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883475).length < 2 ^ (prefixWord ++ tailWord_1883475).sum := by decide
  have hdescent : baseEnd_1883475 < baseStart_1883475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883492 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1883492 : Nat := 118140960795 + 1883492 * 2 ^ 59
def prefixEnd_1883492 : Nat := 4983230072969 + 3 ^ 40 * 1883492 * 2
def baseEnd_1883492 : Nat := 429838535510333361150215

theorem tailTrace_1883492 : CollatzResearch.WordTrace tailWord_1883492 prefixEnd_1883492 429838535510333361150215 := by
  unfold tailWord_1883492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348298446218816834434365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45797731261625089112579153 34348298446218816834434365)
  ·
    refine ⟨12880611917332056312912887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34348298446218816834434365 12880611917332056312912887)
    ·
      refine ⟨19320917875998084469369331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12880611917332056312912887 19320917875998084469369331)
      ·
        refine ⟨28981376813997126704053997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19320917875998084469369331 28981376813997126704053997)
        ·
          refine ⟨10868016305248922514020249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28981376813997126704053997 10868016305248922514020249)
          ·
            refine ⟨8151012228936691885515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10868016305248922514020249 8151012228936691885515187)
            ·
              refine ⟨12226518343405037828272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151012228936691885515187 12226518343405037828272781)
              ·
                refine ⟨4584944378776889185602293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12226518343405037828272781 4584944378776889185602293)
                ·
                  refine ⟨429838535510333361150215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4584944378776889185602293 429838535510333361150215)
                  ·
                    rfl

theorem cell21_1883492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1883492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883492 prefixEnd_1883492 := by exact prefixLift 1883492
  have htrace : WordTrace (prefixWord ++ tailWord_1883492) baseStart_1883492 baseEnd_1883492 := by
    simpa [prefixWord, tailWord_1883492, baseEnd_1883492] using wordTrace_append hprefix tailTrace_1883492
  have hstable : (prefixWord ++ tailWord_1883492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883492).length < 2 ^ (prefixWord ++ tailWord_1883492).sum := by decide
  have hdescent : baseEnd_1883492 < baseStart_1883492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883554 : List Nat := [3, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1883554 : Nat := 118140960795 + 1883554 * 2 ^ 59
def prefixEnd_1883554 : Nat := 4983230072969 + 3 ^ 40 * 1883554 * 2
def baseEnd_1883554 : Nat := 143284228251678343705585

theorem tailTrace_1883554 : CollatzResearch.WordTrace tailWord_1883554 prefixEnd_1883554 143284228251678343705585 := by
  unfold tailWord_1883554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17174714554553254564406429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45799238812142012171750477 17174714554553254564406429)
  ·
    refine ⟨6440517957957470461652411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17174714554553254564406429 6440517957957470461652411)
    ·
      refine ⟨9660776936936205692478617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440517957957470461652411 9660776936936205692478617)
      ·
        refine ⟨7245582702702154269358963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9660776936936205692478617 7245582702702154269358963)
        ·
          refine ⟨10868374054053231404038445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7245582702702154269358963 10868374054053231404038445)
          ·
            refine ⟨4075640270269961776514417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10868374054053231404038445 4075640270269961776514417)
            ·
              refine ⟨3056730202702471332385813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075640270269961776514417 3056730202702471332385813)
              ·
                refine ⟨143284228251678343705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3056730202702471332385813 143284228251678343705585)
                ·
                  rfl

theorem cell21_1883554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1883554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883554 prefixEnd_1883554 := by exact prefixLift 1883554
  have htrace : WordTrace (prefixWord ++ tailWord_1883554) baseStart_1883554 baseEnd_1883554 := by
    simpa [prefixWord, tailWord_1883554, baseEnd_1883554] using wordTrace_append hprefix tailTrace_1883554
  have hstable : (prefixWord ++ tailWord_1883554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883554).length < 2 ^ (prefixWord ++ tailWord_1883554).sum := by decide
  have hdescent : baseEnd_1883554 < baseStart_1883554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883630 : List Nat := [4, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1883630 : Nat := 118140960795 + 1883630 * 2 ^ 59
def prefixEnd_1883630 : Nat := 4983230072969 + 3 ^ 40 * 1883630 * 2
def baseEnd_1883630 : Nat := 143290009663491929283311

theorem tailTrace_1883630 : CollatzResearch.WordTrace tailWord_1883630 prefixEnd_1883630 143290009663491929283311 := by
  unfold tailWord_1883630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587703770742210404674043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45801086777291788824928229 8587703770742210404674043)
  ·
    refine ⟨12881555656113315607011065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587703770742210404674043 12881555656113315607011065)
    ·
      refine ⟨9661166742084986705258299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12881555656113315607011065 9661166742084986705258299)
      ·
        refine ⟨14491750113127480057887449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9661166742084986705258299 14491750113127480057887449)
        ·
          refine ⟨10868812584845610043415587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14491750113127480057887449 10868812584845610043415587)
          ·
            refine ⟨16303218877268415065123381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868812584845610043415587 16303218877268415065123381)
            ·
              refine ⟨1528426769743913912355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16303218877268415065123381 1528426769743913912355317)
              ·
                refine ⟨143290009663491929283311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528426769743913912355317 143290009663491929283311)
                ·
                  rfl

theorem cell21_1883630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1883630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883630 prefixEnd_1883630 := by exact prefixLift 1883630
  have htrace : WordTrace (prefixWord ++ tailWord_1883630) baseStart_1883630 baseEnd_1883630 := by
    simpa [prefixWord, tailWord_1883630, baseEnd_1883630] using wordTrace_append hprefix tailTrace_1883630
  have hstable : (prefixWord ++ tailWord_1883630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883630).length < 2 ^ (prefixWord ++ tailWord_1883630).sum := by decide
  have hdescent : baseEnd_1883630 < baseStart_1883630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883765 : List Nat := [1, 3, 4, 2, 1, 10]
def baseStart_1883765 : Nat := 118140960795 + 1883765 * 2 ^ 59
def prefixEnd_1883765 : Nat := 4983230072969 + 3 ^ 40 * 1883765 * 2
def baseEnd_1883765 : Nat := 15922253252953539003691

theorem tailTrace_1883765 : CollatzResearch.WordTrace tailWord_1883765 prefixEnd_1883765 15922253252953539003691 := by
  unfold tailWord_1883765
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706554020448601293556749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45804369346965734195704499 68706554020448601293556749)
  ·
    refine ⟨25764957757668225485083781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68706554020448601293556749 25764957757668225485083781)
    ·
      refine ⟨4830929579562792278453209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25764957757668225485083781 4830929579562792278453209)
      ·
        refine ⟨3623197184672094208839907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830929579562792278453209 3623197184672094208839907)
        ·
          refine ⟨5434795777008141313259861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623197184672094208839907 5434795777008141313259861)
          ·
            refine ⟨15922253252953539003691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5434795777008141313259861 15922253252953539003691)
            ·
              rfl

theorem cell21_1883765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 10].length) (baseStart_1883765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883765 prefixEnd_1883765 := by exact prefixLift 1883765
  have htrace : WordTrace (prefixWord ++ tailWord_1883765) baseStart_1883765 baseEnd_1883765 := by
    simpa [prefixWord, tailWord_1883765, baseEnd_1883765] using wordTrace_append hprefix tailTrace_1883765
  have hstable : (prefixWord ++ tailWord_1883765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883765).length < 2 ^ (prefixWord ++ tailWord_1883765).sum := by decide
  have hdescent : baseEnd_1883765 < baseStart_1883765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883779 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_1883779 : Nat := 118140960795 + 1883779 * 2 ^ 59
def prefixEnd_1883779 : Nat := 4983230072969 + 3 ^ 40 * 1883779 * 2
def baseEnd_1883779 : Nat := 429904032820484639866295

theorem tailTrace_1883779 : CollatzResearch.WordTrace tailWord_1883779 prefixEnd_1883779 429904032820484639866295 := by
  unfold tailWord_1883779
  simp only [CollatzResearch.WordTrace]
  refine ⟨68707064642397881684566391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45804709761598587789710927 68707064642397881684566391)
  ·
    refine ⟨103060596963596822526849587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68707064642397881684566391 103060596963596822526849587)
    ·
      refine ⟨154590895445395233790274381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103060596963596822526849587 154590895445395233790274381)
      ·
        refine ⟨57971585792023212671352893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154590895445395233790274381 57971585792023212671352893)
        ·
          refine ⟨21739344672008704751757335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57971585792023212671352893 21739344672008704751757335)
          ·
            refine ⟨32609017008013057127636003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739344672008704751757335 32609017008013057127636003)
            ·
              refine ⟨48913525512019585691454005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32609017008013057127636003 48913525512019585691454005)
              ·
                refine ⟨4585643016751836158573813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48913525512019585691454005 4585643016751836158573813)
                ·
                  refine ⟨429904032820484639866295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585643016751836158573813 429904032820484639866295)
                  ·
                    rfl

theorem cell21_1883779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_1883779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883779 prefixEnd_1883779 := by exact prefixLift 1883779
  have htrace : WordTrace (prefixWord ++ tailWord_1883779) baseStart_1883779 baseEnd_1883779 := by
    simpa [prefixWord, tailWord_1883779, baseEnd_1883779] using wordTrace_append hprefix tailTrace_1883779
  have hstable : (prefixWord ++ tailWord_1883779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883779).length < 2 ^ (prefixWord ++ tailWord_1883779).sum := by decide
  have hdescent : baseEnd_1883779 < baseStart_1883779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883830 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1883830 : Nat := 118140960795 + 1883830 * 2 ^ 59
def prefixEnd_1883830 : Nat := 4983230072969 + 3 ^ 40 * 1883830 * 2
def baseEnd_1883830 : Nat := 429915671715319884516191

theorem tailTrace_1883830 : CollatzResearch.WordTrace tailWord_1883830 prefixEnd_1883830 429915671715319884516191 := by
  unfold tailWord_1883830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294307797825819837167059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45805949843475411596448629 4294307797825819837167059)
  ·
    refine ⟨6441461696738729755750589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294307797825819837167059 6441461696738729755750589)
    ·
      refine ⟨2415548136277023658406471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6441461696738729755750589 2415548136277023658406471)
      ·
        refine ⟨3623322204415535487609707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415548136277023658406471 3623322204415535487609707)
        ·
          refine ⟨5434983306623303231414561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623322204415535487609707 5434983306623303231414561)
          ·
            refine ⟨4076237479967477423560921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434983306623303231414561 4076237479967477423560921)
            ·
              refine ⟨3057178109975608067670691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076237479967477423560921 3057178109975608067670691)
              ·
                refine ⟨4585767164963412101506037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057178109975608067670691 4585767164963412101506037)
                ·
                  refine ⟨429915671715319884516191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585767164963412101506037 429915671715319884516191)
                  ·
                    rfl

theorem cell21_1883830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1883830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883830 prefixEnd_1883830 := by exact prefixLift 1883830
  have htrace : WordTrace (prefixWord ++ tailWord_1883830) baseStart_1883830 baseEnd_1883830 := by
    simpa [prefixWord, tailWord_1883830, baseEnd_1883830] using wordTrace_append hprefix tailTrace_1883830
  have hstable : (prefixWord ++ tailWord_1883830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883830).length < 2 ^ (prefixWord ++ tailWord_1883830).sum := by decide
  have hdescent : baseEnd_1883830 < baseStart_1883830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883844 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1883844 : Nat := 118140960795 + 1883844 * 2 ^ 59
def prefixEnd_1883844 : Nat := 4983230072969 + 3 ^ 40 * 1883844 * 2
def baseEnd_1883844 : Nat := 429918866706058971282829

theorem tailTrace_1883844 : CollatzResearch.WordTrace tailWord_1883844 prefixEnd_1883844 429918866706058971282829 := by
  unfold tailWord_1883844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34354717693581198892841293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45806290258108265190455057 34354717693581198892841293)
  ·
    refine ⟨12883019135092949584815485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34354717693581198892841293 12883019135092949584815485)
    ·
      refine ⟨4831132175659856094305807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12883019135092949584815485 4831132175659856094305807)
      ·
        refine ⟨7246698263489784141458711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831132175659856094305807 7246698263489784141458711)
        ·
          refine ⟨10870047395234676212188067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246698263489784141458711 10870047395234676212188067)
          ·
            refine ⟨16305071092852014318282101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870047395234676212188067 16305071092852014318282101)
            ·
              refine ⟨1528600414954876342338947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16305071092852014318282101 1528600414954876342338947)
              ·
                refine ⟨2292900622432314513508421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528600414954876342338947 2292900622432314513508421)
                ·
                  refine ⟨429918866706058971282829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292900622432314513508421 429918866706058971282829)
                  ·
                    rfl

theorem cell21_1883844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1883844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883844 prefixEnd_1883844 := by exact prefixLift 1883844
  have htrace : WordTrace (prefixWord ++ tailWord_1883844) baseStart_1883844 baseEnd_1883844 := by
    simpa [prefixWord, tailWord_1883844, baseEnd_1883844] using wordTrace_append hprefix tailTrace_1883844
  have hstable : (prefixWord ++ tailWord_1883844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883844).length < 2 ^ (prefixWord ++ tailWord_1883844).sum := by decide
  have hdescent : baseEnd_1883844 < baseStart_1883844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883858 : List Nat := [3, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1883858 : Nat := 118140960795 + 1883858 * 2 ^ 59
def prefixEnd_1883858 : Nat := 4983230072969 + 3 ^ 40 * 1883858 * 2
def baseEnd_1883858 : Nat := 143307353898932686016489

theorem tailTrace_1883858 : CollatzResearch.WordTrace tailWord_1883858 prefixEnd_1883858 143307353898932686016489 := by
  unfold tailWord_1883858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177486502277919544173057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45806630672741118784461485 17177486502277919544173057)
  ·
    refine ⟨12883114876708439658129793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17177486502277919544173057 12883114876708439658129793)
    ·
      refine ⟨9662336157531329743597345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12883114876708439658129793 9662336157531329743597345)
      ·
        refine ⟨7246752118148497307698009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9662336157531329743597345 7246752118148497307698009)
        ·
          refine ⟨5435064088611372980773507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7246752118148497307698009 5435064088611372980773507)
          ·
            refine ⟨8152596132917059471160261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435064088611372980773507 8152596132917059471160261)
            ·
              refine ⟨1528611774921948650842549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8152596132917059471160261 1528611774921948650842549)
              ·
                refine ⟨143307353898932686016489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528611774921948650842549 143307353898932686016489)
                ·
                  rfl

theorem cell21_1883858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1883858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883858 prefixEnd_1883858 := by exact prefixLift 1883858
  have htrace : WordTrace (prefixWord ++ tailWord_1883858) baseStart_1883858 baseEnd_1883858 := by
    simpa [prefixWord, tailWord_1883858, baseEnd_1883858] using wordTrace_append hprefix tailTrace_1883858
  have hstable : (prefixWord ++ tailWord_1883858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883858).length < 2 ^ (prefixWord ++ tailWord_1883858).sum := by decide
  have hdescent : baseEnd_1883858 < baseStart_1883858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883886 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1883886 : Nat := 118140960795 + 1883886 * 2 ^ 59
def prefixEnd_1883886 : Nat := 4983230072969 + 3 ^ 40 * 1883886 * 2
def baseEnd_1883886 : Nat := 429928451678276231582743

theorem tailTrace_1883886 : CollatzResearch.WordTrace tailWord_1883886 prefixEnd_1883886 429928451678276231582743 := by
  unfold tailWord_1883886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588870906626279869838939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45807311502006825972474341 8588870906626279869838939)
  ·
    refine ⟨12883306359939419804758409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588870906626279869838939 12883306359939419804758409)
    ·
      refine ⟨9662479769954564853568807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12883306359939419804758409 9662479769954564853568807)
      ·
        refine ⟨14493719654931847280353211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662479769954564853568807 14493719654931847280353211)
        ·
          refine ⟨21740579482397770920529817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493719654931847280353211 21740579482397770920529817)
          ·
            refine ⟨16305434611798328190397363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21740579482397770920529817 16305434611798328190397363)
            ·
              refine ⟨24458151917697492285596045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305434611798328190397363 24458151917697492285596045)
              ·
                refine ⟨9171806969136559607098517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24458151917697492285596045 9171806969136559607098517)
                ·
                  refine ⟨429928451678276231582743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9171806969136559607098517 429928451678276231582743)
                  ·
                    rfl

theorem cell21_1883886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1883886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883886 prefixEnd_1883886 := by exact prefixLift 1883886
  have htrace : WordTrace (prefixWord ++ tailWord_1883886) baseStart_1883886 baseEnd_1883886 := by
    simpa [prefixWord, tailWord_1883886, baseEnd_1883886] using wordTrace_append hprefix tailTrace_1883886
  have hstable : (prefixWord ++ tailWord_1883886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883886).length < 2 ^ (prefixWord ++ tailWord_1883886).sum := by decide
  have hdescent : baseEnd_1883886 < baseStart_1883886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883903 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 4]
def baseStart_1883903 : Nat := 118140960795 + 1883903 * 2 ^ 59
def prefixEnd_1883903 : Nat := 4983230072969 + 3 ^ 40 * 1883903 * 2
def baseEnd_1883903 : Nat := 429932331309887979799375

theorem tailTrace_1883903 : CollatzResearch.WordTrace tailWord_1883903 prefixEnd_1883903 429932331309887979799375 := by
  unfold tailWord_1883903
  simp only [CollatzResearch.WordTrace]
  refine ⟨68711587293948650862080363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45807724862632433908053575 68711587293948650862080363)
  ·
    refine ⟨103067380940922976293120545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68711587293948650862080363 103067380940922976293120545)
    ·
      refine ⟨77300535705692232219840409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103067380940922976293120545 77300535705692232219840409)
      ·
        refine ⟨57975401779269174164880307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77300535705692232219840409 57975401779269174164880307)
        ·
          refine ⟨86963102668903761247320461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57975401779269174164880307 86963102668903761247320461)
          ·
            refine ⟨32611163500838910467745173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86963102668903761247320461 32611163500838910467745173)
            ·
              refine ⟨1528648289101823928175555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32611163500838910467745173 1528648289101823928175555)
              ·
                refine ⟨2292972433652735892263333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528648289101823928175555 2292972433652735892263333)
                ·
                  refine ⟨429932331309887979799375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292972433652735892263333 429932331309887979799375)
                  ·
                    rfl

theorem cell21_1883903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_1883903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883903 prefixEnd_1883903 := by exact prefixLift 1883903
  have htrace : WordTrace (prefixWord ++ tailWord_1883903) baseStart_1883903 baseEnd_1883903 := by
    simpa [prefixWord, tailWord_1883903, baseEnd_1883903] using wordTrace_append hprefix tailTrace_1883903
  have hstable : (prefixWord ++ tailWord_1883903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883903).length < 2 ^ (prefixWord ++ tailWord_1883903).sum := by decide
  have hdescent : baseEnd_1883903 < baseStart_1883903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883934 : List Nat := [4, 3, 2, 2, 10]
def baseStart_1883934 : Nat := 118140960795 + 1883934 * 2 ^ 59
def prefixEnd_1883934 : Nat := 4983230072969 + 3 ^ 40 * 1883934 * 2
def baseEnd_1883934 : Nat := 5307893900398010059045

theorem tailTrace_1883934 : CollatzResearch.WordTrace tailWord_1883934 prefixEnd_1883934 5307893900398010059045 := by
  unfold tailWord_1883934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8589089744604542894557357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45808478637890895437639237 8589089744604542894557357)
  ·
    refine ⟨3220908654226703585459009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8589089744604542894557357 3220908654226703585459009)
    ·
      refine ⟨2415681490670027689094257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220908654226703585459009 2415681490670027689094257)
      ·
        refine ⟨1811761118002520766820693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415681490670027689094257 1811761118002520766820693)
        ·
          refine ⟨5307893900398010059045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1811761118002520766820693 5307893900398010059045)
          ·
            rfl

theorem cell21_1883934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 10].length) (baseStart_1883934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1883934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1883934 prefixEnd_1883934 := by exact prefixLift 1883934
  have htrace : WordTrace (prefixWord ++ tailWord_1883934) baseStart_1883934 baseEnd_1883934 := by
    simpa [prefixWord, tailWord_1883934, baseEnd_1883934] using wordTrace_append hprefix tailTrace_1883934
  have hstable : (prefixWord ++ tailWord_1883934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883934).length < 2 ^ (prefixWord ++ tailWord_1883934).sum := by decide
  have hdescent : baseEnd_1883934 < baseStart_1883934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884058 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_1884058 : Nat := 118140960795 + 1884058 * 2 ^ 59
def prefixEnd_1884058 : Nat := 4983230072969 + 3 ^ 40 * 1884058 * 2
def baseEnd_1884058 : Nat := 429967704421642154715725

theorem tailTrace_1884058 : CollatzResearch.WordTrace tailWord_1884058 prefixEnd_1884058 429967704421642154715725 := by
  unfold tailWord_1884058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179310152096778083493207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45811493738924741555981885 17179310152096778083493207)
  ·
    refine ⟨25768965228145167125239811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17179310152096778083493207 25768965228145167125239811)
    ·
      refine ⟨38653447842217750687859717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768965228145167125239811 38653447842217750687859717)
      ·
        refine ⟨7247521470415828253973697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38653447842217750687859717 7247521470415828253973697)
        ·
          refine ⟨5435641102811871190480273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247521470415828253973697 5435641102811871190480273)
          ·
            refine ⟨4076730827108903392860205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435641102811871190480273 4076730827108903392860205)
            ·
              refine ⟨1528774060165838772322577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4076730827108903392860205 1528774060165838772322577)
              ·
                refine ⟨1146580545124379079241933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528774060165838772322577 1146580545124379079241933)
                ·
                  refine ⟨429967704421642154715725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146580545124379079241933 429967704421642154715725)
                  ·
                    rfl

theorem cell21_1884058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_1884058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884058 prefixEnd_1884058 := by exact prefixLift 1884058
  have htrace : WordTrace (prefixWord ++ tailWord_1884058) baseStart_1884058 baseEnd_1884058 := by
    simpa [prefixWord, tailWord_1884058, baseEnd_1884058] using wordTrace_append hprefix tailTrace_1884058
  have hstable : (prefixWord ++ tailWord_1884058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884058).length < 2 ^ (prefixWord ++ tailWord_1884058).sum := by decide
  have hdescent : baseEnd_1884058 < baseStart_1884058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884117 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 3]
def baseStart_1884117 : Nat := 118140960795 + 1884117 * 2 ^ 59
def prefixEnd_1884117 : Nat := 4983230072969 + 3 ^ 40 * 1884117 * 2
def baseEnd_1884117 : Nat := 429981169025471163232271

theorem tailTrace_1884117 : CollatzResearch.WordTrace tailWord_1884117 prefixEnd_1884117 429981169025471163232271 := by
  unfold tailWord_1884117
  simp only [CollatzResearch.WordTrace]
  refine ⟨68719392515173365410370605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45812928343448910273580403 68719392515173365410370605)
  ·
    refine ⟨25769772193190012028888977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68719392515173365410370605 25769772193190012028888977)
    ·
      refine ⟨19327329144892509021666733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25769772193190012028888977 19327329144892509021666733)
      ·
        refine ⟨7247748429334690883125025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19327329144892509021666733 7247748429334690883125025)
        ·
          refine ⟨5435811322001018162343769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247748429334690883125025 5435811322001018162343769)
          ·
            refine ⟨4076858491500763621757827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435811322001018162343769 4076858491500763621757827)
            ·
              refine ⟨6115287737251145432636741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076858491500763621757827 6115287737251145432636741)
              ·
                refine ⟨1146616450734589768619389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6115287737251145432636741 1146616450734589768619389)
                ·
                  refine ⟨429981169025471163232271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146616450734589768619389 429981169025471163232271)
                  ·
                    rfl

theorem cell21_1884117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_1884117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884117 prefixEnd_1884117 := by exact prefixLift 1884117
  have htrace : WordTrace (prefixWord ++ tailWord_1884117) baseStart_1884117 baseEnd_1884117 := by
    simpa [prefixWord, tailWord_1884117, baseEnd_1884117] using wordTrace_append hprefix tailTrace_1884117
  have hstable : (prefixWord ++ tailWord_1884117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884117).length < 2 ^ (prefixWord ++ tailWord_1884117).sum := by decide
  have hdescent : baseEnd_1884117 < baseStart_1884117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884314 : List Nat := [3, 1, 1, 5, 2, 1, 3, 5]
def baseStart_1884314 : Nat := 118140960795 + 1884314 * 2 ^ 59
def prefixEnd_1884314 : Nat := 4983230072969 + 3 ^ 40 * 1884314 * 2
def baseEnd_1884314 : Nat := 143342042369814199482845

theorem tailTrace_1884314 : CollatzResearch.WordTrace tailWord_1884314 prefixEnd_1884314 143342042369814199482845 := by
  unfold tailWord_1884314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181644423864917013822999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45817718463639778703527997 17181644423864917013822999)
  ·
    refine ⟨25772466635797375520734499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17181644423864917013822999 25772466635797375520734499)
    ·
      refine ⟨38658699953696063281101749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25772466635797375520734499 38658699953696063281101749)
      ·
        refine ⟨3624253120659005932603289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38658699953696063281101749 3624253120659005932603289)
        ·
          refine ⟨2718189840494254449452467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624253120659005932603289 2718189840494254449452467)
          ·
            refine ⟨4077284760741381674178701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718189840494254449452467 4077284760741381674178701)
            ·
              refine ⟨1528981785278018127817013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4077284760741381674178701 1528981785278018127817013)
              ·
                refine ⟨143342042369814199482845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528981785278018127817013 143342042369814199482845)
                ·
                  rfl

theorem cell21_1884314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_1884314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884314 prefixEnd_1884314 := by exact prefixLift 1884314
  have htrace : WordTrace (prefixWord ++ tailWord_1884314) baseStart_1884314 baseEnd_1884314 := by
    simpa [prefixWord, tailWord_1884314, baseEnd_1884314] using wordTrace_append hprefix tailTrace_1884314
  have hstable : (prefixWord ++ tailWord_1884314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884314).length < 2 ^ (prefixWord ++ tailWord_1884314).sum := by decide
  have hdescent : baseEnd_1884314 < baseStart_1884314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884325 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_1884325 : Nat := 118140960795 + 1884325 * 2 ^ 59
def prefixEnd_1884325 : Nat := 4983230072969 + 3 ^ 40 * 1884325 * 2
def baseEnd_1884325 : Nat := 430028637459309023765179

theorem tailTrace_1884325 : CollatzResearch.WordTrace tailWord_1884325 prefixEnd_1884325 430028637459309023765179 := by
  unfold tailWord_1884325
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726978898419816933942429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45817985932279877955961619 68726978898419816933942429)
  ·
    refine ⟨25772617086907431350228411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68726978898419816933942429 25772617086907431350228411)
    ·
      refine ⟨38658925630361147025342617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25772617086907431350228411 38658925630361147025342617)
      ·
        refine ⟨28994194222770860269006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38658925630361147025342617 28994194222770860269006963)
        ·
          refine ⟨43491291334156290403510445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28994194222770860269006963 43491291334156290403510445)
          ·
            refine ⟨16309234250308608901316417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43491291334156290403510445 16309234250308608901316417)
            ·
              refine ⟨12231925687731456675987313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16309234250308608901316417 12231925687731456675987313)
              ·
                refine ⟨9173944265798592506990485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12231925687731456675987313 9173944265798592506990485)
                ·
                  refine ⟨430028637459309023765179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9173944265798592506990485 430028637459309023765179)
                  ·
                    rfl

theorem cell21_1884325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_1884325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884325 prefixEnd_1884325 := by exact prefixLift 1884325
  have htrace : WordTrace (prefixWord ++ tailWord_1884325) baseStart_1884325 baseEnd_1884325 := by
    simpa [prefixWord, tailWord_1884325, baseEnd_1884325] using wordTrace_append hprefix tailTrace_1884325
  have hstable : (prefixWord ++ tailWord_1884325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884325).length < 2 ^ (prefixWord ++ tailWord_1884325).sum := by decide
  have hdescent : baseEnd_1884325 < baseStart_1884325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884334 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1884334 : Nat := 118140960795 + 1884334 * 2 ^ 59
def prefixEnd_1884334 : Nat := 4983230072969 + 3 ^ 40 * 1884334 * 2
def baseEnd_1884334 : Nat := 430030691381927008115161

theorem tailTrace_1884334 : CollatzResearch.WordTrace tailWord_1884334 prefixEnd_1884334 430030691381927008115161 := by
  unfold tailWord_1884334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590913394423401433877507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45818204770258140980680037 8590913394423401433877507)
  ·
    refine ⟨12886370091635102150816261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8590913394423401433877507 12886370091635102150816261)
    ·
      refine ⟨2416194392181581653278049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12886370091635102150816261 2416194392181581653278049)
      ·
        refine ⟨1812145794136186239958537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416194392181581653278049 1812145794136186239958537)
        ·
          refine ⟨1359109345602139679968903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812145794136186239958537 1359109345602139679968903)
          ·
            refine ⟨2038664018403209519953355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359109345602139679968903 2038664018403209519953355)
            ·
              refine ⟨3057996027604814279930033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038664018403209519953355 3057996027604814279930033)
              ·
                refine ⟨2293497020703610709947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057996027604814279930033 2293497020703610709947525)
                ·
                  refine ⟨430030691381927008115161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293497020703610709947525 430030691381927008115161)
                  ·
                    rfl

theorem cell21_1884334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1884334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884334 prefixEnd_1884334 := by exact prefixLift 1884334
  have htrace : WordTrace (prefixWord ++ tailWord_1884334) baseStart_1884334 baseEnd_1884334 := by
    simpa [prefixWord, tailWord_1884334, baseEnd_1884334] using wordTrace_append hprefix tailTrace_1884334
  have hstable : (prefixWord ++ tailWord_1884334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884334).length < 2 ^ (prefixWord ++ tailWord_1884334).sum := by decide
  have hdescent : baseEnd_1884334 < baseStart_1884334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884373 : List Nat := [1, 3, 2, 4, 2, 1, 1, 7]
def baseStart_1884373 : Nat := 118140960795 + 1884373 * 2 ^ 59
def prefixEnd_1884373 : Nat := 4983230072969 + 3 ^ 40 * 1884373 * 2
def baseEnd_1884373 : Nat := 143346530571090535655027

theorem tailTrace_1884373 : CollatzResearch.WordTrace tailWord_1884373 prefixEnd_1884373 143346530571090535655027 := by
  unfold tailWord_1884373
  simp only [CollatzResearch.WordTrace]
  refine ⟨68728729602245921131689773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45819153068163947421126515 68728729602245921131689773)
  ·
    refine ⟨25773273600842220424383665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68728729602245921131689773 25773273600842220424383665)
    ·
      refine ⟨19329955200631665318287749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25773273600842220424383665 19329955200631665318287749)
      ·
        refine ⟨3624366600118437247178953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19329955200631665318287749 3624366600118437247178953)
        ·
          refine ⟨2718274950088827935384215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624366600118437247178953 2718274950088827935384215)
          ·
            refine ⟨4077412425133241903076323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718274950088827935384215 4077412425133241903076323)
            ·
              refine ⟨6116118637699862854614485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077412425133241903076323 6116118637699862854614485)
              ·
                refine ⟨143346530571090535655027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6116118637699862854614485 143346530571090535655027)
                ·
                  rfl

theorem cell21_1884373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_1884373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884373 prefixEnd_1884373 := by exact prefixLift 1884373
  have htrace : WordTrace (prefixWord ++ tailWord_1884373) baseStart_1884373 baseEnd_1884373 := by
    simpa [prefixWord, tailWord_1884373, baseEnd_1884373] using wordTrace_append hprefix tailTrace_1884373
  have hstable : (prefixWord ++ tailWord_1884373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884373).length < 2 ^ (prefixWord ++ tailWord_1884373).sum := by decide
  have hdescent : baseEnd_1884373 < baseStart_1884373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884401 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_1884401 : Nat := 118140960795 + 1884401 * 2 ^ 59
def prefixEnd_1884401 : Nat := 4983230072969 + 3 ^ 40 * 1884401 * 2
def baseEnd_1884401 : Nat := 430045981694749780498357

theorem tailTrace_1884401 : CollatzResearch.WordTrace tailWord_1884401 prefixEnd_1884401 430045981694749780498357 := by
  unfold tailWord_1884401
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729750846144481913709057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45819833897429654609139371 68729750846144481913709057)
  ·
    refine ⟨51547313134608361435281793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68729750846144481913709057 51547313134608361435281793)
    ·
      refine ⟨38660484850956271076461345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51547313134608361435281793 38660484850956271076461345)
      ·
        refine ⟨28995363638217203307346009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38660484850956271076461345 28995363638217203307346009)
        ·
          refine ⟨21746522728662902480509507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28995363638217203307346009 21746522728662902480509507)
          ·
            refine ⟨32619784092994353720764261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746522728662902480509507 32619784092994353720764261)
            ·
              refine ⟨6116209517436441322643299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32619784092994353720764261 6116209517436441322643299)
              ·
                refine ⟨9174314276154661983964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116209517436441322643299 9174314276154661983964949)
                ·
                  refine ⟨430045981694749780498357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9174314276154661983964949 430045981694749780498357)
                  ·
                    rfl

theorem cell21_1884401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_1884401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884401 prefixEnd_1884401 := by exact prefixLift 1884401
  have htrace : WordTrace (prefixWord ++ tailWord_1884401) baseStart_1884401 baseEnd_1884401 := by
    simpa [prefixWord, tailWord_1884401, baseEnd_1884401] using wordTrace_append hprefix tailTrace_1884401
  have hstable : (prefixWord ++ tailWord_1884401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884401).length < 2 ^ (prefixWord ++ tailWord_1884401).sum := by decide
  have hdescent : baseEnd_1884401 < baseStart_1884401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884455 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 3]
def baseStart_1884455 : Nat := 118140960795 + 1884455 * 2 ^ 59
def prefixEnd_1884455 : Nat := 4983230072969 + 3 ^ 40 * 1884455 * 2
def baseEnd_1884455 : Nat := 430058305230457686598247

theorem tailTrace_1884455 : CollatzResearch.WordTrace tailWord_1884455 prefixEnd_1884455 430058305230457686598247 := by
  unfold tailWord_1884455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68731720387948849136174819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45821146925299232757449879 68731720387948849136174819)
  ·
    refine ⟨103097580581923273704262229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68731720387948849136174819 103097580581923273704262229)
    ·
      refine ⟨1208174772444413363721823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 103097580581923273704262229 1208174772444413363721823)
      ·
        refine ⟨1812262158666620045582735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208174772444413363721823 1812262158666620045582735)
        ·
          refine ⟨2718393237999930068374103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812262158666620045582735 2718393237999930068374103)
          ·
            refine ⟨4077589856999895102561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718393237999930068374103 4077589856999895102561155)
            ·
              refine ⟨6116384785499842653841733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077589856999895102561155 6116384785499842653841733)
              ·
                refine ⟨1146822147281220497595325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6116384785499842653841733 1146822147281220497595325)
                ·
                  refine ⟨430058305230457686598247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146822147281220497595325 430058305230457686598247)
                  ·
                    rfl

theorem cell21_1884455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].length) (baseStart_1884455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884455 prefixEnd_1884455 := by exact prefixLift 1884455
  have htrace : WordTrace (prefixWord ++ tailWord_1884455) baseStart_1884455 baseEnd_1884455 := by
    simpa [prefixWord, tailWord_1884455, baseEnd_1884455] using wordTrace_append hprefix tailTrace_1884455
  have hstable : (prefixWord ++ tailWord_1884455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884455).length < 2 ^ (prefixWord ++ tailWord_1884455).sum := by decide
  have hdescent : baseEnd_1884455 < baseStart_1884455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884466 : List Nat := [3, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1884466 : Nat := 118140960795 + 1884466 * 2 ^ 59
def prefixEnd_1884466 : Nat := 4983230072969 + 3 ^ 40 * 1884466 * 2
def baseEnd_1884466 : Nat := 143353605193441370638297

theorem tailTrace_1884466 : CollatzResearch.WordTrace tailWord_1884466 prefixEnd_1884466 143353605193441370638297 := by
  unfold tailWord_1884466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183030397727249503706313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45821414393939332009883501 17183030397727249503706313)
  ·
    refine ⟨12887272798295437127779735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17183030397727249503706313 12887272798295437127779735)
    ·
      refine ⟨19330909197443155691669603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12887272798295437127779735 19330909197443155691669603)
      ·
        refine ⟨28996363796164733537504405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19330909197443155691669603 28996363796164733537504405)
        ·
          refine ⟨1359204552945221884570519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28996363796164733537504405 1359204552945221884570519)
          ·
            refine ⟨2038806829417832826855779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359204552945221884570519 2038806829417832826855779)
            ·
              refine ⟨3058210244126749240283669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038806829417832826855779 3058210244126749240283669)
              ·
                refine ⟨143353605193441370638297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3058210244126749240283669 143353605193441370638297)
                ·
                  rfl

theorem cell21_1884466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1884466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884466 prefixEnd_1884466 := by exact prefixLift 1884466
  have htrace : WordTrace (prefixWord ++ tailWord_1884466) baseStart_1884466 baseEnd_1884466 := by
    simpa [prefixWord, tailWord_1884466, baseEnd_1884466] using wordTrace_append hprefix tailTrace_1884466
  have hstable : (prefixWord ++ tailWord_1884466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884466).length < 2 ^ (prefixWord ++ tailWord_1884466).sum := by decide
  have hdescent : baseEnd_1884466 < baseStart_1884466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884553 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_1884553 : Nat := 118140960795 + 1884553 * 2 ^ 59
def prefixEnd_1884553 : Nat := 4983230072969 + 3 ^ 40 * 1884553 * 2
def baseEnd_1884553 : Nat := 430080670165631293964713

theorem tailTrace_1884553 : CollatzResearch.WordTrace tailWord_1884553 prefixEnd_1884553 430080670165631293964713 := by
  unfold tailWord_1884553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68735294741593811873242313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45823529827729207915494875 68735294741593811873242313)
  ·
    refine ⟨51551471056195358904931735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68735294741593811873242313 51551471056195358904931735)
    ·
      refine ⟨77327206584293038357397603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51551471056195358904931735 77327206584293038357397603)
      ·
        refine ⟨115990809876439557536096405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77327206584293038357397603 115990809876439557536096405)
        ·
          refine ⟨5437069212958104259504519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115990809876439557536096405 5437069212958104259504519)
          ·
            refine ⟨8155603819437156389256779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437069212958104259504519 8155603819437156389256779)
            ·
              refine ⟨12233405729155734583885169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8155603819437156389256779 12233405729155734583885169)
              ·
                refine ⟨9175054296866800937913877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233405729155734583885169 9175054296866800937913877)
                ·
                  refine ⟨430080670165631293964713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9175054296866800937913877 430080670165631293964713)
                  ·
                    rfl

theorem cell21_1884553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_1884553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884553 prefixEnd_1884553 := by exact prefixLift 1884553
  have htrace : WordTrace (prefixWord ++ tailWord_1884553) baseStart_1884553 baseEnd_1884553 := by
    simpa [prefixWord, tailWord_1884553, baseEnd_1884553] using wordTrace_append hprefix tailTrace_1884553
  have hstable : (prefixWord ++ tailWord_1884553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884553).length < 2 ^ (prefixWord ++ tailWord_1884553).sum := by decide
  have hdescent : baseEnd_1884553 < baseStart_1884553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884556 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_1884556 : Nat := 118140960795 + 1884556 * 2 ^ 59
def prefixEnd_1884556 : Nat := 4983230072969 + 3 ^ 40 * 1884556 * 2
def baseEnd_1884556 : Nat := 430081354806503955414707

theorem tailTrace_1884556 : CollatzResearch.WordTrace tailWord_1884556 prefixEnd_1884556 430081354806503955414707 := by
  unfold tailWord_1884556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34367702080291471692800761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45823602773721962257067681 34367702080291471692800761)
  ·
    refine ⟨25775776560218603769600571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34367702080291471692800761 25775776560218603769600571)
    ·
      refine ⟨38663664840327905654400857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25775776560218603769600571 38663664840327905654400857)
      ·
        refine ⟨28997748630245929240800643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38663664840327905654400857 28997748630245929240800643)
        ·
          refine ⟨43496622945368893861200965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28997748630245929240800643 43496622945368893861200965)
          ·
            refine ⟨8155616802256667598975181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43496622945368893861200965 8155616802256667598975181)
            ·
              refine ⟨3058356300846250349615693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8155616802256667598975181 3058356300846250349615693)
              ·
                refine ⟨1146883612817343881105885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3058356300846250349615693 1146883612817343881105885)
                ·
                  refine ⟨430081354806503955414707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146883612817343881105885 430081354806503955414707)
                  ·
                    rfl

theorem cell21_1884556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_1884556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884556 prefixEnd_1884556 := by exact prefixLift 1884556
  have htrace : WordTrace (prefixWord ++ tailWord_1884556) baseStart_1884556 baseEnd_1884556 := by
    simpa [prefixWord, tailWord_1884556, baseEnd_1884556] using wordTrace_append hprefix tailTrace_1884556
  have hstable : (prefixWord ++ tailWord_1884556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884556).length < 2 ^ (prefixWord ++ tailWord_1884556).sum := by decide
  have hdescent : baseEnd_1884556 < baseStart_1884556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884567 : List Nat := [1, 1, 3, 3, 1, 1, 11]
def baseStart_1884567 : Nat := 118140960795 + 1884567 * 2 ^ 59
def prefixEnd_1884567 : Nat := 4983230072969 + 3 ^ 40 * 1884567 * 2
def baseEnd_1884567 : Nat := 47787096128485597859039

theorem tailTrace_1884567 : CollatzResearch.WordTrace tailWord_1884567 prefixEnd_1884567 47787096128485597859039 := by
  unfold tailWord_1884567
  simp only [CollatzResearch.WordTrace]
  refine ⟨68735805363543092264251955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45823870242362061509501303 68735805363543092264251955)
  ·
    refine ⟨103103708045314638396377933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68735805363543092264251955 103103708045314638396377933)
    ·
      refine ⟨38663890516992989398641725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103103708045314638396377933 38663890516992989398641725)
      ·
        refine ⟨14498958943872371024490647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38663890516992989398641725 14498958943872371024490647)
        ·
          refine ⟨21748438415808556536735971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498958943872371024490647 21748438415808556536735971)
          ·
            refine ⟨32622657623712834805103957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21748438415808556536735971 32622657623712834805103957)
            ·
              refine ⟨47787096128485597859039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32622657623712834805103957 47787096128485597859039)
              ·
                rfl

theorem cell21_1884567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_1884567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884567 prefixEnd_1884567 := by exact prefixLift 1884567
  have htrace : WordTrace (prefixWord ++ tailWord_1884567) baseStart_1884567 baseEnd_1884567 := by
    simpa [prefixWord, tailWord_1884567, baseEnd_1884567] using wordTrace_append hprefix tailTrace_1884567
  have hstable : (prefixWord ++ tailWord_1884567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884567).length < 2 ^ (prefixWord ++ tailWord_1884567).sum := by decide
  have hdescent : baseEnd_1884567 < baseStart_1884567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884573 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1884573 : Nat := 118140960795 + 1884573 * 2 ^ 59
def prefixEnd_1884573 : Nat := 4983230072969 + 3 ^ 40 * 1884573 * 2
def baseEnd_1884573 : Nat := 430085234438115703631339

theorem tailTrace_1884573 : CollatzResearch.WordTrace tailWord_1884573 prefixEnd_1884573 430085234438115703631339 := by
  unfold tailWord_1884573
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736024201521355288970373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45824016134347570192646915 68736024201521355288970373)
  ·
    refine ⟨12888004537785254116681945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68736024201521355288970373 12888004537785254116681945)
    ·
      refine ⟨9666003403338940587511459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12888004537785254116681945 9666003403338940587511459)
      ·
        refine ⟨14499005105008410881267189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666003403338940587511459 14499005105008410881267189)
        ·
          refine ⟨1359281728594538520118799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14499005105008410881267189 1359281728594538520118799)
          ·
            refine ⟨2038922592891807780178199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359281728594538520118799 2038922592891807780178199)
            ·
              refine ⟨3058383889337711670267299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038922592891807780178199 3058383889337711670267299)
              ·
                refine ⟨4587575834006567505400949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058383889337711670267299 4587575834006567505400949)
                ·
                  refine ⟨430085234438115703631339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4587575834006567505400949 430085234438115703631339)
                  ·
                    rfl

theorem cell21_1884573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1884573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884573 prefixEnd_1884573 := by exact prefixLift 1884573
  have htrace : WordTrace (prefixWord ++ tailWord_1884573) baseStart_1884573 baseEnd_1884573 := by
    simpa [prefixWord, tailWord_1884573, baseEnd_1884573] using wordTrace_append hprefix tailTrace_1884573
  have hstable : (prefixWord ++ tailWord_1884573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884573).length < 2 ^ (prefixWord ++ tailWord_1884573).sum := by decide
  have hdescent : baseEnd_1884573 < baseStart_1884573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884691 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 3]
def baseStart_1884691 : Nat := 118140960795 + 1884691 * 2 ^ 59
def prefixEnd_1884691 : Nat := 4983230072969 + 3 ^ 40 * 1884691 * 2
def baseEnd_1884691 : Nat := 430112163645773720664431

theorem tailTrace_1884691 : CollatzResearch.WordTrace tailWord_1884691 prefixEnd_1884691 430112163645773720664431 := by
  unfold tailWord_1884691
  simp only [CollatzResearch.WordTrace]
  refine ⟨68740328015093861441765927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45826885343395907627843951 68740328015093861441765927)
  ·
    refine ⟨103110492022640792162648891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68740328015093861441765927 103110492022640792162648891)
    ·
      refine ⟨154665738033961188243973337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103110492022640792162648891 154665738033961188243973337)
      ·
        refine ⟨115999303525470891182980003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154665738033961188243973337 115999303525470891182980003)
        ·
          refine ⟨173998955288206336774470005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115999303525470891182980003 173998955288206336774470005)
          ·
            refine ⟨16312402058269344072606563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173998955288206336774470005 16312402058269344072606563)
            ·
              refine ⟨24468603087404016108909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16312402058269344072606563 24468603087404016108909845)
              ·
                refine ⟨1146965769722063255105149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24468603087404016108909845 1146965769722063255105149)
                ·
                  refine ⟨430112163645773720664431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146965769722063255105149 430112163645773720664431)
                  ·
                    rfl

theorem cell21_1884691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].length) (baseStart_1884691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884691 prefixEnd_1884691 := by exact prefixLift 1884691
  have htrace : WordTrace (prefixWord ++ tailWord_1884691) baseStart_1884691 baseEnd_1884691 := by
    simpa [prefixWord, tailWord_1884691, baseEnd_1884691] using wordTrace_append hprefix tailTrace_1884691
  have hstable : (prefixWord ++ tailWord_1884691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884691).length < 2 ^ (prefixWord ++ tailWord_1884691).sum := by decide
  have hdescent : baseEnd_1884691 < baseStart_1884691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884711 : List Nat := [1, 1, 7, 2, 1, 2, 2, 5]
def baseStart_1884711 : Nat := 118140960795 + 1884711 * 2 ^ 59
def prefixEnd_1884711 : Nat := 4983230072969 + 3 ^ 40 * 1884711 * 2
def baseEnd_1884711 : Nat := 143372242639419376777019

theorem tailTrace_1884711 : CollatzResearch.WordTrace tailWord_1884711 prefixEnd_1884711 143372242639419376777019 := by
  unfold tailWord_1884711
  simp only [CollatzResearch.WordTrace]
  refine ⟨68741057475021404857493987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45827371650014269904995991 68741057475021404857493987)
  ·
    refine ⟨103111586212532107286240981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68741057475021404857493987 103111586212532107286240981)
    ·
      refine ⟨2416677801856221264521273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103111586212532107286240981 2416677801856221264521273)
      ·
        refine ⟨1812508351392165948390955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416677801856221264521273 1812508351392165948390955)
        ·
          refine ⟨2718762527088248922586433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812508351392165948390955 2718762527088248922586433)
          ·
            refine ⟨2039071895316186691939825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2718762527088248922586433 2039071895316186691939825)
            ·
              refine ⟨1529303921487140018954869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039071895316186691939825 1529303921487140018954869)
              ·
                refine ⟨143372242639419376777019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529303921487140018954869 143372242639419376777019)
                ·
                  rfl

theorem cell21_1884711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].length) (baseStart_1884711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884711 prefixEnd_1884711 := by exact prefixLift 1884711
  have htrace : WordTrace (prefixWord ++ tailWord_1884711) baseStart_1884711 baseEnd_1884711 := by
    simpa [prefixWord, tailWord_1884711, baseEnd_1884711] using wordTrace_append hprefix tailTrace_1884711
  have hstable : (prefixWord ++ tailWord_1884711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884711).length < 2 ^ (prefixWord ++ tailWord_1884711).sum := by decide
  have hdescent : baseEnd_1884711 < baseStart_1884711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884888 : List Nat := [2, 1, 2, 2, 3, 2, 4, 5]
def baseStart_1884888 : Nat := 118140960795 + 1884888 * 2 ^ 59
def prefixEnd_1884888 : Nat := 4983230072969 + 3 ^ 40 * 1884888 * 2
def baseEnd_1884888 : Nat := 143385707243248385293565

theorem tailTrace_1884888 : CollatzResearch.WordTrace tailWord_1884888 prefixEnd_1884888 143385707243248385293565 := by
  unfold tailWord_1884888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373756597690082043343659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45831675463586776057791545 34373756597690082043343659)
  ·
    refine ⟨51560634896535123065015489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34373756597690082043343659 51560634896535123065015489)
    ·
      refine ⟨38670476172401342298761617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51560634896535123065015489 38670476172401342298761617)
      ·
        refine ⟨29002857129301006724071213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38670476172401342298761617 29002857129301006724071213)
        ·
          refine ⟨10876071423487877521526705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29002857129301006724071213 10876071423487877521526705)
          ·
            refine ⟨8157053567615908141145029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10876071423487877521526705 8157053567615908141145029)
            ·
              refine ⟨1529447543927982776464693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8157053567615908141145029 1529447543927982776464693)
              ·
                refine ⟨143385707243248385293565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529447543927982776464693 143385707243248385293565)
                ·
                  rfl

theorem cell21_1884888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_1884888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884888 prefixEnd_1884888 := by exact prefixLift 1884888
  have htrace : WordTrace (prefixWord ++ tailWord_1884888) baseStart_1884888 baseEnd_1884888 := by
    simpa [prefixWord, tailWord_1884888, baseEnd_1884888] using wordTrace_append hprefix tailTrace_1884888
  have hstable : (prefixWord ++ tailWord_1884888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884888).length < 2 ^ (prefixWord ++ tailWord_1884888).sum := by decide
  have hdescent : baseEnd_1884888 < baseStart_1884888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884964 : List Nat := [2, 3, 1, 3, 4, 8]
def baseStart_1884964 : Nat := 118140960795 + 1884964 * 2 ^ 59
def prefixEnd_1884964 : Nat := 4983230072969 + 3 ^ 40 * 1884964 * 2
def baseEnd_1884964 : Nat := 15932387628340218985699

theorem tailTrace_1884964 : CollatzResearch.WordTrace tailWord_1884964 prefixEnd_1884964 15932387628340218985699 := by
  unfold tailWord_1884964
  simp only [CollatzResearch.WordTrace]
  refine ⟨34375142571552414533226973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45833523428736552710969297 34375142571552414533226973)
  ·
    refine ⟨12890678464332155449960115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34375142571552414533226973 12890678464332155449960115)
    ·
      refine ⟨19336017696498233174940173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890678464332155449960115 19336017696498233174940173)
      ·
        refine ⟨7251006636186837440602565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19336017696498233174940173 7251006636186837440602565)
        ·
          refine ⟨1359563744285032020112981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7251006636186837440602565 1359563744285032020112981)
          ·
            refine ⟨15932387628340218985699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1359563744285032020112981 15932387628340218985699)
            ·
              rfl

theorem cell21_1884964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 8].length) (baseStart_1884964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884964 prefixEnd_1884964 := by exact prefixLift 1884964
  have htrace : WordTrace (prefixWord ++ tailWord_1884964) baseStart_1884964 baseEnd_1884964 := by
    simpa [prefixWord, tailWord_1884964, baseEnd_1884964] using wordTrace_append hprefix tailTrace_1884964
  have hstable : (prefixWord ++ tailWord_1884964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884964).length < 2 ^ (prefixWord ++ tailWord_1884964).sum := by decide
  have hdescent : baseEnd_1884964 < baseStart_1884964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884978 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1884978 : Nat := 118140960795 + 1884978 * 2 ^ 59
def prefixEnd_1884978 : Nat := 4983230072969 + 3 ^ 40 * 1884978 * 2
def baseEnd_1884978 : Nat := 430177660955924999380511

theorem tailTrace_1884978 : CollatzResearch.WordTrace tailWord_1884978 prefixEnd_1884978 430177660955924999380511 := by
  unfold tailWord_1884978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187698941263527364365897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45833863843369406304975725 17187698941263527364365897)
  ·
    refine ⟨12890774205947645523274423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17187698941263527364365897 12890774205947645523274423)
    ·
      refine ⟨19336161308921468284911635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890774205947645523274423 19336161308921468284911635)
      ·
        refine ⟨29004241963382202427367453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336161308921468284911635 29004241963382202427367453)
        ·
          refine ⟨10876590736268325910262795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29004241963382202427367453 10876590736268325910262795)
          ·
            refine ⟨16314886104402488865394193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10876590736268325910262795 16314886104402488865394193)
            ·
              refine ⟨12236164578301866649045645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16314886104402488865394193 12236164578301866649045645)
              ·
                refine ⟨4588561716863199993392117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12236164578301866649045645 4588561716863199993392117)
                ·
                  refine ⟨430177660955924999380511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4588561716863199993392117 430177660955924999380511)
                  ·
                    rfl

theorem cell21_1884978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1884978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1884978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1884978 prefixEnd_1884978 := by exact prefixLift 1884978
  have htrace : WordTrace (prefixWord ++ tailWord_1884978) baseStart_1884978 baseEnd_1884978 := by
    simpa [prefixWord, tailWord_1884978, baseEnd_1884978] using wordTrace_append hprefix tailTrace_1884978
  have hstable : (prefixWord ++ tailWord_1884978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884978).length < 2 ^ (prefixWord ++ tailWord_1884978).sum := by decide
  have hdescent : baseEnd_1884978 < baseStart_1884978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885026 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1885026 : Nat := 118140960795 + 1885026 * 2 ^ 59
def prefixEnd_1885026 : Nat := 4983230072969 + 3 ^ 40 * 1885026 * 2
def baseEnd_1885026 : Nat := 430188615209887582580413

theorem tailTrace_1885026 : CollatzResearch.WordTrace tailWord_1885026 prefixEnd_1885026 430188615209887582580413 := by
  unfold tailWord_1885026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188136617220053413802733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45835030979253475770140621 17188136617220053413802733)
  ·
    refine ⟨6445551231457520030176025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17188136617220053413802733 6445551231457520030176025)
    ·
      refine ⟨4834163423593140022632019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445551231457520030176025 4834163423593140022632019)
      ·
        refine ⟨7251245135389710033948029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834163423593140022632019 7251245135389710033948029)
        ·
          refine ⟨2719216925771141262730511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7251245135389710033948029 2719216925771141262730511)
          ·
            refine ⟨4078825388656711894095767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719216925771141262730511 4078825388656711894095767)
            ·
              refine ⟨6118238082985067841143651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078825388656711894095767 6118238082985067841143651)
              ·
                refine ⟨9177357124477601761715477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118238082985067841143651 9177357124477601761715477)
                ·
                  refine ⟨430188615209887582580413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9177357124477601761715477 430188615209887582580413)
                  ·
                    rfl

theorem cell21_1885026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1885026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885026 prefixEnd_1885026 := by exact prefixLift 1885026
  have htrace : WordTrace (prefixWord ++ tailWord_1885026) baseStart_1885026 baseEnd_1885026 := by
    simpa [prefixWord, tailWord_1885026, baseEnd_1885026] using wordTrace_append hprefix tailTrace_1885026
  have hstable : (prefixWord ++ tailWord_1885026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885026).length < 2 ^ (prefixWord ++ tailWord_1885026).sum := by decide
  have hdescent : baseEnd_1885026 < baseStart_1885026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885068 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1885068 : Nat := 118140960795 + 1885068 * 2 ^ 59
def prefixEnd_1885068 : Nat := 4983230072969 + 3 ^ 40 * 1885068 * 2
def baseEnd_1885068 : Nat := 430198200182104842880327

theorem tailTrace_1885068 : CollatzResearch.WordTrace tailWord_1885068 prefixEnd_1885068 430198200182104842880327 := by
  unfold tailWord_1885068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377039167364027414119929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45836052223152036552159905 34377039167364027414119929)
  ·
    refine ⟨25782779375523020560589947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34377039167364027414119929 25782779375523020560589947)
    ·
      refine ⟨38674169063284530840884921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25782779375523020560589947 38674169063284530840884921)
      ·
        refine ⟨29005626797463398130663691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38674169063284530840884921 29005626797463398130663691)
        ·
          refine ⟨43508440196195097195995537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29005626797463398130663691 43508440196195097195995537)
          ·
            refine ⟨32631330147146322896996653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43508440196195097195995537 32631330147146322896996653)
            ·
              refine ⟨12236748805179871086373745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32631330147146322896996653 12236748805179871086373745)
              ·
                refine ⟨9177561603884903314780309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12236748805179871086373745 9177561603884903314780309)
                ·
                  refine ⟨430198200182104842880327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9177561603884903314780309 430198200182104842880327)
                  ·
                    rfl

theorem cell21_1885068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1885068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885068 prefixEnd_1885068 := by exact prefixLift 1885068
  have htrace : WordTrace (prefixWord ++ tailWord_1885068) baseStart_1885068 baseEnd_1885068 := by
    simpa [prefixWord, tailWord_1885068, baseEnd_1885068] using wordTrace_append hprefix tailTrace_1885068
  have hstable : (prefixWord ++ tailWord_1885068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885068).length < 2 ^ (prefixWord ++ tailWord_1885068).sum := by decide
  have hdescent : baseEnd_1885068 < baseStart_1885068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885085 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1885085 : Nat := 118140960795 + 1885085 * 2 ^ 59
def prefixEnd_1885085 : Nat := 4983230072969 + 3 ^ 40 * 1885085 * 2
def baseEnd_1885085 : Nat := 430202079813716591096959

theorem tailTrace_1885085 : CollatzResearch.WordTrace tailWord_1885085 prefixEnd_1885085 430202079813716591096959 := by
  unfold tailWord_1885085
  simp only [CollatzResearch.WordTrace]
  refine ⟨68754698375666466731608709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45836465583777644487739139 68754698375666466731608709)
  ·
    refine ⟨12891505945437462512176633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68754698375666466731608709 12891505945437462512176633)
    ·
      refine ⟨9668629459078096884132475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12891505945437462512176633 9668629459078096884132475)
      ·
        refine ⟨14502944188617145326198713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9668629459078096884132475 14502944188617145326198713)
        ·
          refine ⟨10877208141462858994649035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14502944188617145326198713 10877208141462858994649035)
          ·
            refine ⟨16315812212194288491973553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877208141462858994649035 16315812212194288491973553)
            ·
              refine ⟨12236859159145716368980165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16315812212194288491973553 12236859159145716368980165)
              ·
                refine ⟨2294411092339821819183781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12236859159145716368980165 2294411092339821819183781)
                ·
                  refine ⟨430202079813716591096959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294411092339821819183781 430202079813716591096959)
                  ·
                    rfl

theorem cell21_1885085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1885085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885085 prefixEnd_1885085 := by exact prefixLift 1885085
  have htrace : WordTrace (prefixWord ++ tailWord_1885085) baseStart_1885085 baseEnd_1885085 := by
    simpa [prefixWord, tailWord_1885085, baseEnd_1885085] using wordTrace_append hprefix tailTrace_1885085
  have hstable : (prefixWord ++ tailWord_1885085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885085).length < 2 ^ (prefixWord ++ tailWord_1885085).sum := by decide
  have hdescent : baseEnd_1885085 < baseStart_1885085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885133 : List Nat := [1, 6, 3, 1, 10]
def baseStart_1885133 : Nat := 118140960795 + 1885133 * 2 ^ 59
def prefixEnd_1885133 : Nat := 4983230072969 + 3 ^ 40 * 1885133 * 2
def baseEnd_1885133 : Nat := 5311272025526903386381

theorem tailTrace_1885133 : CollatzResearch.WordTrace tailWord_1885133 prefixEnd_1885133 5311272025526903386381 := by
  unfold tailWord_1885133
  simp only [CollatzResearch.WordTrace]
  refine ⟨68756449079492570929356053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45837632719661713952904035 68756449079492570929356053)
  ·
    refine ⟨3222958550601214262313565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68756449079492570929356053 3222958550601214262313565)
    ·
      refine ⟨1208609456475455348367587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3222958550601214262313565 1208609456475455348367587)
      ·
        refine ⟨1812914184713183022551381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208609456475455348367587 1812914184713183022551381)
        ·
          refine ⟨5311272025526903386381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1812914184713183022551381 5311272025526903386381)
          ·
            rfl

theorem cell21_1885133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 10].length) (baseStart_1885133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885133 prefixEnd_1885133 := by exact prefixLift 1885133
  have htrace : WordTrace (prefixWord ++ tailWord_1885133) baseStart_1885133 baseEnd_1885133 := by
    simpa [prefixWord, tailWord_1885133, baseEnd_1885133] using wordTrace_append hprefix tailTrace_1885133
  have hstable : (prefixWord ++ tailWord_1885133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885133).length < 2 ^ (prefixWord ++ tailWord_1885133).sum := by decide
  have hdescent : baseEnd_1885133 < baseStart_1885133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885189 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_1885189 : Nat := 118140960795 + 1885189 * 2 ^ 59
def prefixEnd_1885189 : Nat := 4983230072969 + 3 ^ 40 * 1885189 * 2
def baseEnd_1885189 : Nat := 430225814030635521363413

theorem tailTrace_1885189 : CollatzResearch.WordTrace tailWord_1885189 prefixEnd_1885189 430225814030635521363413 := by
  unfold tailWord_1885189
  simp only [CollatzResearch.WordTrace]
  refine ⟨68758491567289692493394621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45838994378193128328929747 68758491567289692493394621)
  ·
    refine ⟨25784434337733634685022983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68758491567289692493394621 25784434337733634685022983)
    ·
      refine ⟨38676651506600452027534475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25784434337733634685022983 38676651506600452027534475)
      ·
        refine ⟨58014977259900678041301713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38676651506600452027534475 58014977259900678041301713)
        ·
          refine ⟨43511232944925508530976285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58014977259900678041301713 43511232944925508530976285)
          ·
            refine ⟨16316712354347065699116107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43511232944925508530976285 16316712354347065699116107)
            ·
              refine ⟨24475068531520598548674161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16316712354347065699116107 24475068531520598548674161)
              ·
                refine ⟨18356301398640448911505621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24475068531520598548674161 18356301398640448911505621)
                ·
                  refine ⟨430225814030635521363413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18356301398640448911505621 430225814030635521363413)
                  ·
                    rfl

theorem cell21_1885189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_1885189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885189 prefixEnd_1885189 := by exact prefixLift 1885189
  have htrace : WordTrace (prefixWord ++ tailWord_1885189) baseStart_1885189 baseEnd_1885189 := by
    simpa [prefixWord, tailWord_1885189, baseEnd_1885189] using wordTrace_append hprefix tailTrace_1885189
  have hstable : (prefixWord ++ tailWord_1885189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885189).length < 2 ^ (prefixWord ++ tailWord_1885189).sum := by decide
  have hdescent : baseEnd_1885189 < baseStart_1885189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885223 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_1885223 : Nat := 118140960795 + 1885223 * 2 ^ 59
def prefixEnd_1885223 : Nat := 4983230072969 + 3 ^ 40 * 1885223 * 2
def baseEnd_1885223 : Nat := 430233573293859017796677

theorem tailTrace_1885223 : CollatzResearch.WordTrace tailWord_1885223 prefixEnd_1885223 430233573293859017796677 := by
  unfold tailWord_1885223
  simp only [CollatzResearch.WordTrace]
  refine ⟨68759731649166516300132323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45839821099444344200088215 68759731649166516300132323)
  ·
    refine ⟨103139597473749774450198485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68759731649166516300132323 103139597473749774450198485)
    ·
      refine ⟨2417334315791010338676527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103139597473749774450198485 2417334315791010338676527)
      ·
        refine ⟨3626001473686515508014791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417334315791010338676527 3626001473686515508014791)
        ·
          refine ⟨5439002210529773262022187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626001473686515508014791 5439002210529773262022187)
          ·
            refine ⟨8158503315794659893033281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439002210529773262022187 8158503315794659893033281)
            ·
              refine ⟨6118877486845994919774961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158503315794659893033281 6118877486845994919774961)
              ·
                refine ⟨4589158115134496189831221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118877486845994919774961 4589158115134496189831221)
                ·
                  refine ⟨430233573293859017796677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4589158115134496189831221 430233573293859017796677)
                  ·
                    rfl

theorem cell21_1885223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_1885223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885223 prefixEnd_1885223 := by exact prefixLift 1885223
  have htrace : WordTrace (prefixWord ++ tailWord_1885223) baseStart_1885223 baseEnd_1885223 := by
    simpa [prefixWord, tailWord_1885223, baseEnd_1885223] using wordTrace_append hprefix tailTrace_1885223
  have hstable : (prefixWord ++ tailWord_1885223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885223).length < 2 ^ (prefixWord ++ tailWord_1885223).sum := by decide
  have hdescent : baseEnd_1885223 < baseStart_1885223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885226 : List Nat := [3, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1885226 : Nat := 118140960795 + 1885226 * 2 ^ 59
def prefixEnd_1885226 : Nat := 4983230072969 + 3 ^ 40 * 1885226 * 2
def baseEnd_1885226 : Nat := 143411419311577226415557

theorem tailTrace_1885226 : CollatzResearch.WordTrace tailWord_1885226 prefixEnd_1885226 143411419311577226415557 := by
  unfold tailWord_1885226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17189960267038911953122883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45839894045437098541661021 17189960267038911953122883)
  ·
    refine ⟨25784940400558367929684325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17189960267038911953122883 25784940400558367929684325)
    ·
      refine ⟨4834676325104693986815811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25784940400558367929684325 4834676325104693986815811)
      ·
        refine ⟨7252014487657040980223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834676325104693986815811 7252014487657040980223717)
        ·
          refine ⟨1359752716435695183791947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7252014487657040980223717 1359752716435695183791947)
          ·
            refine ⟨2039629074653542775687921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359752716435695183791947 2039629074653542775687921)
            ·
              refine ⟨1529721805990157081765941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039629074653542775687921 1529721805990157081765941)
              ·
                refine ⟨143411419311577226415557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529721805990157081765941 143411419311577226415557)
                ·
                  rfl

theorem cell21_1885226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1885226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885226 prefixEnd_1885226 := by exact prefixLift 1885226
  have htrace : WordTrace (prefixWord ++ tailWord_1885226) baseStart_1885226 baseEnd_1885226 := by
    simpa [prefixWord, tailWord_1885226, baseEnd_1885226] using wordTrace_append hprefix tailTrace_1885226
  have hstable : (prefixWord ++ tailWord_1885226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885226).length < 2 ^ (prefixWord ++ tailWord_1885226).sum := by decide
  have hdescent : baseEnd_1885226 < baseStart_1885226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885240 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_1885240 : Nat := 118140960795 + 1885240 * 2 ^ 59
def prefixEnd_1885240 : Nat := 4983230072969 + 3 ^ 40 * 1885240 * 2
def baseEnd_1885240 : Nat := 430237452925470766013309

theorem tailTrace_1885240 : CollatzResearch.WordTrace tailWord_1885240 prefixEnd_1885240 430237452925470766013309 := by
  unfold tailWord_1885240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34380175845052464101750587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45840234460069952135667449 34380175845052464101750587)
  ·
    refine ⟨51570263767578696152625881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34380175845052464101750587 51570263767578696152625881)
    ·
      refine ⟨38677697825684022114469411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51570263767578696152625881 38677697825684022114469411)
      ·
        refine ⟨58016546738526033171704117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38677697825684022114469411 58016546738526033171704117)
        ·
          refine ⟨5439051256736815609847261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58016546738526033171704117 5439051256736815609847261)
          ·
            refine ⟨2039644221276305853692723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5439051256736815609847261 2039644221276305853692723)
            ·
              refine ⟨3059466331914458780539085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039644221276305853692723 3059466331914458780539085)
              ·
                refine ⟨1147299874467922042702157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059466331914458780539085 1147299874467922042702157)
                ·
                  refine ⟨430237452925470766013309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147299874467922042702157 430237452925470766013309)
                  ·
                    rfl

theorem cell21_1885240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_1885240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885240 prefixEnd_1885240 := by exact prefixLift 1885240
  have htrace : WordTrace (prefixWord ++ tailWord_1885240) baseStart_1885240 baseEnd_1885240 := by
    simpa [prefixWord, tailWord_1885240, baseEnd_1885240] using wordTrace_append hprefix tailTrace_1885240
  have hstable : (prefixWord ++ tailWord_1885240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885240).length < 2 ^ (prefixWord ++ tailWord_1885240).sum := by decide
  have hdescent : baseEnd_1885240 < baseStart_1885240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885254 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1885254 : Nat := 118140960795 + 1885254 * 2 ^ 59
def prefixEnd_1885254 : Nat := 4983230072969 + 3 ^ 40 * 1885254 * 2
def baseEnd_1885254 : Nat := 430240647916209852779947

theorem tailTrace_1885254 : CollatzResearch.WordTrace tailWord_1885254 prefixEnd_1885254 430240647916209852779947 := by
  unfold tailWord_1885254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148776947251694018578463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45840574874702805729673877 2148776947251694018578463)
  ·
    refine ⟨3223165420877541027867695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148776947251694018578463 3223165420877541027867695)
    ·
      refine ⟨4834748131316311541801543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223165420877541027867695 4834748131316311541801543)
      ·
        refine ⟨7252122196974467312702315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834748131316311541801543 7252122196974467312702315)
        ·
          refine ⟨10878183295461700969053473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252122196974467312702315 10878183295461700969053473)
          ·
            refine ⟨8158637471596275726790105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878183295461700969053473 8158637471596275726790105)
            ·
              refine ⟨6118978103697206795092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158637471596275726790105 6118978103697206795092579)
              ·
                refine ⟨9178467155545810192638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118978103697206795092579 9178467155545810192638869)
                ·
                  refine ⟨430240647916209852779947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9178467155545810192638869 430240647916209852779947)
                  ·
                    rfl

theorem cell21_1885254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1885254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885254 prefixEnd_1885254 := by exact prefixLift 1885254
  have htrace : WordTrace (prefixWord ++ tailWord_1885254) baseStart_1885254 baseEnd_1885254 := by
    simpa [prefixWord, tailWord_1885254, baseEnd_1885254] using wordTrace_append hprefix tailTrace_1885254
  have hstable : (prefixWord ++ tailWord_1885254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885254).length < 2 ^ (prefixWord ++ tailWord_1885254).sum := by decide
  have hdescent : baseEnd_1885254 < baseStart_1885254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885313 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_1885313 : Nat := 118140960795 + 1885313 * 2 ^ 59
def prefixEnd_1885313 : Nat := 4983230072969 + 3 ^ 40 * 1885313 * 2
def baseEnd_1885313 : Nat := 430254112520038861296493

theorem tailTrace_1885313 : CollatzResearch.WordTrace tailWord_1885313 prefixEnd_1885313 430254112520038861296493 := by
  unfold tailWord_1885313
  simp only [CollatzResearch.WordTrace]
  refine ⟨68763014218840461670908593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45842009479226974447272395 68763014218840461670908593)
  ·
    refine ⟨51572260664130346253181445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68763014218840461670908593 51572260664130346253181445)
    ·
      refine ⟨9669798874524439922471521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51572260664130346253181445 9669798874524439922471521)
      ·
        refine ⟨7252349155893329941853641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9669798874524439922471521 7252349155893329941853641)
        ·
          refine ⟨5439261866919997456390231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7252349155893329941853641 5439261866919997456390231)
          ·
            refine ⟨8158892800379996184585347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439261866919997456390231 8158892800379996184585347)
            ·
              refine ⟨12238339200569994276878021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158892800379996184585347 12238339200569994276878021)
              ·
                refine ⟨2294688600106873926914629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12238339200569994276878021 2294688600106873926914629)
                ·
                  refine ⟨430254112520038861296493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294688600106873926914629 430254112520038861296493)
                  ·
                    rfl

theorem cell21_1885313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_1885313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885313 prefixEnd_1885313 := by exact prefixLift 1885313
  have htrace : WordTrace (prefixWord ++ tailWord_1885313) baseStart_1885313 baseEnd_1885313 := by
    simpa [prefixWord, tailWord_1885313, baseEnd_1885313] using wordTrace_append hprefix tailTrace_1885313
  have hstable : (prefixWord ++ tailWord_1885313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885313).length < 2 ^ (prefixWord ++ tailWord_1885313).sum := by decide
  have hdescent : baseEnd_1885313 < baseStart_1885313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885316 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1885316 : Nat := 118140960795 + 1885316 * 2 ^ 59
def prefixEnd_1885316 : Nat := 4983230072969 + 3 ^ 40 * 1885316 * 2
def baseEnd_1885316 : Nat := 430254797160911522746487

theorem tailTrace_1885316 : CollatzResearch.WordTrace tailWord_1885316 prefixEnd_1885316 430254797160911522746487 := by
  unfold tailWord_1885316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34381561818914796591633901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45842082425219728788845201 34381561818914796591633901)
  ·
    refine ⟨12893085682093048721862713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34381561818914796591633901 12893085682093048721862713)
    ·
      refine ⟨9669814261569786541397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12893085682093048721862713 9669814261569786541397035)
      ·
        refine ⟨14504721392354679812095553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9669814261569786541397035 14504721392354679812095553)
        ·
          refine ⟨10878541044266009859071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14504721392354679812095553 10878541044266009859071665)
          ·
            refine ⟨8158905783199507394303749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878541044266009859071665 8158905783199507394303749)
            ·
              refine ⟨1529794834349907636431953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8158905783199507394303749 1529794834349907636431953)
              ·
                refine ⟨1147346125762430727323965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529794834349907636431953 1147346125762430727323965)
                ·
                  refine ⟨430254797160911522746487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147346125762430727323965 430254797160911522746487)
                  ·
                    rfl

theorem cell21_1885316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1885316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885316 prefixEnd_1885316 := by exact prefixLift 1885316
  have htrace : WordTrace (prefixWord ++ tailWord_1885316) baseStart_1885316 baseEnd_1885316 := by
    simpa [prefixWord, tailWord_1885316, baseEnd_1885316] using wordTrace_append hprefix tailTrace_1885316
  have hstable : (prefixWord ++ tailWord_1885316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885316).length < 2 ^ (prefixWord ++ tailWord_1885316).sum := by decide
  have hdescent : baseEnd_1885316 < baseStart_1885316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885479 : List Nat := [1, 1, 8, 11]
def baseStart_1885479 : Nat := 118140960795 + 1885479 * 2 ^ 59
def prefixEnd_1885479 : Nat := 4983230072969 + 3 ^ 40 * 1885479 * 2
def baseEnd_1885479 : Nat := 1770748954657034821109

theorem tailTrace_1885479 : CollatzResearch.WordTrace tailWord_1885479 prefixEnd_1885479 1770748954657034821109 := by
  unfold tailWord_1885479
  simp only [CollatzResearch.WordTrace]
  refine ⟨68769068736239072021451491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45846045824159381347634327 68769068736239072021451491)
  ·
    refine ⟨103153603104358608032177237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68769068736239072021451491 103153603104358608032177237)
    ·
      refine ⟨1208831286379202437877077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 103153603104358608032177237 1208831286379202437877077)
      ·
        refine ⟨1770748954657034821109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1208831286379202437877077 1770748954657034821109)
        ·
          rfl

theorem cell21_1885479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 11].length) (baseStart_1885479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885479 prefixEnd_1885479 := by exact prefixLift 1885479
  have htrace : WordTrace (prefixWord ++ tailWord_1885479) baseStart_1885479 baseEnd_1885479 := by
    simpa [prefixWord, tailWord_1885479, baseEnd_1885479] using wordTrace_append hprefix tailTrace_1885479
  have hstable : (prefixWord ++ tailWord_1885479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885479).length < 2 ^ (prefixWord ++ tailWord_1885479).sum := by decide
  have hdescent : baseEnd_1885479 < baseStart_1885479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885482 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1885482 : Nat := 118140960795 + 1885482 * 2 ^ 59
def prefixEnd_1885482 : Nat := 4983230072969 + 3 ^ 40 * 1885482 * 2
def baseEnd_1885482 : Nat := 430292680622532122979481

theorem tailTrace_1885482 : CollatzResearch.WordTrace tailWord_1885482 prefixEnd_1885482 430292680622532122979481 := by
  unfold tailWord_1885482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192294538807050883452675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45846118770152135689207133 17192294538807050883452675)
  ·
    refine ⟨25788441808210576325179013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17192294538807050883452675 25788441808210576325179013)
    ·
      refine ⟨4835332839039483060971065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25788441808210576325179013 4835332839039483060971065)
      ·
        refine ⟨3626499629279612295728299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835332839039483060971065 3626499629279612295728299)
        ·
          refine ⟨5439749443919418443592449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626499629279612295728299 5439749443919418443592449)
          ·
            refine ⟨4079812082939563832694337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439749443919418443592449 4079812082939563832694337)
            ·
              refine ⟨3059859062204672874520753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079812082939563832694337 3059859062204672874520753)
              ·
                refine ⟨2294894296653504655890565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059859062204672874520753 2294894296653504655890565)
                ·
                  refine ⟨430292680622532122979481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294894296653504655890565 430292680622532122979481)
                  ·
                    rfl

theorem cell21_1885482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1885482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885482 prefixEnd_1885482 := by exact prefixLift 1885482
  have htrace : WordTrace (prefixWord ++ tailWord_1885482) baseStart_1885482 baseEnd_1885482 := by
    simpa [prefixWord, tailWord_1885482, baseEnd_1885482] using wordTrace_append hprefix tailTrace_1885482
  have hstable : (prefixWord ++ tailWord_1885482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885482).length < 2 ^ (prefixWord ++ tailWord_1885482).sum := by decide
  have hdescent : baseEnd_1885482 < baseStart_1885482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885485 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1885485 : Nat := 118140960795 + 1885485 * 2 ^ 59
def prefixEnd_1885485 : Nat := 4983230072969 + 3 ^ 40 * 1885485 * 2
def baseEnd_1885485 : Nat := 430293365263404784429475

theorem tailTrace_1885485 : CollatzResearch.WordTrace tailWord_1885485 prefixEnd_1885485 430293365263404784429475 := by
  unfold tailWord_1885485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68769287574217335046169909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45846191716144890030779939 68769287574217335046169909)
  ·
    refine ⟨6447120710082875160578429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68769287574217335046169909 6447120710082875160578429)
    ·
      refine ⟨2417670266281078185216911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6447120710082875160578429 2417670266281078185216911)
      ·
        refine ⟨3626505399421617277825367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417670266281078185216911 3626505399421617277825367)
        ·
          refine ⟨5439758099132425916738051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626505399421617277825367 5439758099132425916738051)
          ·
            refine ⟨8159637148698638875107077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439758099132425916738051 8159637148698638875107077)
            ·
              refine ⟨1529931965380994789082577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8159637148698638875107077 1529931965380994789082577)
              ·
                refine ⟨1147448974035746091811933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529931965380994789082577 1147448974035746091811933)
                ·
                  refine ⟨430293365263404784429475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147448974035746091811933 430293365263404784429475)
                  ·
                    rfl

theorem cell21_1885485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1885485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885485 prefixEnd_1885485 := by exact prefixLift 1885485
  have htrace : WordTrace (prefixWord ++ tailWord_1885485) baseStart_1885485 baseEnd_1885485 := by
    simpa [prefixWord, tailWord_1885485, baseEnd_1885485] using wordTrace_append hprefix tailTrace_1885485
  have hstable : (prefixWord ++ tailWord_1885485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885485).length < 2 ^ (prefixWord ++ tailWord_1885485).sum := by decide
  have hdescent : baseEnd_1885485 < baseStart_1885485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885507 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_1885507 : Nat := 118140960795 + 1885507 * 2 ^ 59
def prefixEnd_1885507 : Nat := 4983230072969 + 3 ^ 40 * 1885507 * 2
def baseEnd_1885507 : Nat := 430298385963137635062763

theorem tailTrace_1885507 : CollatzResearch.WordTrace tailWord_1885507 prefixEnd_1885507 430298385963137635062763 := by
  unfold tailWord_1885507
  simp only [CollatzResearch.WordTrace]
  refine ⟨68770089980137632803470775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45846726653425088535647183 68770089980137632803470775)
  ·
    refine ⟨103155134970206449205206163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68770089980137632803470775 103155134970206449205206163)
    ·
      refine ⟨154732702455309673807809245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103155134970206449205206163 154732702455309673807809245)
      ·
        refine ⟨58024763420741127677928467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154732702455309673807809245 58024763420741127677928467)
        ·
          refine ⟨87037145131111691516892701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58024763420741127677928467 87037145131111691516892701)
          ·
            refine ⟨32638929424166884318834763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87037145131111691516892701 32638929424166884318834763)
            ·
              refine ⟨48958394136250326478252145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32638929424166884318834763 48958394136250326478252145)
              ·
                refine ⟨36718795602187744858689109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48958394136250326478252145 36718795602187744858689109)
                ·
                  refine ⟨430298385963137635062763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36718795602187744858689109 430298385963137635062763)
                  ·
                    rfl

theorem cell21_1885507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_1885507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885507 prefixEnd_1885507 := by exact prefixLift 1885507
  have htrace : WordTrace (prefixWord ++ tailWord_1885507) baseStart_1885507 baseEnd_1885507 := by
    simpa [prefixWord, tailWord_1885507, baseEnd_1885507] using wordTrace_append hprefix tailTrace_1885507
  have hstable : (prefixWord ++ tailWord_1885507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885507).length < 2 ^ (prefixWord ++ tailWord_1885507).sum := by decide
  have hdescent : baseEnd_1885507 < baseStart_1885507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885524 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1885524 : Nat := 118140960795 + 1885524 * 2 ^ 59
def prefixEnd_1885524 : Nat := 4983230072969 + 3 ^ 40 * 1885524 * 2
def baseEnd_1885524 : Nat := 430302265594749383279395

theorem tailTrace_1885524 : CollatzResearch.WordTrace tailWord_1885524 prefixEnd_1885524 430302265594749383279395 := by
  unfold tailWord_1885524
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385355010538022353419813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45847140014050696471226417 34385355010538022353419813)
  ·
    refine ⟨6447254064475879191266215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34385355010538022353419813 6447254064475879191266215)
    ·
      refine ⟨9670881096713818786899323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447254064475879191266215 9670881096713818786899323)
      ·
        refine ⟨14506321645070728180348985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670881096713818786899323 14506321645070728180348985)
        ·
          refine ⟨10879741233803046135261739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14506321645070728180348985 10879741233803046135261739)
          ·
            refine ⟨16319611850704569202892609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10879741233803046135261739 16319611850704569202892609)
            ·
              refine ⟨12239708888028426902169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16319611850704569202892609 12239708888028426902169457)
              ·
                refine ⟨9179781666021320176627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239708888028426902169457 9179781666021320176627093)
                ·
                  refine ⟨430302265594749383279395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9179781666021320176627093 430302265594749383279395)
                  ·
                    rfl

theorem cell21_1885524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1885524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885524 prefixEnd_1885524 := by exact prefixLift 1885524
  have htrace : WordTrace (prefixWord ++ tailWord_1885524) baseStart_1885524 baseEnd_1885524 := by
    simpa [prefixWord, tailWord_1885524, baseEnd_1885524] using wordTrace_append hprefix tailTrace_1885524
  have hstable : (prefixWord ++ tailWord_1885524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885524).length < 2 ^ (prefixWord ++ tailWord_1885524).sum := by decide
  have hdescent : baseEnd_1885524 < baseStart_1885524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885527 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 3]
def baseStart_1885527 : Nat := 118140960795 + 1885527 * 2 ^ 59
def prefixEnd_1885527 : Nat := 4983230072969 + 3 ^ 40 * 1885527 * 2
def baseEnd_1885527 : Nat := 430302950235622044729389

theorem tailTrace_1885527 : CollatzResearch.WordTrace tailWord_1885527 prefixEnd_1885527 430302950235622044729389 := by
  unfold tailWord_1885527
  simp only [CollatzResearch.WordTrace]
  refine ⟨68770819440065176219198835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45847212960043450812799223 68770819440065176219198835)
  ·
    refine ⟨103156229160097764328798253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68770819440065176219198835 103156229160097764328798253)
    ·
      refine ⟨38683585935036661623299345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103156229160097764328798253 38683585935036661623299345)
      ·
        refine ⟨29012689451277496217474509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38683585935036661623299345 29012689451277496217474509)
        ·
          refine ⟨10879758544229061081552941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29012689451277496217474509 10879758544229061081552941)
          ·
            refine ⟨4079909454085897905582353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10879758544229061081552941 4079909454085897905582353)
            ·
              refine ⟨3059932090564423429186765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079909454085897905582353 3059932090564423429186765)
              ·
                refine ⟨1147474533961658785945037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059932090564423429186765 1147474533961658785945037)
                ·
                  refine ⟨430302950235622044729389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147474533961658785945037 430302950235622044729389)
                  ·
                    rfl

theorem cell21_1885527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].length) (baseStart_1885527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885527 prefixEnd_1885527 := by exact prefixLift 1885527
  have htrace : WordTrace (prefixWord ++ tailWord_1885527) baseStart_1885527 baseEnd_1885527 := by
    simpa [prefixWord, tailWord_1885527, baseEnd_1885527] using wordTrace_append hprefix tailTrace_1885527
  have hstable : (prefixWord ++ tailWord_1885527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885527).length < 2 ^ (prefixWord ++ tailWord_1885527).sum := by decide
  have hdescent : baseEnd_1885527 < baseStart_1885527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885533 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 4]
def baseStart_1885533 : Nat := 118140960795 + 1885533 * 2 ^ 59
def prefixEnd_1885533 : Nat := 4983230072969 + 3 ^ 40 * 1885533 * 2
def baseEnd_1885533 : Nat := 430304319517367367629377

theorem tailTrace_1885533 : CollatzResearch.WordTrace tailWord_1885533 prefixEnd_1885533 430304319517367367629377 := by
  unfold tailWord_1885533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68771038278043439243917253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45847358852028959495944835 68771038278043439243917253)
  ·
    refine ⟨12894569677133144858234485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68771038278043439243917253 12894569677133144858234485)
    ·
      refine ⟨1208865907231232330459483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12894569677133144858234485 1208865907231232330459483)
      ·
        refine ⟨1813298860846848495689225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208865907231232330459483 1813298860846848495689225)
        ·
          refine ⟨1359974145635136371766919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813298860846848495689225 1359974145635136371766919)
          ·
            refine ⟨2039961218452704557650379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359974145635136371766919 2039961218452704557650379)
            ·
              refine ⟨3059941827679056836475569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039961218452704557650379 3059941827679056836475569)
              ·
                refine ⟨2294956370759292627356677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059941827679056836475569 2294956370759292627356677)
                ·
                  refine ⟨430304319517367367629377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294956370759292627356677 430304319517367367629377)
                  ·
                    rfl

theorem cell21_1885533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_1885533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885533 prefixEnd_1885533 := by exact prefixLift 1885533
  have htrace : WordTrace (prefixWord ++ tailWord_1885533) baseStart_1885533 baseEnd_1885533 := by
    simpa [prefixWord, tailWord_1885533, baseEnd_1885533] using wordTrace_append hprefix tailTrace_1885533
  have hstable : (prefixWord ++ tailWord_1885533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885533).length < 2 ^ (prefixWord ++ tailWord_1885533).sum := by decide
  have hdescent : baseEnd_1885533 < baseStart_1885533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885572 : List Nat := [2, 3, 2, 1, 1, 5, 2, 5]
def baseStart_1885572 : Nat := 118140960795 + 1885572 * 2 ^ 59
def prefixEnd_1885572 : Nat := 4983230072969 + 3 ^ 40 * 1885572 * 2
def baseEnd_1885572 : Nat := 143437739949570655493099

theorem tailTrace_1885572 : CollatzResearch.WordTrace tailWord_1885572 prefixEnd_1885572 143437739949570655493099 := by
  unfold tailWord_1885572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386230362451074452293485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45848307149934765936391313 34386230362451074452293485)
  ·
    refine ⟨12894836385919152919610057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34386230362451074452293485 12894836385919152919610057)
    ·
      refine ⟨9671127289439364689707543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12894836385919152919610057 9671127289439364689707543)
      ·
        refine ⟨14506690934159047034561315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671127289439364689707543 14506690934159047034561315)
        ·
          refine ⟨21760036401238570551841973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14506690934159047034561315 21760036401238570551841973)
          ·
            refine ⟨2040003412616115989235185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21760036401238570551841973 2040003412616115989235185)
            ·
              refine ⟨1530002559462086991926389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040003412616115989235185 1530002559462086991926389)
              ·
                refine ⟨143437739949570655493099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1530002559462086991926389 143437739949570655493099)
                ·
                  rfl

theorem cell21_1885572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_1885572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885572 prefixEnd_1885572 := by exact prefixLift 1885572
  have htrace : WordTrace (prefixWord ++ tailWord_1885572) baseStart_1885572 baseEnd_1885572 := by
    simpa [prefixWord, tailWord_1885572, baseEnd_1885572] using wordTrace_append hprefix tailTrace_1885572
  have hstable : (prefixWord ++ tailWord_1885572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885572).length < 2 ^ (prefixWord ++ tailWord_1885572).sum := by decide
  have hdescent : baseEnd_1885572 < baseStart_1885572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885600 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_1885600 : Nat := 118140960795 + 1885600 * 2 ^ 59
def prefixEnd_1885600 : Nat := 4983230072969 + 3 ^ 40 * 1885600 * 2
def baseEnd_1885600 : Nat := 430319609830190140012573

theorem tailTrace_1885600 : CollatzResearch.WordTrace tailWord_1885600 prefixEnd_1885600 430319609830190140012573 := by
  unfold tailWord_1885600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386740984400354843303127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45848987979200473124404169 34386740984400354843303127)
  ·
    refine ⟨51580111476600532264954691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34386740984400354843303127 51580111476600532264954691)
    ·
      refine ⟨77370167214900798397432037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51580111476600532264954691 77370167214900798397432037)
      ·
        refine ⟨14506906352793899699518507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77370167214900798397432037 14506906352793899699518507)
        ·
          refine ⟨21760359529190849549277761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14506906352793899699518507 21760359529190849549277761)
          ·
            refine ⟨16320269646893137161958321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21760359529190849549277761 16320269646893137161958321)
            ·
              refine ⟨12240202235169852871468741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16320269646893137161958321 12240202235169852871468741)
              ·
                refine ⟨2295037919094347413400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12240202235169852871468741 2295037919094347413400389)
                ·
                  refine ⟨430319609830190140012573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295037919094347413400389 430319609830190140012573)
                  ·
                    rfl

theorem cell21_1885600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_1885600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885600 prefixEnd_1885600 := by exact prefixLift 1885600
  have htrace : WordTrace (prefixWord ++ tailWord_1885600) baseStart_1885600 baseEnd_1885600 := by
    simpa [prefixWord, tailWord_1885600, baseEnd_1885600] using wordTrace_append hprefix tailTrace_1885600
  have hstable : (prefixWord ++ tailWord_1885600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885600).length < 2 ^ (prefixWord ++ tailWord_1885600).sum := by decide
  have hdescent : baseEnd_1885600 < baseStart_1885600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885603 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 3]
def baseStart_1885603 : Nat := 118140960795 + 1885603 * 2 ^ 59
def prefixEnd_1885603 : Nat := 4983230072969 + 3 ^ 40 * 1885603 * 2
def baseEnd_1885603 : Nat := 430320294471062801462567

theorem tailTrace_1885603 : CollatzResearch.WordTrace tailWord_1885603 prefixEnd_1885603 430320294471062801462567 := by
  unfold tailWord_1885603
  simp only [CollatzResearch.WordTrace]
  refine ⟨68773591387789841198965463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45849060925193227465976975 68773591387789841198965463)
  ·
    refine ⟨103160387081684761798448195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68773591387789841198965463 103160387081684761798448195)
    ·
      refine ⟨154740580622527142697672293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103160387081684761798448195 154740580622527142697672293)
      ·
        refine ⟨29013858866723839255813555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154740580622527142697672293 29013858866723839255813555)
        ·
          refine ⟨43520788300085758883720333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29013858866723839255813555 43520788300085758883720333)
          ·
            refine ⟨16320295612532159581395125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43520788300085758883720333 16320295612532159581395125)
            ·
              refine ⟨1530027713674889960755793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16320295612532159581395125 1530027713674889960755793)
              ·
                refine ⟨1147520785256167470566845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530027713674889960755793 1147520785256167470566845)
                ·
                  refine ⟨430320294471062801462567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147520785256167470566845 430320294471062801462567)
                  ·
                    rfl

theorem cell21_1885603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].length) (baseStart_1885603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885603 prefixEnd_1885603 := by exact prefixLift 1885603
  have htrace : WordTrace (prefixWord ++ tailWord_1885603) baseStart_1885603 baseEnd_1885603 := by
    simpa [prefixWord, tailWord_1885603, baseEnd_1885603] using wordTrace_append hprefix tailTrace_1885603
  have hstable : (prefixWord ++ tailWord_1885603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885603).length < 2 ^ (prefixWord ++ tailWord_1885603).sum := by decide
  have hdescent : baseEnd_1885603 < baseStart_1885603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885710 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1885710 : Nat := 118140960795 + 1885710 * 2 ^ 59
def prefixEnd_1885710 : Nat := 4983230072969 + 3 ^ 40 * 1885710 * 2
def baseEnd_1885710 : Nat := 430344713328854393179015

theorem tailTrace_1885710 : CollatzResearch.WordTrace tailWord_1885710 prefixEnd_1885710 430344713328854393179015 := by
  unfold tailWord_1885710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597186749800274809138823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45851662665601465648740389 8597186749800274809138823)
  ·
    refine ⟨12895780124700412213708235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8597186749800274809138823 12895780124700412213708235)
    ·
      refine ⟨19343670187050618320562353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895780124700412213708235 19343670187050618320562353)
      ·
        refine ⟨14507752640287963740421765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19343670187050618320562353 14507752640287963740421765)
        ·
          refine ⟨2720203620053993201329081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14507752640287963740421765 2720203620053993201329081)
          ·
            refine ⟨2040152715040494900996811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720203620053993201329081 2040152715040494900996811)
            ·
              refine ⟨3060229072560742351495217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040152715040494900996811 3060229072560742351495217)
              ·
                refine ⟨2295171804420556763621413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060229072560742351495217 2295171804420556763621413)
                ·
                  refine ⟨430344713328854393179015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295171804420556763621413 430344713328854393179015)
                  ·
                    rfl

theorem cell21_1885710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1885710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885710 prefixEnd_1885710 := by exact prefixLift 1885710
  have htrace : WordTrace (prefixWord ++ tailWord_1885710) baseStart_1885710 baseEnd_1885710 := by
    simpa [prefixWord, tailWord_1885710, baseEnd_1885710] using wordTrace_append hprefix tailTrace_1885710
  have hstable : (prefixWord ++ tailWord_1885710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885710).length < 2 ^ (prefixWord ++ tailWord_1885710).sum := by decide
  have hdescent : baseEnd_1885710 < baseStart_1885710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885831 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 3]
def baseStart_1885831 : Nat := 118140960795 + 1885831 * 2 ^ 59
def prefixEnd_1885831 : Nat := 4983230072969 + 3 ^ 40 * 1885831 * 2
def baseEnd_1885831 : Nat := 430372327177385071662101

theorem tailTrace_1885831 : CollatzResearch.WordTrace tailWord_1885831 prefixEnd_1885831 430372327177385071662101 := by
  unfold tailWord_1885831
  simp only [CollatzResearch.WordTrace]
  refine ⟨68781907230963836138265347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45854604820642557425510231 68781907230963836138265347)
  ·
    refine ⟨103172860846445754207398021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68781907230963836138265347 103172860846445754207398021)
    ·
      refine ⟨19344911408708578913887129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103172860846445754207398021 19344911408708578913887129)
      ·
        refine ⟨14508683556531434185415347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19344911408708578913887129 14508683556531434185415347)
        ·
          refine ⟨21763025334797151278123021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14508683556531434185415347 21763025334797151278123021)
          ·
            refine ⟨8161134500548931729296133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21763025334797151278123021 8161134500548931729296133)
            ·
              refine ⟨1530212718852924699243025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8161134500548931729296133 1530212718852924699243025)
              ·
                refine ⟨1147659539139693524432269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530212718852924699243025 1147659539139693524432269)
                ·
                  refine ⟨430372327177385071662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147659539139693524432269 430372327177385071662101)
                  ·
                    rfl

theorem cell21_1885831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].length) (baseStart_1885831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885831 prefixEnd_1885831 := by exact prefixLift 1885831
  have htrace : WordTrace (prefixWord ++ tailWord_1885831) baseStart_1885831 baseEnd_1885831 := by
    simpa [prefixWord, tailWord_1885831, baseEnd_1885831] using wordTrace_append hprefix tailTrace_1885831
  have hstable : (prefixWord ++ tailWord_1885831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885831).length < 2 ^ (prefixWord ++ tailWord_1885831).sum := by decide
  have hdescent : baseEnd_1885831 < baseStart_1885831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885887 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_1885887 : Nat := 118140960795 + 1885887 * 2 ^ 59
def prefixEnd_1885887 : Nat := 4983230072969 + 3 ^ 40 * 1885887 * 2
def baseEnd_1885887 : Nat := 430385107140341418728653

theorem tailTrace_1885887 : CollatzResearch.WordTrace tailWord_1885887 prefixEnd_1885887 430385107140341418728653 := by
  unfold tailWord_1885887
  simp only [CollatzResearch.WordTrace]
  refine ⟨68783949718760957702303915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45855966479173971801535943 68783949718760957702303915)
  ·
    refine ⟨103175924578141436553455873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68783949718760957702303915 103175924578141436553455873)
    ·
      refine ⟨77381943433606077415091905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103175924578141436553455873 77381943433606077415091905)
      ·
        refine ⟨58036457575204558061318929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77381943433606077415091905 58036457575204558061318929)
        ·
          refine ⟨43527343181403418545989197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58036457575204558061318929 43527343181403418545989197)
          ·
            refine ⟨16322753693026281954745949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43527343181403418545989197 16322753693026281954745949)
            ·
              refine ⟨6121032634884855733029731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16322753693026281954745949 6121032634884855733029731)
              ·
                refine ⟨9181548952327283599544597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121032634884855733029731 9181548952327283599544597)
                ·
                  refine ⟨430385107140341418728653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9181548952327283599544597 430385107140341418728653)
                  ·
                    rfl

theorem cell21_1885887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_1885887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885887 prefixEnd_1885887 := by exact prefixLift 1885887
  have htrace : WordTrace (prefixWord ++ tailWord_1885887) baseStart_1885887 baseEnd_1885887 := by
    simpa [prefixWord, tailWord_1885887, baseEnd_1885887] using wordTrace_append hprefix tailTrace_1885887
  have hstable : (prefixWord ++ tailWord_1885887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885887).length < 2 ^ (prefixWord ++ tailWord_1885887).sum := by decide
  have hdescent : baseEnd_1885887 < baseStart_1885887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885910 : List Nat := [5, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1885910 : Nat := 118140960795 + 1885910 * 2 ^ 59
def prefixEnd_1885910 : Nat := 4983230072969 + 3 ^ 40 * 1885910 * 2
def baseEnd_1885910 : Nat := 143463452017899496615091

theorem tailTrace_1885910 : CollatzResearch.WordTrace tailWord_1885910 prefixEnd_1885910 143463452017899496615091 := by
  unfold tailWord_1885910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299049287354852039399449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45856525731785088420260789 4299049287354852039399449)
  ·
    refine ⟨3224286965516139029549587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299049287354852039399449 3224286965516139029549587)
    ·
      refine ⟨4836430448274208544324381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224286965516139029549587 4836430448274208544324381)
      ·
        refine ⟨1813661418102828204121643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4836430448274208544324381 1813661418102828204121643)
        ·
          refine ⟨2720492127154242306182465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813661418102828204121643 2720492127154242306182465)
          ·
            refine ⟨2040369095365681729636849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720492127154242306182465 2040369095365681729636849)
            ·
              refine ⟨1530276821524261297227637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040369095365681729636849 1530276821524261297227637)
              ·
                refine ⟨143463452017899496615091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1530276821524261297227637 143463452017899496615091)
                ·
                  rfl

theorem cell21_1885910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1885910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885910 prefixEnd_1885910 := by exact prefixLift 1885910
  have htrace : WordTrace (prefixWord ++ tailWord_1885910) baseStart_1885910 baseEnd_1885910 := by
    simpa [prefixWord, tailWord_1885910, baseEnd_1885910] using wordTrace_append hprefix tailTrace_1885910
  have hstable : (prefixWord ++ tailWord_1885910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885910).length < 2 ^ (prefixWord ++ tailWord_1885910).sum := by decide
  have hdescent : baseEnd_1885910 < baseStart_1885910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885932 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1885932 : Nat := 118140960795 + 1885932 * 2 ^ 59
def prefixEnd_1885932 : Nat := 4983230072969 + 3 ^ 40 * 1885932 * 2
def baseEnd_1885932 : Nat := 430395376753431340478561

theorem tailTrace_1885932 : CollatzResearch.WordTrace tailWord_1885932 prefixEnd_1885932 430395376753431340478561 := by
  unfold tailWord_1885932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34392795501798965193846025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45857060669065286925128033 34392795501798965193846025)
  ·
    refine ⟨25794596626349223895384519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34392795501798965193846025 25794596626349223895384519)
    ·
      refine ⟨38691894939523835843076779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25794596626349223895384519 38691894939523835843076779)
      ·
        refine ⟨58037842409285753764615169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38691894939523835843076779 58037842409285753764615169)
        ·
          refine ⟨43528381806964315323461377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58037842409285753764615169 43528381806964315323461377)
          ·
            refine ⟨32646286355223236492596033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43528381806964315323461377 32646286355223236492596033)
            ·
              refine ⟨24484714766417427369447025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32646286355223236492596033 24484714766417427369447025)
              ·
                refine ⟨18363536074813070527085269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24484714766417427369447025 18363536074813070527085269)
                ·
                  refine ⟨430395376753431340478561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18363536074813070527085269 430395376753431340478561)
                  ·
                    rfl

theorem cell21_1885932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1885932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1885932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1885932 prefixEnd_1885932 := by exact prefixLift 1885932
  have htrace : WordTrace (prefixWord ++ tailWord_1885932) baseStart_1885932 baseEnd_1885932 := by
    simpa [prefixWord, tailWord_1885932, baseEnd_1885932] using wordTrace_append hprefix tailTrace_1885932
  have hstable : (prefixWord ++ tailWord_1885932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885932).length < 2 ^ (prefixWord ++ tailWord_1885932).sum := by decide
  have hdescent : baseEnd_1885932 < baseStart_1885932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886042 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_1886042 : Nat := 118140960795 + 1886042 * 2 ^ 59
def prefixEnd_1886042 : Nat := 4983230072969 + 3 ^ 40 * 1886042 * 2
def baseEnd_1886042 : Nat := 430420480252095593645003

theorem tailTrace_1886042 : CollatzResearch.WordTrace tailWord_1886042 prefixEnd_1886042 430420480252095593645003 := by
  unfold tailWord_1886042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197400758299854793549095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45859735355466279449464253 17197400758299854793549095)
  ·
    refine ⟨25796101137449782190323643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17197400758299854793549095 25796101137449782190323643)
    ·
      refine ⟨38694151706174673285485465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25796101137449782190323643 38694151706174673285485465)
      ·
        refine ⟨29020613779631004964114099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38694151706174673285485465 29020613779631004964114099)
        ·
          refine ⟨43530920669446507446171149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29020613779631004964114099 43530920669446507446171149)
          ·
            refine ⟨16324095251042440292314181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43530920669446507446171149 16324095251042440292314181)
            ·
              refine ⟨3060767859570457554808909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16324095251042440292314181 3060767859570457554808909)
              ·
                refine ⟨1147787947338921583053341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060767859570457554808909 1147787947338921583053341)
                ·
                  refine ⟨430420480252095593645003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147787947338921583053341 430420480252095593645003)
                  ·
                    rfl

theorem cell21_1886042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_1886042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886042 prefixEnd_1886042 := by exact prefixLift 1886042
  have htrace : WordTrace (prefixWord ++ tailWord_1886042) baseStart_1886042 baseEnd_1886042 := by
    simpa [prefixWord, tailWord_1886042, baseEnd_1886042] using wordTrace_append hprefix tailTrace_1886042
  have hstable : (prefixWord ++ tailWord_1886042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886042).length < 2 ^ (prefixWord ++ tailWord_1886042).sum := by decide
  have hdescent : baseEnd_1886042 < baseStart_1886042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886104 : List Nat := [2, 1, 2, 6, 2, 1, 7]
def baseStart_1886104 : Nat := 118140960795 + 1886104 * 2 ^ 59
def prefixEnd_1886104 : Nat := 4983230072969 + 3 ^ 40 * 1886104 * 2
def baseEnd_1886104 : Nat := 47826069944088584845727

theorem tailTrace_1886104 : CollatzResearch.WordTrace tailWord_1886104 prefixEnd_1886104 47826069944088584845727 := by
  unfold tailWord_1886104
  simp only [CollatzResearch.WordTrace]
  refine ⟨34395932179487401881476683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45861242905983202508635577 34395932179487401881476683)
  ·
    refine ⟨51593898269231102822215025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34395932179487401881476683 51593898269231102822215025)
    ·
      refine ⟨38695423701923327116661269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51593898269231102822215025 38695423701923327116661269)
      ·
        refine ⟨1813847986027655958593497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38695423701923327116661269 1813847986027655958593497)
        ·
          refine ⟨1360385989520741968945123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813847986027655958593497 1360385989520741968945123)
          ·
            refine ⟨2040578984281112953417685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360385989520741968945123 2040578984281112953417685)
            ·
              refine ⟨47826069944088584845727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2040578984281112953417685 47826069944088584845727)
              ·
                rfl

theorem cell21_1886104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 7].length) (baseStart_1886104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886104 prefixEnd_1886104 := by exact prefixLift 1886104
  have htrace : WordTrace (prefixWord ++ tailWord_1886104) baseStart_1886104 baseEnd_1886104 := by
    simpa [prefixWord, tailWord_1886104, baseEnd_1886104] using wordTrace_append hprefix tailTrace_1886104
  have hstable : (prefixWord ++ tailWord_1886104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886104).length < 2 ^ (prefixWord ++ tailWord_1886104).sum := by decide
  have hdescent : baseEnd_1886104 < baseStart_1886104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886115 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_1886115 : Nat := 118140960795 + 1886115 * 2 ^ 59
def prefixEnd_1886115 : Nat := 4983230072969 + 3 ^ 40 * 1886115 * 2
def baseEnd_1886115 : Nat := 430437139846663688928187

theorem tailTrace_1886115 : CollatzResearch.WordTrace tailWord_1886115 prefixEnd_1886115 430437139846663688928187 := by
  unfold tailWord_1886115
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792265561934952641603799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45861510374623301761069199 68792265561934952641603799)
  ·
    refine ⟨103188398342902428962405699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68792265561934952641603799 103188398342902428962405699)
    ·
      refine ⟨154782597514353643443608549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103188398342902428962405699 154782597514353643443608549)
      ·
        refine ⟨29021737033941308145676603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154782597514353643443608549 29021737033941308145676603)
        ·
          refine ⟨43532605550911962218514905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29021737033941308145676603 43532605550911962218514905)
          ·
            refine ⟨32649454163183971663886179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43532605550911962218514905 32649454163183971663886179)
            ·
              refine ⟨48974181244775957495829269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32649454163183971663886179 48974181244775957495829269)
              ·
                refine ⟨2295664745848873007616997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48974181244775957495829269 2295664745848873007616997)
                ·
                  refine ⟨430437139846663688928187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295664745848873007616997 430437139846663688928187)
                  ·
                    rfl

theorem cell21_1886115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_1886115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886115 prefixEnd_1886115 := by exact prefixLift 1886115
  have htrace : WordTrace (prefixWord ++ tailWord_1886115) baseStart_1886115 baseEnd_1886115 := by
    simpa [prefixWord, tailWord_1886115, baseEnd_1886115] using wordTrace_append hprefix tailTrace_1886115
  have hstable : (prefixWord ++ tailWord_1886115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886115).length < 2 ^ (prefixWord ++ tailWord_1886115).sum := by decide
  have hdescent : baseEnd_1886115 < baseStart_1886115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886166 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1886166 : Nat := 118140960795 + 1886166 * 2 ^ 59
def prefixEnd_1886166 : Nat := 4983230072969 + 3 ^ 40 * 1886166 * 2
def baseEnd_1886166 : Nat := 430448778741498933578083

theorem tailTrace_1886166 : CollatzResearch.WordTrace tailWord_1886166 prefixEnd_1886166 430448778741498933578083 := by
  unfold tailWord_1886166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299632855296886771981897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45862750456500125567806901 4299632855296886771981897)
  ·
    refine ⟨3224724641472665078986423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299632855296886771981897 3224724641472665078986423)
    ·
      refine ⟨4837086962208997618479635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224724641472665078986423 4837086962208997618479635)
      ·
        refine ⟨7255630443313496427719453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837086962208997618479635 7255630443313496427719453)
        ·
          refine ⟨2720861416242561160394795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7255630443313496427719453 2720861416242561160394795)
          ·
            refine ⟨4081292124363841740592193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720861416242561160394795 4081292124363841740592193)
            ·
              refine ⟨3060969093272881305444145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081292124363841740592193 3060969093272881305444145)
              ·
                refine ⟨2295726819954660979083109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060969093272881305444145 2295726819954660979083109)
                ·
                  refine ⟨430448778741498933578083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295726819954660979083109 430448778741498933578083)
                  ·
                    rfl

theorem cell21_1886166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1886166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886166 prefixEnd_1886166 := by exact prefixLift 1886166
  have htrace : WordTrace (prefixWord ++ tailWord_1886166) baseStart_1886166 baseEnd_1886166 := by
    simpa [prefixWord, tailWord_1886166, baseEnd_1886166] using wordTrace_append hprefix tailTrace_1886166
  have hstable : (prefixWord ++ tailWord_1886166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886166).length < 2 ^ (prefixWord ++ tailWord_1886166).sum := by decide
  have hdescent : baseEnd_1886166 < baseStart_1886166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886191 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_1886191 : Nat := 118140960795 + 1886191 * 2 ^ 59
def prefixEnd_1886191 : Nat := 4983230072969 + 3 ^ 40 * 1886191 * 2
def baseEnd_1886191 : Nat := 430454484082104445661365

theorem tailTrace_1886191 : CollatzResearch.WordTrace tailWord_1886191 prefixEnd_1886191 430454484082104445661365 := by
  unfold tailWord_1886191
  simp only [CollatzResearch.WordTrace]
  refine ⟨68795037509659617621370427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45863358339773078414246951 68795037509659617621370427)
  ·
    refine ⟨103192556264489426432055641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68795037509659617621370427 103192556264489426432055641)
    ·
      refine ⟨77394417198367069824041731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103192556264489426432055641 77394417198367069824041731)
      ·
        refine ⟨116091625797550604736062597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77394417198367069824041731 116091625797550604736062597)
        ·
          refine ⟨21767179837040738388011737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116091625797550604736062597 21767179837040738388011737)
          ·
            refine ⟨16325384877780553791008803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21767179837040738388011737 16325384877780553791008803)
            ·
              refine ⟨24488077316670830686513205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16325384877780553791008803 24488077316670830686513205)
              ·
                refine ⟨2295757248437890376860613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24488077316670830686513205 2295757248437890376860613)
                ·
                  refine ⟨430454484082104445661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295757248437890376860613 430454484082104445661365)
                  ·
                    rfl

theorem cell21_1886191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_1886191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886191 prefixEnd_1886191 := by exact prefixLift 1886191
  have htrace : WordTrace (prefixWord ++ tailWord_1886191) baseStart_1886191 baseEnd_1886191 := by
    simpa [prefixWord, tailWord_1886191, baseEnd_1886191] using wordTrace_append hprefix tailTrace_1886191
  have hstable : (prefixWord ++ tailWord_1886191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886191).length < 2 ^ (prefixWord ++ tailWord_1886191).sum := by decide
  have hdescent : baseEnd_1886191 < baseStart_1886191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886205 : List Nat := [1, 4, 1, 1, 1, 2, 2, 9]
def baseStart_1886205 : Nat := 118140960795 + 1886205 * 2 ^ 59
def prefixEnd_1886205 : Nat := 4983230072969 + 3 ^ 40 * 1886205 * 2
def baseEnd_1886205 : Nat := 143485893024281177476001

theorem tailTrace_1886205 : CollatzResearch.WordTrace tailWord_1886205 prefixEnd_1886205 143485893024281177476001 := by
  unfold tailWord_1886205
  simp only [CollatzResearch.WordTrace]
  refine ⟨68795548131608898012380069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45863698754405932008253379 68795548131608898012380069)
  ·
    refine ⟨12899165274676668377321263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68795548131608898012380069 12899165274676668377321263)
    ·
      refine ⟨19348747912015002565981895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12899165274676668377321263 19348747912015002565981895)
      ·
        refine ⟨29023121868022503848972843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19348747912015002565981895 29023121868022503848972843)
        ·
          refine ⟨43534682802033755773459265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29023121868022503848972843 43534682802033755773459265)
          ·
            refine ⟨32651012101525316830094449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43534682802033755773459265 32651012101525316830094449)
            ·
              refine ⟨24488259076143987622570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32651012101525316830094449 24488259076143987622570837)
              ·
                refine ⟨143485893024281177476001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24488259076143987622570837 143485893024281177476001)
                ·
                  rfl

theorem cell21_1886205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_1886205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886205 prefixEnd_1886205 := by exact prefixLift 1886205
  have htrace : WordTrace (prefixWord ++ tailWord_1886205) baseStart_1886205 baseEnd_1886205 := by
    simpa [prefixWord, tailWord_1886205, baseEnd_1886205] using wordTrace_append hprefix tailTrace_1886205
  have hstable : (prefixWord ++ tailWord_1886205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886205).length < 2 ^ (prefixWord ++ tailWord_1886205).sum := by decide
  have hdescent : baseEnd_1886205 < baseStart_1886205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886301 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1886301 : Nat := 118140960795 + 1886301 * 2 ^ 59
def prefixEnd_1886301 : Nat := 4983230072969 + 3 ^ 40 * 1886301 * 2
def baseEnd_1886301 : Nat := 430479587580768698827807

theorem tailTrace_1886301 : CollatzResearch.WordTrace tailWord_1886301 prefixEnd_1886301 430479587580768698827807 := by
  unfold tailWord_1886301
  simp only [CollatzResearch.WordTrace]
  refine ⟨68799049539261106407874757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45866033026174070938583171 68799049539261106407874757)
  ·
    refine ⟨12899821788611457451476517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68799049539261106407874757 12899821788611457451476517)
    ·
      refine ⟨2418716585364648272151847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12899821788611457451476517 2418716585364648272151847)
      ·
        refine ⟨3628074878046972408227771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418716585364648272151847 3628074878046972408227771)
        ·
          refine ⟨5442112317070458612341657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628074878046972408227771 5442112317070458612341657)
          ·
            refine ⟨4081584237802843959256243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442112317070458612341657 4081584237802843959256243)
            ·
              refine ⟨6122376356704265938884365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081584237802843959256243 6122376356704265938884365)
              ·
                refine ⟨2295891133764099727081637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6122376356704265938884365 2295891133764099727081637)
                ·
                  refine ⟨430479587580768698827807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295891133764099727081637 430479587580768698827807)
                  ·
                    rfl

theorem cell21_1886301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1886301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886301 prefixEnd_1886301 := by exact prefixLift 1886301
  have htrace : WordTrace (prefixWord ++ tailWord_1886301) baseStart_1886301 baseEnd_1886301 := by
    simpa [prefixWord, tailWord_1886301, baseEnd_1886301] using wordTrace_append hprefix tailTrace_1886301
  have hstable : (prefixWord ++ tailWord_1886301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886301).length < 2 ^ (prefixWord ++ tailWord_1886301).sum := by decide
  have hdescent : baseEnd_1886301 < baseStart_1886301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886343 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_1886343 : Nat := 118140960795 + 1886343 * 2 ^ 59
def prefixEnd_1886343 : Nat := 4983230072969 + 3 ^ 40 * 1886343 * 2
def baseEnd_1886343 : Nat := 430489172552985959127721

theorem tailTrace_1886343 : CollatzResearch.WordTrace tailWord_1886343 prefixEnd_1886343 430489172552985959127721 := by
  unfold tailWord_1886343
  simp only [CollatzResearch.WordTrace]
  refine ⟨68800581405108947580903683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45867054270072631720602455 68800581405108947580903683)
  ·
    refine ⟨103200872107663421371355525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68800581405108947580903683 103200872107663421371355525)
    ·
      refine ⟨19350163520186891507129161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103200872107663421371355525 19350163520186891507129161)
      ·
        refine ⟨14512622640140168630346871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19350163520186891507129161 14512622640140168630346871)
        ·
          refine ⟨21768933960210252945520307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512622640140168630346871 21768933960210252945520307)
          ·
            refine ⟨32653400940315379418280461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768933960210252945520307 32653400940315379418280461)
            ·
              refine ⟨12245025352618267281855173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32653400940315379418280461 12245025352618267281855173)
              ·
                refine ⟨2295942253615925115347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12245025352618267281855173 2295942253615925115347845)
                ·
                  refine ⟨430489172552985959127721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295942253615925115347845 430489172552985959127721)
                  ·
                    rfl

theorem cell21_1886343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_1886343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886343 prefixEnd_1886343 := by exact prefixLift 1886343
  have htrace : WordTrace (prefixWord ++ tailWord_1886343) baseStart_1886343 baseEnd_1886343 := by
    simpa [prefixWord, tailWord_1886343, baseEnd_1886343] using wordTrace_append hprefix tailTrace_1886343
  have hstable : (prefixWord ++ tailWord_1886343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886343).length < 2 ^ (prefixWord ++ tailWord_1886343).sum := by decide
  have hdescent : baseEnd_1886343 < baseStart_1886343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886346 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_1886346 : Nat := 118140960795 + 1886346 * 2 ^ 59
def prefixEnd_1886346 : Nat := 4983230072969 + 3 ^ 40 * 1886346 * 2
def baseEnd_1886346 : Nat := 430489857193858620577715

theorem tailTrace_1886346 : CollatzResearch.WordTrace tailWord_1886346 prefixEnd_1886346 430489857193858620577715 := by
  unfold tailWord_1886346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200172706024519773315723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45867127216065386062175261 17200172706024519773315723)
  ·
    refine ⟨25800259059036779659973585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17200172706024519773315723 25800259059036779659973585)
    ·
      refine ⟨19350194294277584744980189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25800259059036779659973585 19350194294277584744980189)
      ·
        refine ⟨7256322860354094279367571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19350194294277584744980189 7256322860354094279367571)
        ·
          refine ⟨10884484290531141419051357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256322860354094279367571 10884484290531141419051357)
          ·
            refine ⟨4081681608949178032144259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10884484290531141419051357 4081681608949178032144259)
            ·
              refine ⟨6122522413423767048216389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081681608949178032144259 6122522413423767048216389)
              ·
                refine ⟨1147972952516956321540573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6122522413423767048216389 1147972952516956321540573)
                ·
                  refine ⟨430489857193858620577715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147972952516956321540573 430489857193858620577715)
                  ·
                    rfl

theorem cell21_1886346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_1886346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886346 prefixEnd_1886346 := by exact prefixLift 1886346
  have htrace : WordTrace (prefixWord ++ tailWord_1886346) baseStart_1886346 baseEnd_1886346 := by
    simpa [prefixWord, tailWord_1886346, baseEnd_1886346] using wordTrace_append hprefix tailTrace_1886346
  have hstable : (prefixWord ++ tailWord_1886346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886346).length < 2 ^ (prefixWord ++ tailWord_1886346).sum := by decide
  have hdescent : baseEnd_1886346 < baseStart_1886346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886405 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 3]
def baseStart_1886405 : Nat := 118140960795 + 1886405 * 2 ^ 59
def prefixEnd_1886405 : Nat := 4983230072969 + 3 ^ 40 * 1886405 * 2
def baseEnd_1886405 : Nat := 430503321797687629094261

theorem tailTrace_1886405 : CollatzResearch.WordTrace tailWord_1886405 prefixEnd_1886405 430503321797687629094261 := by
  unfold tailWord_1886405
  simp only [CollatzResearch.WordTrace]
  refine ⟨68802842730884332169660669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45868561820589554779773779 68802842730884332169660669)
  ·
    refine ⟨25801066024081624563622751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68802842730884332169660669 25801066024081624563622751)
    ·
      refine ⟨38701599036122436845434127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25801066024081624563622751 38701599036122436845434127)
      ·
        refine ⟨58052398554183655268151191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38701599036122436845434127 58052398554183655268151191)
        ·
          refine ⟨87078597831275482902226787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58052398554183655268151191 87078597831275482902226787)
          ·
            refine ⟨130617896746913224353340181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87078597831275482902226787 130617896746913224353340181)
            ·
              refine ⟨6122713910011557391562821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130617896746913224353340181 6122713910011557391562821)
              ·
                refine ⟨1148008858127167010918029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6122713910011557391562821 1148008858127167010918029)
                ·
                  refine ⟨430503321797687629094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148008858127167010918029 430503321797687629094261)
                  ·
                    rfl

theorem cell21_1886405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_1886405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886405 prefixEnd_1886405 := by exact prefixLift 1886405
  have htrace : WordTrace (prefixWord ++ tailWord_1886405) baseStart_1886405 baseEnd_1886405 := by
    simpa [prefixWord, tailWord_1886405, baseEnd_1886405] using wordTrace_append hprefix tailTrace_1886405
  have hstable : (prefixWord ++ tailWord_1886405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886405).length < 2 ^ (prefixWord ++ tailWord_1886405).sum := by decide
  have hdescent : baseEnd_1886405 < baseStart_1886405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886422 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1886422 : Nat := 118140960795 + 1886422 * 2 ^ 59
def prefixEnd_1886422 : Nat := 4983230072969 + 3 ^ 40 * 1886422 * 2
def baseEnd_1886422 : Nat := 430507201429299377310893

theorem tailTrace_1886422 : CollatzResearch.WordTrace tailWord_1886422 prefixEnd_1886422 430507201429299377310893 := by
  unfold tailWord_1886422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300216423238921504564345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45868975181215162715353013 4300216423238921504564345)
  ·
    refine ⟨3225162317429191128423259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4300216423238921504564345 3225162317429191128423259)
    ·
      refine ⟨4837743476143786692634889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225162317429191128423259 4837743476143786692634889)
      ·
        refine ⟨3628307607107840019476167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837743476143786692634889 3628307607107840019476167)
        ·
          refine ⟨5442461410661760029214251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628307607107840019476167 5442461410661760029214251)
          ·
            refine ⟨8163692115992640043821377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442461410661760029214251 8163692115992640043821377)
            ·
              refine ⟨6122769086994480032866033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163692115992640043821377 6122769086994480032866033)
              ·
                refine ⟨4592076815245860024649525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122769086994480032866033 4592076815245860024649525)
                ·
                  refine ⟨430507201429299377310893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4592076815245860024649525 430507201429299377310893)
                  ·
                    rfl

theorem cell21_1886422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1886422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886422 prefixEnd_1886422 := by exact prefixLift 1886422
  have htrace : WordTrace (prefixWord ++ tailWord_1886422) baseStart_1886422 baseEnd_1886422 := by
    simpa [prefixWord, tailWord_1886422, baseEnd_1886422] using wordTrace_append hprefix tailTrace_1886422
  have hstable : (prefixWord ++ tailWord_1886422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886422).length < 2 ^ (prefixWord ++ tailWord_1886422).sum := by decide
  have hdescent : baseEnd_1886422 < baseStart_1886422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886433 : List Nat := [1, 2, 3, 1, 3, 1, 3, 7]
def baseStart_1886433 : Nat := 118140960795 + 1886433 * 2 ^ 59
def prefixEnd_1886433 : Nat := 4983230072969 + 3 ^ 40 * 1886433 * 2
def baseEnd_1886433 : Nat := 143503237259721934209179

theorem tailTrace_1886433 : CollatzResearch.WordTrace tailWord_1886433 prefixEnd_1886433 143503237259721934209179 := by
  unfold tailWord_1886433
  simp only [CollatzResearch.WordTrace]
  refine ⟨68803863974782892951679953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45869242649855261967786635 68803863974782892951679953)
  ·
    refine ⟨51602897981087169713759965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68803863974782892951679953 51602897981087169713759965)
    ·
      refine ⟨19351086742907688642659987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51602897981087169713759965 19351086742907688642659987)
      ·
        refine ⟨29026630114361532963989981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19351086742907688642659987 29026630114361532963989981)
        ·
          refine ⟨10884986292885574861496243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29026630114361532963989981 10884986292885574861496243)
          ·
            refine ⟨16327479439328362292244365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884986292885574861496243 16327479439328362292244365)
            ·
              refine ⟨6122804789748135859591637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16327479439328362292244365 6122804789748135859591637)
              ·
                refine ⟨143503237259721934209179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6122804789748135859591637 143503237259721934209179)
                ·
                  rfl

theorem cell21_1886433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_1886433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886433 prefixEnd_1886433 := by exact prefixLift 1886433
  have htrace : WordTrace (prefixWord ++ tailWord_1886433) baseStart_1886433 baseEnd_1886433 := by
    simpa [prefixWord, tailWord_1886433, baseEnd_1886433] using wordTrace_append hprefix tailTrace_1886433
  have hstable : (prefixWord ++ tailWord_1886433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886433).length < 2 ^ (prefixWord ++ tailWord_1886433).sum := by decide
  have hdescent : baseEnd_1886433 < baseStart_1886433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886439 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 3]
def baseStart_1886439 : Nat := 118140960795 + 1886439 * 2 ^ 59
def prefixEnd_1886439 : Nat := 4983230072969 + 3 ^ 40 * 1886439 * 2
def baseEnd_1886439 : Nat := 430511081060911125527525

theorem tailTrace_1886439 : CollatzResearch.WordTrace tailWord_1886439 prefixEnd_1886439 430511081060911125527525 := by
  unfold tailWord_1886439
  simp only [CollatzResearch.WordTrace]
  refine ⟨68804082812761155976398371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45869388541840770650932247 68804082812761155976398371)
  ·
    refine ⟨103206124219141733964597557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68804082812761155976398371 103206124219141733964597557)
    ·
      refine ⟨9675574145544537559181021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103206124219141733964597557 9675574145544537559181021)
      ·
        refine ⟨3628340304579201584692883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9675574145544537559181021 3628340304579201584692883)
        ·
          refine ⟨5442510456868802377039325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628340304579201584692883 5442510456868802377039325)
          ·
            refine ⟨2040941421325800891389747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5442510456868802377039325 2040941421325800891389747)
            ·
              refine ⟨3061412131988701337084621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040941421325800891389747 3061412131988701337084621)
              ·
                refine ⟨1148029549495763001406733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3061412131988701337084621 1148029549495763001406733)
                ·
                  refine ⟨430511081060911125527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148029549495763001406733 430511081060911125527525)
                  ·
                    rfl

theorem cell21_1886439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].length) (baseStart_1886439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886439 prefixEnd_1886439 := by exact prefixLift 1886439
  have htrace : WordTrace (prefixWord ++ tailWord_1886439) baseStart_1886439 baseEnd_1886439 := by
    simpa [prefixWord, tailWord_1886439, baseEnd_1886439] using wordTrace_append hprefix tailTrace_1886439
  have hstable : (prefixWord ++ tailWord_1886439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886439).length < 2 ^ (prefixWord ++ tailWord_1886439).sum := by decide
  have hdescent : baseEnd_1886439 < baseStart_1886439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886450 : List Nat := [3, 2, 1, 3, 2, 3, 7]
def baseStart_1886450 : Nat := 118140960795 + 1886450 * 2 ^ 59
def prefixEnd_1886450 : Nat := 4983230072969 + 3 ^ 40 * 1886450 * 2
def baseEnd_1886450 : Nat := 47834843490086394538241

theorem tailTrace_1886450 : CollatzResearch.WordTrace tailWord_1886450 prefixEnd_1886450 47834843490086394538241 := by
  unfold tailWord_1886450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201121003930326213762201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45869656010480869903365869 17201121003930326213762201)
  ·
    refine ⟨12900840752947744660321651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17201121003930326213762201 12900840752947744660321651)
    ·
      refine ⟨19351261129421616990482477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12900840752947744660321651 19351261129421616990482477)
      ·
        refine ⟨7256722923533106371430929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19351261129421616990482477 7256722923533106371430929)
        ·
          refine ⟨5442542192649829778573197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256722923533106371430929 5442542192649829778573197)
          ·
            refine ⟨2040953322243686166964949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5442542192649829778573197 2040953322243686166964949)
            ·
              refine ⟨47834843490086394538241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2040953322243686166964949 47834843490086394538241)
              ·
                rfl

theorem cell21_1886450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 7].length) (baseStart_1886450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886450 prefixEnd_1886450 := by exact prefixLift 1886450
  have htrace : WordTrace (prefixWord ++ tailWord_1886450) baseStart_1886450 baseEnd_1886450 := by
    simpa [prefixWord, tailWord_1886450, baseEnd_1886450] using wordTrace_append hprefix tailTrace_1886450
  have hstable : (prefixWord ++ tailWord_1886450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886450).length < 2 ^ (prefixWord ++ tailWord_1886450).sum := by decide
  have hdescent : baseEnd_1886450 < baseStart_1886450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886464 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_1886464 : Nat := 118140960795 + 1886464 * 2 ^ 59
def prefixEnd_1886464 : Nat := 4983230072969 + 3 ^ 40 * 1886464 * 2
def baseEnd_1886464 : Nat := 430516786401516637610807

theorem tailTrace_1886464 : CollatzResearch.WordTrace tailWord_1886464 prefixEnd_1886464 430516786401516637610807 := by
  unfold tailWord_1886464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34402497318835292623029223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45869996425113723497372297 34402497318835292623029223)
  ·
    refine ⟨51603745978252938934543835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34402497318835292623029223 51603745978252938934543835)
    ·
      refine ⟨77405618967379408401815753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51603745978252938934543835 77405618967379408401815753)
      ·
        refine ⟨58054214225534556301361815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77405618967379408401815753 58054214225534556301361815)
        ·
          refine ⟨87081321338301834452042723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58054214225534556301361815 87081321338301834452042723)
          ·
            refine ⟨130621982007452751678064085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87081321338301834452042723 130621982007452751678064085)
            ·
              refine ⟨3061452703299673867454627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130621982007452751678064085 3061452703299673867454627)
              ·
                refine ⟨4592179054949510801181941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061452703299673867454627 4592179054949510801181941)
                ·
                  refine ⟨430516786401516637610807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4592179054949510801181941 430516786401516637610807)
                  ·
                    rfl

theorem cell21_1886464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_1886464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886464 prefixEnd_1886464 := by exact prefixLift 1886464
  have htrace : WordTrace (prefixWord ++ tailWord_1886464) baseStart_1886464 baseEnd_1886464 := by
    simpa [prefixWord, tailWord_1886464, baseEnd_1886464] using wordTrace_append hprefix tailTrace_1886464
  have hstable : (prefixWord ++ tailWord_1886464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886464).length < 2 ^ (prefixWord ++ tailWord_1886464).sum := by decide
  have hdescent : baseEnd_1886464 < baseStart_1886464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886526 : List Nat := [4, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1886526 : Nat := 118140960795 + 1886526 * 2 ^ 59
def prefixEnd_1886526 : Nat := 4983230072969 + 3 ^ 40 * 1886526 * 2
def baseEnd_1886526 : Nat := 143510311882072769192449

theorem tailTrace_1886526 : CollatzResearch.WordTrace tailWord_1886526 prefixEnd_1886526 143510311882072769192449 := by
  unfold tailWord_1886526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600906995430746229351929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45871503975630646556543621 8600906995430746229351929)
  ·
    refine ⟨6450680246573059672013947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8600906995430746229351929 6450680246573059672013947)
    ·
      refine ⟨9676020369859589508020921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450680246573059672013947 9676020369859589508020921)
      ·
        refine ⟨7257015277394692131015691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9676020369859589508020921 7257015277394692131015691)
        ·
          refine ⟨10885522916092038196523537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257015277394692131015691 10885522916092038196523537)
          ·
            refine ⟨8164142187069028647392653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10885522916092038196523537 8164142187069028647392653)
            ·
              refine ⟨3061553320150885742772245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8164142187069028647392653 3061553320150885742772245)
              ·
                refine ⟨143510311882072769192449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3061553320150885742772245 143510311882072769192449)
                ·
                  rfl

theorem cell21_1886526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1886526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886526 prefixEnd_1886526 := by exact prefixLift 1886526
  have htrace : WordTrace (prefixWord ++ tailWord_1886526) baseStart_1886526 baseEnd_1886526 := by
    simpa [prefixWord, tailWord_1886526, baseEnd_1886526] using wordTrace_append hprefix tailTrace_1886526
  have hstable : (prefixWord ++ tailWord_1886526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886526).length < 2 ^ (prefixWord ++ tailWord_1886526).sum := by decide
  have hdescent : baseEnd_1886526 < baseStart_1886526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886540 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1886540 : Nat := 118140960795 + 1886540 * 2 ^ 59
def prefixEnd_1886540 : Nat := 4983230072969 + 3 ^ 40 * 1886540 * 2
def baseEnd_1886540 : Nat := 430534130636957394343985

theorem tailTrace_1886540 : CollatzResearch.WordTrace tailWord_1886540 prefixEnd_1886540 430534130636957394343985 := by
  unfold tailWord_1886540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403883292697625112912537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45871844390263500150550049 34403883292697625112912537)
  ·
    refine ⟨25802912469523218834684403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34403883292697625112912537 25802912469523218834684403)
    ·
      refine ⟨38704368704284828252026605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25802912469523218834684403 38704368704284828252026605)
      ·
        refine ⟨14514138264106810594509977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38704368704284828252026605 14514138264106810594509977)
        ·
          refine ⟨10885603698080107945882483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14514138264106810594509977 10885603698080107945882483)
          ·
            refine ⟨16328405547120161918823725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885603698080107945882483 16328405547120161918823725)
            ·
              refine ⟨6123152080170060719558897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16328405547120161918823725 6123152080170060719558897)
              ·
                refine ⟨4592364060127545539669173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123152080170060719558897 4592364060127545539669173)
                ·
                  refine ⟨430534130636957394343985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4592364060127545539669173 430534130636957394343985)
                  ·
                    rfl

theorem cell21_1886540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1886540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886540 prefixEnd_1886540 := by exact prefixLift 1886540
  have htrace : WordTrace (prefixWord ++ tailWord_1886540) baseStart_1886540 baseEnd_1886540 := by
    simpa [prefixWord, tailWord_1886540, baseEnd_1886540] using wordTrace_append hprefix tailTrace_1886540
  have hstable : (prefixWord ++ tailWord_1886540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886540).length < 2 ^ (prefixWord ++ tailWord_1886540).sum := by decide
  have hdescent : baseEnd_1886540 < baseStart_1886540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886554 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1886554 : Nat := 118140960795 + 1886554 * 2 ^ 59
def prefixEnd_1886554 : Nat := 4983230072969 + 3 ^ 40 * 1886554 * 2
def baseEnd_1886554 : Nat := 430537325627696481110623

theorem tailTrace_1886554 : CollatzResearch.WordTrace tailWord_1886554 prefixEnd_1886554 430537325627696481110623 := by
  unfold tailWord_1886554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202069301836132654208679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45872184804896353744556477 17202069301836132654208679)
  ·
    refine ⟨25803103952754198981313019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17202069301836132654208679 25803103952754198981313019)
    ·
      refine ⟨38704655929131298471969529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25803103952754198981313019 38704655929131298471969529)
      ·
        refine ⟨29028491946848473853977147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38704655929131298471969529 29028491946848473853977147)
        ·
          refine ⟨43542737920272710780965721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29028491946848473853977147 43542737920272710780965721)
          ·
            refine ⟨32657053440204533085724291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43542737920272710780965721 32657053440204533085724291)
            ·
              refine ⟨48985580160306799628586437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32657053440204533085724291 48985580160306799628586437)
              ·
                refine ⟨9184796280057524930359957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48985580160306799628586437 9184796280057524930359957)
                ·
                  refine ⟨430537325627696481110623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9184796280057524930359957 430537325627696481110623)
                  ·
                    rfl

theorem cell21_1886554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1886554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886554 prefixEnd_1886554 := by exact prefixLift 1886554
  have htrace : WordTrace (prefixWord ++ tailWord_1886554) baseStart_1886554 baseEnd_1886554 := by
    simpa [prefixWord, tailWord_1886554, baseEnd_1886554] using wordTrace_append hprefix tailTrace_1886554
  have hstable : (prefixWord ++ tailWord_1886554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886554).length < 2 ^ (prefixWord ++ tailWord_1886554).sum := by decide
  have hdescent : baseEnd_1886554 < baseStart_1886554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886647 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_1886647 : Nat := 118140960795 + 1886647 * 2 ^ 59
def prefixEnd_1886647 : Nat := 4983230072969 + 3 ^ 40 * 1886647 * 2
def baseEnd_1886647 : Nat := 430558549494748986060433

theorem tailTrace_1886647 : CollatzResearch.WordTrace tailWord_1886647 prefixEnd_1886647 430558549494748986060433 := by
  unfold tailWord_1886647
  simp only [CollatzResearch.WordTrace]
  refine ⟨68811669196007607499970195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45874446130671738333313463 68811669196007607499970195)
  ·
    refine ⟨103217503794011411249955293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68811669196007607499970195 103217503794011411249955293)
    ·
      refine ⟨38706563922754279218733235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103217503794011411249955293 38706563922754279218733235)
      ·
        refine ⟨58059845884131418828099853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38706563922754279218733235 58059845884131418828099853)
        ·
          refine ⟨21772442206549282060537445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58059845884131418828099853 21772442206549282060537445)
          ·
            refine ⟨4082332913727990386350771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21772442206549282060537445 4082332913727990386350771)
            ·
              refine ⟨6123499370591985579526157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082332913727990386350771 6123499370591985579526157)
              ·
                refine ⟨2296312263971994592322309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6123499370591985579526157 2296312263971994592322309)
                ·
                  refine ⟨430558549494748986060433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296312263971994592322309 430558549494748986060433)
                  ·
                    rfl

theorem cell21_1886647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_1886647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886647 prefixEnd_1886647 := by exact prefixLift 1886647
  have htrace : WordTrace (prefixWord ++ tailWord_1886647) baseStart_1886647 baseEnd_1886647 := by
    simpa [prefixWord, tailWord_1886647, baseEnd_1886647] using wordTrace_append hprefix tailTrace_1886647
  have hstable : (prefixWord ++ tailWord_1886647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886647).length < 2 ^ (prefixWord ++ tailWord_1886647).sum := by decide
  have hdescent : baseEnd_1886647 < baseStart_1886647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886740 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1886740 : Nat := 118140960795 + 1886740 * 2 ^ 59
def prefixEnd_1886740 : Nat := 4983230072969 + 3 ^ 40 * 1886740 * 2
def baseEnd_1886740 : Nat := 430579773361801491010243

theorem tailTrace_1886740 : CollatzResearch.WordTrace tailWord_1886740 prefixEnd_1886740 430579773361801491010243 := by
  unfold tailWord_1886740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407530592335342191552837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45876707456447122922070449 34407530592335342191552837)
  ·
    refine ⟨6451411986062876660916157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34407530592335342191552837 6451411986062876660916157)
    ·
      refine ⟨2419279494773578747843559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6451411986062876660916157 2419279494773578747843559)
      ·
        refine ⟨3628919242160368121765339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419279494773578747843559 3628919242160368121765339)
        ·
          refine ⟨5443378863240552182648009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628919242160368121765339 5443378863240552182648009)
          ·
            refine ⟨4082534147430414136986007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443378863240552182648009 4082534147430414136986007)
            ·
              refine ⟨6123801221145621205479011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082534147430414136986007 6123801221145621205479011)
              ·
                refine ⟨9185701831718431808218517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123801221145621205479011 9185701831718431808218517)
                ·
                  refine ⟨430579773361801491010243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9185701831718431808218517 430579773361801491010243)
                  ·
                    rfl

theorem cell21_1886740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1886740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886740 prefixEnd_1886740 := by exact prefixLift 1886740
  have htrace : WordTrace (prefixWord ++ tailWord_1886740) baseStart_1886740 baseEnd_1886740 := by
    simpa [prefixWord, tailWord_1886740, baseEnd_1886740] using wordTrace_append hprefix tailTrace_1886740
  have hstable : (prefixWord ++ tailWord_1886740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886740).length < 2 ^ (prefixWord ++ tailWord_1886740).sum := by decide
  have hdescent : baseEnd_1886740 < baseStart_1886740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886788 : List Nat := [2, 3, 5, 1, 1, 2, 7]
def baseStart_1886788 : Nat := 118140960795 + 1886788 * 2 ^ 59
def prefixEnd_1886788 : Nat := 4983230072969 + 3 ^ 40 * 1886788 * 2
def baseEnd_1886788 : Nat := 47843414179529341578905

theorem tailTrace_1886788 : CollatzResearch.WordTrace tailWord_1886788 prefixEnd_1886788 47843414179529341578905 := by
  unfold tailWord_1886788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408405944248394290426509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45877874592331192387235345 34408405944248394290426509)
  ·
    refine ⟨12903152229093147858909941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34408405944248394290426509 12903152229093147858909941)
    ·
      refine ⟨1209670521477482611772807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12903152229093147858909941 1209670521477482611772807)
      ·
        refine ⟨1814505782216223917659211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209670521477482611772807 1814505782216223917659211)
        ·
          refine ⟨2721758673324335876488817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814505782216223917659211 2721758673324335876488817)
          ·
            refine ⟨2041319004993251907366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721758673324335876488817 2041319004993251907366613)
            ·
              refine ⟨47843414179529341578905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2041319004993251907366613 47843414179529341578905)
              ·
                rfl

theorem cell21_1886788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 7].length) (baseStart_1886788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886788 prefixEnd_1886788 := by exact prefixLift 1886788
  have htrace : WordTrace (prefixWord ++ tailWord_1886788) baseStart_1886788 baseEnd_1886788 := by
    simpa [prefixWord, tailWord_1886788, baseEnd_1886788] using wordTrace_append hprefix tailTrace_1886788
  have hstable : (prefixWord ++ tailWord_1886788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886788).length < 2 ^ (prefixWord ++ tailWord_1886788).sum := by decide
  have hdescent : baseEnd_1886788 < baseStart_1886788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886802 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1886802 : Nat := 118140960795 + 1886802 * 2 ^ 59
def prefixEnd_1886802 : Nat := 4983230072969 + 3 ^ 40 * 1886802 * 2
def baseEnd_1886802 : Nat := 430593922606503160976783

theorem tailTrace_1886802 : CollatzResearch.WordTrace tailWord_1886802 prefixEnd_1886802 430593922606503160976783 := by
  unfold tailWord_1886802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17204330627611517242965665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45878215006964045981241773 17204330627611517242965665)
  ·
    refine ⟨12903247970708637932224249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17204330627611517242965665 12903247970708637932224249)
    ·
      refine ⟨9677435978031478449168187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12903247970708637932224249 9677435978031478449168187)
      ·
        refine ⟨14516153967047217673752281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9677435978031478449168187 14516153967047217673752281)
        ·
          refine ⟨10887115475285413255314211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14516153967047217673752281 10887115475285413255314211)
          ·
            refine ⟨16330673212928119882971317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10887115475285413255314211 16330673212928119882971317)
            ·
              refine ⟨1531000613712011239028561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16330673212928119882971317 1531000613712011239028561)
              ·
                refine ⟨1148250460284008429271421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531000613712011239028561 1148250460284008429271421)
                ·
                  refine ⟨430593922606503160976783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148250460284008429271421 430593922606503160976783)
                  ·
                    rfl

theorem cell21_1886802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1886802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886802 prefixEnd_1886802 := by exact prefixLift 1886802
  have htrace : WordTrace (prefixWord ++ tailWord_1886802) baseStart_1886802 baseEnd_1886802 := by
    simpa [prefixWord, tailWord_1886802, baseEnd_1886802] using wordTrace_append hprefix tailTrace_1886802
  have hstable : (prefixWord ++ tailWord_1886802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886802).length < 2 ^ (prefixWord ++ tailWord_1886802).sum := by decide
  have hdescent : baseEnd_1886802 < baseStart_1886802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886920 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_1886920 : Nat := 118140960795 + 1886920 * 2 ^ 59
def prefixEnd_1886920 : Nat := 4983230072969 + 3 ^ 40 * 1886920 * 2
def baseEnd_1886920 : Nat := 430620851814161178009875

theorem tailTrace_1886920 : CollatzResearch.WordTrace tailWord_1886920 prefixEnd_1886920 430620851814161178009875 := by
  unfold tailWord_1886920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34410813162009287562329107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45881084216012383416438809 34410813162009287562329107)
  ·
    refine ⟨51616219743013931343493661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34410813162009287562329107 51616219743013931343493661)
    ·
      refine ⟨19356082403630224253810123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51616219743013931343493661 19356082403630224253810123)
      ·
        refine ⟨29034123605445336380715185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19356082403630224253810123 29034123605445336380715185)
        ·
          refine ⟨21775592704084002285536389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29034123605445336380715185 21775592704084002285536389)
          ·
            refine ⟨4082923632015750428538073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21775592704084002285536389 4082923632015750428538073)
            ·
              refine ⟨3062192724011812821403555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082923632015750428538073 3062192724011812821403555)
              ·
                refine ⟨4593289086017719232105333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062192724011812821403555 4593289086017719232105333)
                ·
                  refine ⟨430620851814161178009875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593289086017719232105333 430620851814161178009875)
                  ·
                    rfl

theorem cell21_1886920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_1886920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1886920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1886920 prefixEnd_1886920 := by exact prefixLift 1886920
  have htrace : WordTrace (prefixWord ++ tailWord_1886920) baseStart_1886920 baseEnd_1886920 := by
    simpa [prefixWord, tailWord_1886920, baseEnd_1886920] using wordTrace_append hprefix tailTrace_1886920
  have hstable : (prefixWord ++ tailWord_1886920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886920).length < 2 ^ (prefixWord ++ tailWord_1886920).sum := by decide
  have hdescent : baseEnd_1886920 < baseStart_1886920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887027 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_1887027 : Nat := 118140960795 + 1887027 * 2 ^ 59
def prefixEnd_1887027 : Nat := 4983230072969 + 3 ^ 40 * 1887027 * 2
def baseEnd_1887027 : Nat := 430645270671952769726323

theorem tailTrace_1887027 : CollatzResearch.WordTrace tailWord_1887027 prefixEnd_1887027 430645270671952769726323 := by
  unfold tailWord_1887027
  simp only [CollatzResearch.WordTrace]
  refine ⟨68825528934630932398803335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45883685956420621599202223 68825528934630932398803335)
  ·
    refine ⟨103238293401946398598205003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68825528934630932398803335 103238293401946398598205003)
    ·
      refine ⟨154857440102919597897307505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103238293401946398598205003 154857440102919597897307505)
      ·
        refine ⟨116143080077189698422980629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154857440102919597897307505 116143080077189698422980629)
        ·
          refine ⟨5444206878618267113577217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116143080077189698422980629 5444206878618267113577217)
          ·
            refine ⟨4083155158963700335182913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444206878618267113577217 4083155158963700335182913)
            ·
              refine ⟨3062366369222775251387185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083155158963700335182913 3062366369222775251387185)
              ·
                refine ⟨2296774776917081438540389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062366369222775251387185 2296774776917081438540389)
                ·
                  refine ⟨430645270671952769726323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296774776917081438540389 430645270671952769726323)
                  ·
                    rfl

theorem cell21_1887027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_1887027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887027 prefixEnd_1887027 := by exact prefixLift 1887027
  have htrace : WordTrace (prefixWord ++ tailWord_1887027) baseStart_1887027 baseEnd_1887027 := by
    simpa [prefixWord, tailWord_1887027, baseEnd_1887027] using wordTrace_append hprefix tailTrace_1887027
  have hstable : (prefixWord ++ tailWord_1887027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887027).length < 2 ^ (prefixWord ++ tailWord_1887027).sum := by decide
  have hdescent : baseEnd_1887027 < baseStart_1887027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887145 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_1887145 : Nat := 118140960795 + 1887145 * 2 ^ 59
def prefixEnd_1887145 : Nat := 4983230072969 + 3 ^ 40 * 1887145 * 2
def baseEnd_1887145 : Nat := 430672199879610786759415

theorem tailTrace_1887145 : CollatzResearch.WordTrace tailWord_1887145 prefixEnd_1887145 430672199879610786759415 := by
  unfold tailWord_1887145
  simp only [CollatzResearch.WordTrace]
  refine ⟨68829832748203438551598889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45886555165468959034399259 68829832748203438551598889)
  ·
    refine ⟨51622374561152578913699167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68829832748203438551598889 51622374561152578913699167)
    ·
      refine ⟨77433561841728868370548751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51622374561152578913699167 77433561841728868370548751)
      ·
        refine ⟨116150342762593302555823127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77433561841728868370548751 116150342762593302555823127)
        ·
          refine ⟨174225514143889953833734691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116150342762593302555823127 174225514143889953833734691)
          ·
            refine ⟨261338271215834930750602037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174225514143889953833734691 261338271215834930750602037)
            ·
              refine ⟨24500462926484524757868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261338271215834930750602037 24500462926484524757868941)
              ·
                refine ⟨9187673597431696784200853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24500462926484524757868941 9187673597431696784200853)
                ·
                  refine ⟨430672199879610786759415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9187673597431696784200853 430672199879610786759415)
                  ·
                    rfl

theorem cell21_1887145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_1887145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887145 prefixEnd_1887145 := by exact prefixLift 1887145
  have htrace : WordTrace (prefixWord ++ tailWord_1887145) baseStart_1887145 baseEnd_1887145 := by
    simpa [prefixWord, tailWord_1887145, baseEnd_1887145] using wordTrace_append hprefix tailTrace_1887145
  have hstable : (prefixWord ++ tailWord_1887145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887145).length < 2 ^ (prefixWord ++ tailWord_1887145).sum := by decide
  have hdescent : baseEnd_1887145 < baseStart_1887145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887162 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1887162 : Nat := 118140960795 + 1887162 * 2 ^ 59
def prefixEnd_1887162 : Nat := 4983230072969 + 3 ^ 40 * 1887162 * 2
def baseEnd_1887162 : Nat := 430676079511222534976047

theorem tailTrace_1887162 : CollatzResearch.WordTrace tailWord_1887162 prefixEnd_1887162 430676079511222534976047 := by
  unfold tailWord_1887162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207613197285462613741935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45886968526094566969978493 17207613197285462613741935)
  ·
    refine ⟨25811419795928193920612903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17207613197285462613741935 25811419795928193920612903)
    ·
      refine ⟨38717129693892290880919355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25811419795928193920612903 38717129693892290880919355)
      ·
        refine ⟨58075694540838436321379033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38717129693892290880919355 58075694540838436321379033)
        ·
          refine ⟨43556770905628827241034275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58075694540838436321379033 43556770905628827241034275)
          ·
            refine ⟨65335156358443240861551413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43556770905628827241034275 65335156358443240861551413)
            ·
              refine ⟨6125170908604053830770445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65335156358443240861551413 6125170908604053830770445)
              ·
                refine ⟨2296939090726520186538917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6125170908604053830770445 2296939090726520186538917)
                ·
                  refine ⟨430676079511222534976047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296939090726520186538917 430676079511222534976047)
                  ·
                    rfl

theorem cell21_1887162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1887162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887162 prefixEnd_1887162 := by exact prefixLift 1887162
  have htrace : WordTrace (prefixWord ++ tailWord_1887162) baseStart_1887162 baseEnd_1887162 := by
    simpa [prefixWord, tailWord_1887162, baseEnd_1887162] using wordTrace_append hprefix tailTrace_1887162
  have hstable : (prefixWord ++ tailWord_1887162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887162).length < 2 ^ (prefixWord ++ tailWord_1887162).sum := by decide
  have hdescent : baseEnd_1887162 < baseStart_1887162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887199 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 3]
def baseStart_1887199 : Nat := 118140960795 + 1887199 * 2 ^ 59
def prefixEnd_1887199 : Nat := 4983230072969 + 3 ^ 40 * 1887199 * 2
def baseEnd_1887199 : Nat := 430684523415318692859305

theorem tailTrace_1887199 : CollatzResearch.WordTrace tailWord_1887199 prefixEnd_1887199 430684523415318692859305 := by
  unfold tailWord_1887199
  simp only [CollatzResearch.WordTrace]
  refine ⟨68831802290007805774064651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45887868193338537182709767 68831802290007805774064651)
  ·
    refine ⟨103247703435011708661096977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68831802290007805774064651 103247703435011708661096977)
    ·
      refine ⟨77435777576258781495822733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103247703435011708661096977 77435777576258781495822733)
      ·
        refine ⟨29038416591097043060933525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77435777576258781495822733 29038416591097043060933525)
        ·
          refine ⟨1361175777707673893481259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29038416591097043060933525 1361175777707673893481259)
          ·
            refine ⟨2041763666561510840221889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361175777707673893481259 2041763666561510840221889)
            ·
              refine ⟨1531322749921133130166417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041763666561510840221889 1531322749921133130166417)
              ·
                refine ⟨1148492062440849847624813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531322749921133130166417 1148492062440849847624813)
                ·
                  refine ⟨430684523415318692859305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148492062440849847624813 430684523415318692859305)
                  ·
                    rfl

theorem cell21_1887199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].length) (baseStart_1887199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887199 prefixEnd_1887199 := by exact prefixLift 1887199
  have htrace : WordTrace (prefixWord ++ tailWord_1887199) baseStart_1887199 baseEnd_1887199 := by
    simpa [prefixWord, tailWord_1887199, baseEnd_1887199] using wordTrace_append hprefix tailTrace_1887199
  have hstable : (prefixWord ++ tailWord_1887199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887199).length < 2 ^ (prefixWord ++ tailWord_1887199).sum := by decide
  have hdescent : baseEnd_1887199 < baseStart_1887199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887255 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_1887255 : Nat := 118140960795 + 1887255 * 2 ^ 59
def prefixEnd_1887255 : Nat := 4983230072969 + 3 ^ 40 * 1887255 * 2
def baseEnd_1887255 : Nat := 430697303378275039925857

theorem tailTrace_1887255 : CollatzResearch.WordTrace tailWord_1887255 prefixEnd_1887255 430697303378275039925857 := by
  unfold tailWord_1887255
  simp only [CollatzResearch.WordTrace]
  refine ⟨68833844777804927338103219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45889229851869951558735479 68833844777804927338103219)
  ·
    refine ⟨103250767166707391007154829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68833844777804927338103219 103250767166707391007154829)
    ·
      refine ⟨38719037687515271627683061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103250767166707391007154829 38719037687515271627683061)
      ·
        refine ⟨3629909783204556715095287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38719037687515271627683061 3629909783204556715095287)
        ·
          refine ⟨5444864674806835072642931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629909783204556715095287 5444864674806835072642931)
          ·
            refine ⟨8167297012210252608964397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444864674806835072642931 8167297012210252608964397)
            ·
              refine ⟨3062736379578844728361649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8167297012210252608964397 3062736379578844728361649)
              ·
                refine ⟨2297052284684133546271237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062736379578844728361649 2297052284684133546271237)
                ·
                  refine ⟨430697303378275039925857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297052284684133546271237 430697303378275039925857)
                  ·
                    rfl

theorem cell21_1887255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_1887255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887255 prefixEnd_1887255 := by exact prefixLift 1887255
  have htrace : WordTrace (prefixWord ++ tailWord_1887255) baseStart_1887255 baseEnd_1887255 := by
    simpa [prefixWord, tailWord_1887255, baseEnd_1887255] using wordTrace_append hprefix tailTrace_1887255
  have hstable : (prefixWord ++ tailWord_1887255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887255).length < 2 ^ (prefixWord ++ tailWord_1887255).sum := by decide
  have hdescent : baseEnd_1887255 < baseStart_1887255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887286 : List Nat := [5, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1887286 : Nat := 118140960795 + 1887286 * 2 ^ 59
def prefixEnd_1887286 : Nat := 4983230072969 + 3 ^ 40 * 1887286 * 2
def baseEnd_1887286 : Nat := 143568126000208624969709

theorem tailTrace_1887286 : CollatzResearch.WordTrace tailWord_1887286 prefixEnd_1887286 143568126000208624969709 := by
  unfold tailWord_1887286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302185965043288727030107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45889983627128413088321141 4302185965043288727030107)
  ·
    refine ⟨6453278947564933090545161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4302185965043288727030107 6453278947564933090545161)
    ·
      refine ⟨4839959210673699817908871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6453278947564933090545161 4839959210673699817908871)
      ·
        refine ⟨7259938816010549726863307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839959210673699817908871 7259938816010549726863307)
        ·
          refine ⟨10889908224015824590294961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259938816010549726863307 10889908224015824590294961)
          ·
            refine ⟨8167431168011868442721221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10889908224015824590294961 8167431168011868442721221)
            ·
              refine ⟨1531393344002225333010229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8167431168011868442721221 1531393344002225333010229)
              ·
                refine ⟨143568126000208624969709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1531393344002225333010229 143568126000208624969709)
                ·
                  rfl

theorem cell21_1887286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1887286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887286 prefixEnd_1887286 := by exact prefixLift 1887286
  have htrace : WordTrace (prefixWord ++ tailWord_1887286) baseStart_1887286 baseEnd_1887286 := by
    simpa [prefixWord, tailWord_1887286, baseEnd_1887286] using wordTrace_append hprefix tailTrace_1887286
  have hstable : (prefixWord ++ tailWord_1887286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887286).length < 2 ^ (prefixWord ++ tailWord_1887286).sum := by decide
  have hdescent : baseEnd_1887286 < baseStart_1887286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887314 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1887314 : Nat := 118140960795 + 1887314 * 2 ^ 59
def prefixEnd_1887314 : Nat := 4983230072969 + 3 ^ 40 * 1887314 * 2
def baseEnd_1887314 : Nat := 430710767982104048442403

theorem tailTrace_1887314 : CollatzResearch.WordTrace tailWord_1887314 prefixEnd_1887314 430710767982104048442403 := by
  unfold tailWord_1887314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208999171147795103625249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45890664456394120276333997 17208999171147795103625249)
  ·
    refine ⟨12906749378360846327718937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17208999171147795103625249 12906749378360846327718937)
    ·
      refine ⟨9680062033770634745789203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12906749378360846327718937 9680062033770634745789203)
      ·
        refine ⟨14520093050655952118683805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9680062033770634745789203 14520093050655952118683805)
        ·
          refine ⟨5445034893995982044506427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14520093050655952118683805 5445034893995982044506427)
          ·
            refine ⟨8167552340993973066759641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445034893995982044506427 8167552340993973066759641)
            ·
              refine ⟨6125664255745479800069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167552340993973066759641 6125664255745479800069731)
              ·
                refine ⟨9188496383618219700104597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125664255745479800069731 9188496383618219700104597)
                ·
                  refine ⟨430710767982104048442403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9188496383618219700104597 430710767982104048442403)
                  ·
                    rfl

theorem cell21_1887314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1887314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887314 prefixEnd_1887314 := by exact prefixLift 1887314
  have htrace : WordTrace (prefixWord ++ tailWord_1887314) baseStart_1887314 baseEnd_1887314 := by
    simpa [prefixWord, tailWord_1887314, baseEnd_1887314] using wordTrace_append hprefix tailTrace_1887314
  have hstable : (prefixWord ++ tailWord_1887314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887314).length < 2 ^ (prefixWord ++ tailWord_1887314).sum := by decide
  have hdescent : baseEnd_1887314 < baseStart_1887314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887317 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 3]
def baseStart_1887317 : Nat := 118140960795 + 1887317 * 2 ^ 59
def prefixEnd_1887317 : Nat := 4983230072969 + 3 ^ 40 * 1887317 * 2
def baseEnd_1887317 : Nat := 430711452622976709892397

theorem tailTrace_1887317 : CollatzResearch.WordTrace tailWord_1887317 prefixEnd_1887317 430711452622976709892397 := by
  unfold tailWord_1887317
  simp only [CollatzResearch.WordTrace]
  refine ⟨68836106103580311926860205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45890737402386874617906803 68836106103580311926860205)
  ·
    refine ⟨25813539788842616972572577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68836106103580311926860205 25813539788842616972572577)
    ·
      refine ⟨19360154841631962729429433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25813539788842616972572577 19360154841631962729429433)
      ·
        refine ⟨14520116131223972047072075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19360154841631962729429433 14520116131223972047072075)
        ·
          refine ⟨21780174196835958070608113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14520116131223972047072075 21780174196835958070608113)
          ·
            refine ⟨16335130647626968552956085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21780174196835958070608113 16335130647626968552956085)
            ·
              refine ⟨1531418498215028301839633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16335130647626968552956085 1531418498215028301839633)
              ·
                refine ⟨1148563873661271226379725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531418498215028301839633 1148563873661271226379725)
                ·
                  refine ⟨430711452622976709892397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148563873661271226379725 430711452622976709892397)
                  ·
                    rfl

theorem cell21_1887317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_1887317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887317 prefixEnd_1887317 := by exact prefixLift 1887317
  have htrace : WordTrace (prefixWord ++ tailWord_1887317) baseStart_1887317 baseEnd_1887317 := by
    simpa [prefixWord, tailWord_1887317, baseEnd_1887317] using wordTrace_append hprefix tailTrace_1887317
  have hstable : (prefixWord ++ tailWord_1887317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887317).length < 2 ^ (prefixWord ++ tailWord_1887317).sum := by decide
  have hdescent : baseEnd_1887317 < baseStart_1887317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887328 : List Nat := [2, 1, 1, 3, 2, 2, 4, 6]
def baseStart_1887328 : Nat := 118140960795 + 1887328 * 2 ^ 59
def prefixEnd_1887328 : Nat := 4983230072969 + 3 ^ 40 * 1887328 * 2
def baseEnd_1887328 : Nat := 143571320990947711736347

theorem tailTrace_1887328 : CollatzResearch.WordTrace tailWord_1887328 prefixEnd_1887328 143571320990947711736347 := by
  unfold tailWord_1887328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418253653270230402755319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45891004871026973870340425 34418253653270230402755319)
  ·
    refine ⟨51627380479905345604132979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418253653270230402755319 51627380479905345604132979)
    ·
      refine ⟨77441070719858018406199469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51627380479905345604132979 77441070719858018406199469)
      ·
        refine ⟨29040401519946756902324801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77441070719858018406199469 29040401519946756902324801)
        ·
          refine ⟨21780301139960067676743601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29040401519946756902324801 21780301139960067676743601)
          ·
            refine ⟨16335225854970050757557701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21780301139960067676743601 16335225854970050757557701)
            ·
              refine ⟨3062854847806884517042069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16335225854970050757557701 3062854847806884517042069)
              ·
                refine ⟨143571320990947711736347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3062854847806884517042069 143571320990947711736347)
                ·
                  rfl

theorem cell21_1887328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_1887328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887328 prefixEnd_1887328 := by exact prefixLift 1887328
  have htrace : WordTrace (prefixWord ++ tailWord_1887328) baseStart_1887328 baseEnd_1887328 := by
    simpa [prefixWord, tailWord_1887328, baseEnd_1887328] using wordTrace_append hprefix tailTrace_1887328
  have hstable : (prefixWord ++ tailWord_1887328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887328).length < 2 ^ (prefixWord ++ tailWord_1887328).sum := by decide
  have hdescent : baseEnd_1887328 < baseStart_1887328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887418 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1887418 : Nat := 118140960795 + 1887418 * 2 ^ 59
def prefixEnd_1887418 : Nat := 4983230072969 + 3 ^ 40 * 1887418 * 2
def baseEnd_1887418 : Nat := 430734502199022978708857

theorem tailTrace_1887418 : CollatzResearch.WordTrace tailWord_1887418 prefixEnd_1887418 430734502199022978708857 := by
  unfold tailWord_1887418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209947469053601544071727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45893193250809604117524605 17209947469053601544071727)
  ·
    refine ⟨25814921203580402316107591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17209947469053601544071727 25814921203580402316107591)
    ·
      refine ⟨38722381805370603474161387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25814921203580402316107591 38722381805370603474161387)
      ·
        refine ⟨58083572708055905211242081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38722381805370603474161387 58083572708055905211242081)
        ·
          refine ⟨43562679531041928908431561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58083572708055905211242081 43562679531041928908431561)
          ·
            refine ⟨32672009648281446681323671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43562679531041928908431561 32672009648281446681323671)
            ·
              refine ⟨49008014472422170021985507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672009648281446681323671 49008014472422170021985507)
              ·
                refine ⟨73512021708633255032978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49008014472422170021985507 73512021708633255032978261)
                ·
                  refine ⟨430734502199022978708857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73512021708633255032978261 430734502199022978708857)
                  ·
                    rfl

theorem cell21_1887418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1887418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887418 prefixEnd_1887418 := by exact prefixLift 1887418
  have htrace : WordTrace (prefixWord ++ tailWord_1887418) baseStart_1887418 baseEnd_1887418 := by
    simpa [prefixWord, tailWord_1887418, baseEnd_1887418] using wordTrace_append hprefix tailTrace_1887418
  have hstable : (prefixWord ++ tailWord_1887418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887418).length < 2 ^ (prefixWord ++ tailWord_1887418).sum := by decide
  have hdescent : baseEnd_1887418 < baseStart_1887418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887424 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_1887424 : Nat := 118140960795 + 1887424 * 2 ^ 59
def prefixEnd_1887424 : Nat := 4983230072969 + 3 ^ 40 * 1887424 * 2
def baseEnd_1887424 : Nat := 430735871480768301608845

theorem tailTrace_1887424 : CollatzResearch.WordTrace tailWord_1887424 prefixEnd_1887424 430735871480768301608845 := by
  unfold tailWord_1887424
  simp only [CollatzResearch.WordTrace]
  refine ⟨34420004357096334600502663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45893339142795112800670217 34420004357096334600502663)
  ·
    refine ⟨51630006535644501900753995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34420004357096334600502663 51630006535644501900753995)
    ·
      refine ⟨77445009803466752851130993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51630006535644501900753995 77445009803466752851130993)
      ·
        refine ⟨58083757352600064638348245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77445009803466752851130993 58083757352600064638348245)
        ·
          refine ⟨1361338062951564014961287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58083757352600064638348245 1361338062951564014961287)
          ·
            refine ⟨2042007094427346022441931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361338062951564014961287 2042007094427346022441931)
            ·
              refine ⟨3063010641641019033662897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042007094427346022441931 3063010641641019033662897)
              ·
                refine ⟨2297257981230764275247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063010641641019033662897 2297257981230764275247173)
                ·
                  refine ⟨430735871480768301608845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297257981230764275247173 430735871480768301608845)
                  ·
                    rfl

theorem cell21_1887424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_1887424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887424 prefixEnd_1887424 := by exact prefixLift 1887424
  have htrace : WordTrace (prefixWord ++ tailWord_1887424) baseStart_1887424 baseEnd_1887424 := by
    simpa [prefixWord, tailWord_1887424, baseEnd_1887424] using wordTrace_append hprefix tailTrace_1887424
  have hstable : (prefixWord ++ tailWord_1887424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887424).length < 2 ^ (prefixWord ++ tailWord_1887424).sum := by decide
  have hdescent : baseEnd_1887424 < baseStart_1887424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887469 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1887469 : Nat := 118140960795 + 1887469 * 2 ^ 59
def prefixEnd_1887469 : Nat := 4983230072969 + 3 ^ 40 * 1887469 * 2
def baseEnd_1887469 : Nat := 430746141093858223358753

theorem tailTrace_1887469 : CollatzResearch.WordTrace tailWord_1887469 prefixEnd_1887469 430746141093858223358753 := by
  unfold tailWord_1887469
  simp only [CollatzResearch.WordTrace]
  refine ⟨68841649999029641886393461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45894433332686427924262307 68841649999029641886393461)
  ·
    refine ⟨6453904687409028926849387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68841649999029641886393461 6453904687409028926849387)
    ·
      refine ⟨9680857031113543390274081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453904687409028926849387 9680857031113543390274081)
      ·
        refine ⟨7260642773335157542705561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9680857031113543390274081 7260642773335157542705561)
        ·
          refine ⟨5445482080001368157029171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7260642773335157542705561 5445482080001368157029171)
          ·
            refine ⟨8168223120002052235543757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445482080001368157029171 8168223120002052235543757)
            ·
              refine ⟨3063083670000769588328909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8168223120002052235543757 3063083670000769588328909)
              ·
                refine ⟨1148656376250288595623341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3063083670000769588328909 1148656376250288595623341)
                ·
                  refine ⟨430746141093858223358753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148656376250288595623341 430746141093858223358753)
                  ·
                    rfl

theorem cell21_1887469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1887469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887469 prefixEnd_1887469 := by exact prefixLift 1887469
  have htrace : WordTrace (prefixWord ++ tailWord_1887469) baseStart_1887469 baseEnd_1887469 := by
    simpa [prefixWord, tailWord_1887469, baseEnd_1887469] using wordTrace_append hprefix tailTrace_1887469
  have hstable : (prefixWord ++ tailWord_1887469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887469).length < 2 ^ (prefixWord ++ tailWord_1887469).sum := by decide
  have hdescent : baseEnd_1887469 < baseStart_1887469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887486 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1887486 : Nat := 118140960795 + 1887486 * 2 ^ 59
def prefixEnd_1887486 : Nat := 4983230072969 + 3 ^ 40 * 1887486 * 2
def baseEnd_1887486 : Nat := 430750020725469971575385

theorem tailTrace_1887486 : CollatzResearch.WordTrace tailWord_1887486 prefixEnd_1887486 430750020725469971575385 := by
  unfold tailWord_1887486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605283754996006723720289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45894846693312035859841541 8605283754996006723720289)
  ·
    refine ⟨6453962816247005042790217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8605283754996006723720289 6453962816247005042790217)
    ·
      refine ⟨4840472112185253782092663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6453962816247005042790217 4840472112185253782092663)
      ·
        refine ⟨7260708168277880673138995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4840472112185253782092663 7260708168277880673138995)
        ·
          refine ⟨10891062252416821009708493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260708168277880673138995 10891062252416821009708493)
          ·
            refine ⟨4084148344656307878640685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10891062252416821009708493 4084148344656307878640685)
            ·
              refine ⟨1531555629246115454490257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4084148344656307878640685 1531555629246115454490257)
              ·
                refine ⟨1148666721934586590867693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531555629246115454490257 1148666721934586590867693)
                ·
                  refine ⟨430750020725469971575385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148666721934586590867693 430750020725469971575385)
                  ·
                    rfl

theorem cell21_1887486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1887486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887486 prefixEnd_1887486 := by exact prefixLift 1887486
  have htrace : WordTrace (prefixWord ++ tailWord_1887486) baseStart_1887486 baseEnd_1887486 := by
    simpa [prefixWord, tailWord_1887486, baseEnd_1887486] using wordTrace_append hprefix tailTrace_1887486
  have hstable : (prefixWord ++ tailWord_1887486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887486).length < 2 ^ (prefixWord ++ tailWord_1887486).sum := by decide
  have hdescent : baseEnd_1887486 < baseStart_1887486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887539 : List Nat := [1, 1, 1, 2, 5, 11]
def baseStart_1887539 : Nat := 118140960795 + 1887539 * 2 ^ 59
def prefixEnd_1887539 : Nat := 4983230072969 + 3 ^ 40 * 1887539 * 2
def baseEnd_1887539 : Nat := 15954152446205691007109

theorem tailTrace_1887539 : CollatzResearch.WordTrace tailWord_1887539 prefixEnd_1887539 15954152446205691007109 := by
  unfold tailWord_1887539
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844203108776043841441671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45896135405850695894294447 68844203108776043841441671)
  ·
    refine ⟨103266304663164065762162507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68844203108776043841441671 103266304663164065762162507)
    ·
      refine ⟨154899456994746098643243761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103266304663164065762162507 154899456994746098643243761)
      ·
        refine ⟨116174592746059573982432821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154899456994746098643243761 116174592746059573982432821)
        ·
          refine ⟨10891368069943085060853077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116174592746059573982432821 10891368069943085060853077)
          ·
            refine ⟨15954152446205691007109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10891368069943085060853077 15954152446205691007109)
            ·
              rfl

theorem cell21_1887539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 11].length) (baseStart_1887539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887539 prefixEnd_1887539 := by exact prefixLift 1887539
  have htrace : WordTrace (prefixWord ++ tailWord_1887539) baseStart_1887539 baseEnd_1887539 := by
    simpa [prefixWord, tailWord_1887539, baseEnd_1887539] using wordTrace_append hprefix tailTrace_1887539
  have hstable : (prefixWord ++ tailWord_1887539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887539).length < 2 ^ (prefixWord ++ tailWord_1887539).sum := by decide
  have hdescent : baseEnd_1887539 < baseStart_1887539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887545 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 3]
def baseStart_1887545 : Nat := 118140960795 + 1887545 * 2 ^ 59
def prefixEnd_1887545 : Nat := 4983230072969 + 3 ^ 40 * 1887545 * 2
def baseEnd_1887545 : Nat := 430763485329298980091931

theorem tailTrace_1887545 : CollatzResearch.WordTrace tailWord_1887545 prefixEnd_1887545 430763485329298980091931 := by
  unfold tailWord_1887545
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844421946754306866160089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45896281297836204577440059 68844421946754306866160089)
  ·
    refine ⟨51633316460065730149620067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68844421946754306866160089 51633316460065730149620067)
    ·
      refine ⟨77449974690098595224430101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51633316460065730149620067 77449974690098595224430101)
      ·
        refine ⟨3630467563598371651145161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77449974690098595224430101 3630467563598371651145161)
        ·
          refine ⟨2722850672698778738358871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630467563598371651145161 2722850672698778738358871)
          ·
            refine ⟨4084276009048168107538307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722850672698778738358871 4084276009048168107538307)
            ·
              refine ⟨6126414013572252161307461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084276009048168107538307 6126414013572252161307461)
              ·
                refine ⟨1148702627544797280245149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6126414013572252161307461 1148702627544797280245149)
                ·
                  refine ⟨430763485329298980091931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148702627544797280245149 430763485329298980091931)
                  ·
                    rfl

theorem cell21_1887545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_1887545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887545 prefixEnd_1887545 := by exact prefixLift 1887545
  have htrace : WordTrace (prefixWord ++ tailWord_1887545) baseStart_1887545 baseEnd_1887545 := by
    simpa [prefixWord, tailWord_1887545, baseEnd_1887545] using wordTrace_append hprefix tailTrace_1887545
  have hstable : (prefixWord ++ tailWord_1887545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887545).length < 2 ^ (prefixWord ++ tailWord_1887545).sum := by decide
  have hdescent : baseEnd_1887545 < baseStart_1887545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887573 : List Nat := [1, 3, 2, 2, 3, 2, 3, 5]
def baseStart_1887573 : Nat := 118140960795 + 1887573 * 2 ^ 59
def prefixEnd_1887573 : Nat := 4983230072969 + 3 ^ 40 * 1887573 * 2
def baseEnd_1887573 : Nat := 143589958436925717875069

theorem tailTrace_1887573 : CollatzResearch.WordTrace tailWord_1887573 prefixEnd_1887573 143589958436925717875069 := by
  unfold tailWord_1887573
  simp only [CollatzResearch.WordTrace]
  refine ⟨68845443190652867648179373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45896962127101911765452915 68845443190652867648179373)
  ·
    refine ⟨25817041196494825368067265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68845443190652867648179373 25817041196494825368067265)
    ·
      refine ⟨19362780897371119026050449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25817041196494825368067265 19362780897371119026050449)
      ·
        refine ⟨14522085673028339269537837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19362780897371119026050449 14522085673028339269537837)
        ·
          refine ⟨5445782127385627226076689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14522085673028339269537837 5445782127385627226076689)
          ·
            refine ⟨4084336595539220419557517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445782127385627226076689 4084336595539220419557517)
            ·
              refine ⟨1531626223327207657334069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4084336595539220419557517 1531626223327207657334069)
              ·
                refine ⟨143589958436925717875069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1531626223327207657334069 143589958436925717875069)
                ·
                  rfl

theorem cell21_1887573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].length) (baseStart_1887573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887573 prefixEnd_1887573 := by exact prefixLift 1887573
  have htrace : WordTrace (prefixWord ++ tailWord_1887573) baseStart_1887573 baseEnd_1887573 := by
    simpa [prefixWord, tailWord_1887573, baseEnd_1887573] using wordTrace_append hprefix tailTrace_1887573
  have hstable : (prefixWord ++ tailWord_1887573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887573).length < 2 ^ (prefixWord ++ tailWord_1887573).sum := by decide
  have hdescent : baseEnd_1887573 < baseStart_1887573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887663 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 3]
def baseStart_1887663 : Nat := 118140960795 + 1887663 * 2 ^ 59
def prefixEnd_1887663 : Nat := 4983230072969 + 3 ^ 40 * 1887663 * 2
def baseEnd_1887663 : Nat := 430790414536956997125023

theorem tailTrace_1887663 : CollatzResearch.WordTrace tailWord_1887663 prefixEnd_1887663 430790414536956997125023 := by
  unfold tailWord_1887663
  simp only [CollatzResearch.WordTrace]
  refine ⟨68848725760326813018955643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45899150506884542012637095 68848725760326813018955643)
  ·
    refine ⟨103273088640490219528433465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68848725760326813018955643 103273088640490219528433465)
    ·
      refine ⟨77454816480367664646325099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103273088640490219528433465 77454816480367664646325099)
      ·
        refine ⟨116182224720551496969487649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77454816480367664646325099 116182224720551496969487649)
        ·
          refine ⟨87136668540413622727115737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116182224720551496969487649 87136668540413622727115737)
          ·
            refine ⟨65352501405310217045336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87136668540413622727115737 65352501405310217045336803)
            ·
              refine ⟨98028752107965325568005205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65352501405310217045336803 98028752107965325568005205)
              ·
                refine ⟨1148774438765218659000061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 98028752107965325568005205 1148774438765218659000061)
                ·
                  refine ⟨430790414536956997125023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148774438765218659000061 430790414536956997125023)
                  ·
                    rfl

theorem cell21_1887663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].length) (baseStart_1887663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887663 prefixEnd_1887663 := by exact prefixLift 1887663
  have htrace : WordTrace (prefixWord ++ tailWord_1887663) baseStart_1887663 baseEnd_1887663 := by
    simpa [prefixWord, tailWord_1887663, baseEnd_1887663] using wordTrace_append hprefix tailTrace_1887663
  have hstable : (prefixWord ++ tailWord_1887663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887663).length < 2 ^ (prefixWord ++ tailWord_1887663).sum := by decide
  have hdescent : baseEnd_1887663 < baseStart_1887663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887691 : List Nat := [1, 1, 1, 1, 3, 3, 4, 7]
def baseStart_1887691 : Nat := 118140960795 + 1887691 * 2 ^ 59
def prefixEnd_1887691 : Nat := 4983230072969 + 3 ^ 40 * 1887691 * 2
def baseEnd_1887691 : Nat := 143598934839478390219433

theorem tailTrace_1887691 : CollatzResearch.WordTrace tailWord_1887691 prefixEnd_1887691 143598934839478390219433 := by
  unfold tailWord_1887691
  simp only [CollatzResearch.WordTrace]
  refine ⟨68849747004225373800974927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45899831336150249200649951 68849747004225373800974927)
  ·
    refine ⟨103274620506338060701462391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68849747004225373800974927 103274620506338060701462391)
    ·
      refine ⟨154911930759507091052193587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103274620506338060701462391 154911930759507091052193587)
      ·
        refine ⟨232367896139260636578290381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154911930759507091052193587 232367896139260636578290381)
        ·
          refine ⟨87137961052222738716858893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232367896139260636578290381 87137961052222738716858893)
          ·
            refine ⟨32676735394583527018822085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87137961052222738716858893 32676735394583527018822085)
            ·
              refine ⟨6126887886484411316029141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32676735394583527018822085 6126887886484411316029141)
              ·
                refine ⟨143598934839478390219433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6126887886484411316029141 143598934839478390219433)
                ·
                  rfl

theorem cell21_1887691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_1887691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887691 prefixEnd_1887691 := by exact prefixLift 1887691
  have htrace : WordTrace (prefixWord ++ tailWord_1887691) baseStart_1887691 baseEnd_1887691 := by
    simpa [prefixWord, tailWord_1887691, baseEnd_1887691] using wordTrace_append hprefix tailTrace_1887691
  have hstable : (prefixWord ++ tailWord_1887691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887691).length < 2 ^ (prefixWord ++ tailWord_1887691).sum := by decide
  have hdescent : baseEnd_1887691 < baseStart_1887691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887801 : List Nat := [1, 2, 1, 5, 1, 4, 2, 5]
def baseStart_1887801 : Nat := 118140960795 + 1887801 * 2 ^ 59
def prefixEnd_1887801 : Nat := 4983230072969 + 3 ^ 40 * 1887801 * 2
def baseEnd_1887801 : Nat := 143607302672366474608247

theorem tailTrace_1887801 : CollatzResearch.WordTrace tailWord_1887801 prefixEnd_1887801 143607302672366474608247 := by
  unfold tailWord_1887801
  simp only [CollatzResearch.WordTrace]
  refine ⟨68853759033826862587479257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45902506022551241724986171 68853759033826862587479257)
  ·
    refine ⟨51640319275370146940609443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68853759033826862587479257 51640319275370146940609443)
    ·
      refine ⟨77460478913055220410914165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51640319275370146940609443 77460478913055220410914165)
      ·
        refine ⟨7261919898098926913523203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77460478913055220410914165 7261919898098926913523203)
        ·
          refine ⟨10892879847148390370284805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261919898098926913523203 10892879847148390370284805)
          ·
            refine ⟨2042414971340323194428401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10892879847148390370284805 2042414971340323194428401)
            ·
              refine ⟨1531811228505242395821301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042414971340323194428401 1531811228505242395821301)
              ·
                refine ⟨143607302672366474608247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1531811228505242395821301 143607302672366474608247)
                ·
                  rfl

theorem cell21_1887801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].length) (baseStart_1887801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887801 prefixEnd_1887801 := by exact prefixLift 1887801
  have htrace : WordTrace (prefixWord ++ tailWord_1887801) baseStart_1887801 baseEnd_1887801 := by
    simpa [prefixWord, tailWord_1887801, baseEnd_1887801] using wordTrace_append hprefix tailTrace_1887801
  have hstable : (prefixWord ++ tailWord_1887801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887801).length < 2 ^ (prefixWord ++ tailWord_1887801).sum := by decide
  have hdescent : baseEnd_1887801 < baseStart_1887801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887829 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_1887829 : Nat := 118140960795 + 1887829 * 2 ^ 59
def prefixEnd_1887829 : Nat := 4983230072969 + 3 ^ 40 * 1887829 * 2
def baseEnd_1887829 : Nat := 430828297998577597358017

theorem tailTrace_1887829 : CollatzResearch.WordTrace tailWord_1887829 prefixEnd_1887829 430828297998577597358017 := by
  unfold tailWord_1887829
  simp only [CollatzResearch.WordTrace]
  refine ⟨68854780277725423369498541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45903186851816948912999027 68854780277725423369498541)
  ·
    refine ⟨25820542604147033763561953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68854780277725423369498541 25820542604147033763561953)
    ·
      refine ⟨19365406953110275322671465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25820542604147033763561953 19365406953110275322671465)
      ·
        refine ⟨14524055214832706492003599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19365406953110275322671465 14524055214832706492003599)
        ·
          refine ⟨21786082822249059738005399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524055214832706492003599 21786082822249059738005399)
          ·
            refine ⟨32679124233373589607008099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786082822249059738005399 32679124233373589607008099)
            ·
              refine ⟨49018686350060384410512149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32679124233373589607008099 49018686350060384410512149)
              ·
                refine ⟨2297750922659080519242757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49018686350060384410512149 2297750922659080519242757)
                ·
                  refine ⟨430828297998577597358017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297750922659080519242757 430828297998577597358017)
                  ·
                    rfl

theorem cell21_1887829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_1887829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887829 prefixEnd_1887829 := by exact prefixLift 1887829
  have htrace : WordTrace (prefixWord ++ tailWord_1887829) baseStart_1887829 baseEnd_1887829 := by
    simpa [prefixWord, tailWord_1887829, baseEnd_1887829] using wordTrace_append hprefix tailTrace_1887829
  have hstable : (prefixWord ++ tailWord_1887829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887829).length < 2 ^ (prefixWord ++ tailWord_1887829).sum := by decide
  have hdescent : baseEnd_1887829 < baseStart_1887829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887843 : List Nat := [1, 1, 1, 5, 1, 3, 1, 8]
def baseStart_1887843 : Nat := 118140960795 + 1887843 * 2 ^ 59
def prefixEnd_1887843 : Nat := 4983230072969 + 3 ^ 40 * 1887843 * 2
def baseEnd_1887843 : Nat := 143610497663105561374885

theorem tailTrace_1887843 : CollatzResearch.WordTrace tailWord_1887843 prefixEnd_1887843 143610497663105561374885 := by
  unfold tailWord_1887843
  simp only [CollatzResearch.WordTrace]
  refine ⟨68855290899674703760508183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45903527266449802507005455 68855290899674703760508183)
  ·
    refine ⟨103282936349512055640762275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68855290899674703760508183 103282936349512055640762275)
    ·
      refine ⟨154924404524268083461143413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103282936349512055640762275 154924404524268083461143413)
      ·
        refine ⟨14524162924150132824482195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154924404524268083461143413 14524162924150132824482195)
        ·
          refine ⟨21786244386225199236723293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524162924150132824482195 21786244386225199236723293)
          ·
            refine ⟨8169841644834449713771235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21786244386225199236723293 8169841644834449713771235)
            ·
              refine ⟨12254762467251674570656853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8169841644834449713771235 12254762467251674570656853)
              ·
                refine ⟨143610497663105561374885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12254762467251674570656853 143610497663105561374885)
                ·
                  rfl

theorem cell21_1887843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_1887843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887843 prefixEnd_1887843 := by exact prefixLift 1887843
  have htrace : WordTrace (prefixWord ++ tailWord_1887843) baseStart_1887843 baseEnd_1887843 := by
    simpa [prefixWord, tailWord_1887843, baseEnd_1887843] using wordTrace_append hprefix tailTrace_1887843
  have hstable : (prefixWord ++ tailWord_1887843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887843).length < 2 ^ (prefixWord ++ tailWord_1887843).sum := by decide
  have hdescent : baseEnd_1887843 < baseStart_1887843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887888 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1887888 : Nat := 118140960795 + 1887888 * 2 ^ 59
def prefixEnd_1887888 : Nat := 4983230072969 + 3 ^ 40 * 1887888 * 2
def baseEnd_1887888 : Nat := 430841762602406605874563

theorem tailTrace_1887888 : CollatzResearch.WordTrace tailWord_1887888 prefixEnd_1887888 430841762602406605874563 := by
  unfold tailWord_1887888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34428466092255838222948159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45904621456341117630597545 34428466092255838222948159)
  ·
    refine ⟨51642699138383757334422239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34428466092255838222948159 51642699138383757334422239)
    ·
      refine ⟨77464048707575636001633359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51642699138383757334422239 77464048707575636001633359)
      ·
        refine ⟨116196073061363454002450039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77464048707575636001633359 116196073061363454002450039)
        ·
          refine ⟨174294109592045181003675059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116196073061363454002450039 174294109592045181003675059)
          ·
            refine ⟨261441164388067771505512589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174294109592045181003675059 261441164388067771505512589)
            ·
              refine ⟨98040436645525414314567221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261441164388067771505512589 98040436645525414314567221)
              ·
                refine ⟨9191290935518007591990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98040436645525414314567221 9191290935518007591990677)
                ·
                  refine ⟨430841762602406605874563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9191290935518007591990677 430841762602406605874563)
                  ·
                    rfl

theorem cell21_1887888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1887888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887888 prefixEnd_1887888 := by exact prefixLift 1887888
  have htrace : WordTrace (prefixWord ++ tailWord_1887888) baseStart_1887888 baseEnd_1887888 := by
    simpa [prefixWord, tailWord_1887888, baseEnd_1887888] using wordTrace_append hprefix tailTrace_1887888
  have hstable : (prefixWord ++ tailWord_1887888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887888).length < 2 ^ (prefixWord ++ tailWord_1887888).sum := by decide
  have hdescent : baseEnd_1887888 < baseStart_1887888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887925 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 3]
def baseStart_1887925 : Nat := 118140960795 + 1887925 * 2 ^ 59
def prefixEnd_1887925 : Nat := 4983230072969 + 3 ^ 40 * 1887925 * 2
def baseEnd_1887925 : Nat := 430850206506502763757821

theorem tailTrace_1887925 : CollatzResearch.WordTrace tailWord_1887925 prefixEnd_1887925 430850206506502763757821 := by
  unfold tailWord_1887925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68858281685377631764993229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45905521123585087843328819 68858281685377631764993229)
  ·
    refine ⟨25821855632016611911872461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68858281685377631764993229 25821855632016611911872461)
    ·
      refine ⟨9683195862006229466952173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25821855632016611911872461 9683195862006229466952173)
      ·
        refine ⟨3631198448252336050107065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9683195862006229466952173 3631198448252336050107065)
        ·
          refine ⟨2723398836189252037580299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631198448252336050107065 2723398836189252037580299)
          ·
            refine ⟨4085098254283878056370449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723398836189252037580299 4085098254283878056370449)
            ·
              refine ⟨3063823690712908542277837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085098254283878056370449 3063823690712908542277837)
              ·
                refine ⟨1148933884017340703354189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3063823690712908542277837 1148933884017340703354189)
                ·
                  refine ⟨430850206506502763757821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148933884017340703354189 430850206506502763757821)
                  ·
                    rfl

theorem cell21_1887925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_1887925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887925 prefixEnd_1887925 := by exact prefixLift 1887925
  have htrace : WordTrace (prefixWord ++ tailWord_1887925) baseStart_1887925 baseEnd_1887925 := by
    simpa [prefixWord, tailWord_1887925, baseEnd_1887925] using wordTrace_append hprefix tailTrace_1887925
  have hstable : (prefixWord ++ tailWord_1887925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887925).length < 2 ^ (prefixWord ++ tailWord_1887925).sum := by decide
  have hdescent : baseEnd_1887925 < baseStart_1887925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887942 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1887942 : Nat := 118140960795 + 1887942 * 2 ^ 59
def prefixEnd_1887942 : Nat := 4983230072969 + 3 ^ 40 * 1887942 * 2
def baseEnd_1887942 : Nat := 430854086138114511974453

theorem tailTrace_1887942 : CollatzResearch.WordTrace tailWord_1887942 prefixEnd_1887942 430854086138114511974453 := by
  unfold tailWord_1887942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151840678947376364636315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45905934484210695778908053 2151840678947376364636315)
  ·
    refine ⟨3227761018421064546954473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151840678947376364636315 3227761018421064546954473)
    ·
      refine ⟨2420820763815798410215855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3227761018421064546954473 2420820763815798410215855)
      ·
        refine ⟨3631231145723697615323783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420820763815798410215855 3631231145723697615323783)
        ·
          refine ⟨5446846718585546422985675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631231145723697615323783 5446846718585546422985675)
          ·
            refine ⟨8170270077878319634478513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446846718585546422985675 8170270077878319634478513)
            ·
              refine ⟨6127702558408739725858885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8170270077878319634478513 6127702558408739725858885)
              ·
                refine ⟨1148944229701638698598541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6127702558408739725858885 1148944229701638698598541)
                ·
                  refine ⟨430854086138114511974453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148944229701638698598541 430854086138114511974453)
                  ·
                    rfl

theorem cell21_1887942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1887942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887942 prefixEnd_1887942 := by exact prefixLift 1887942
  have htrace : WordTrace (prefixWord ++ tailWord_1887942) baseStart_1887942 baseEnd_1887942 := by
    simpa [prefixWord, tailWord_1887942, baseEnd_1887942] using wordTrace_append hprefix tailTrace_1887942
  have hstable : (prefixWord ++ tailWord_1887942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887942).length < 2 ^ (prefixWord ++ tailWord_1887942).sum := by decide
  have hdescent : baseEnd_1887942 < baseStart_1887942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887981 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1887981 : Nat := 118140960795 + 1887981 * 2 ^ 59
def prefixEnd_1887981 : Nat := 4983230072969 + 3 ^ 40 * 1887981 * 2
def baseEnd_1887981 : Nat := 430862986469459110824373

theorem tailTrace_1887981 : CollatzResearch.WordTrace tailWord_1887981 prefixEnd_1887981 430862986469459110824373 := by
  unfold tailWord_1887981
  simp only [CollatzResearch.WordTrace]
  refine ⟨68860324173174753329031797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45906882782116502219354531 68860324173174753329031797)
  ·
    refine ⟨6455655391235133124596731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68860324173174753329031797 6455655391235133124596731)
    ·
      refine ⟨9683483086852699686895097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455655391235133124596731 9683483086852699686895097)
      ·
        refine ⟨7262612315139524765171323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9683483086852699686895097 7262612315139524765171323)
        ·
          refine ⟨10893918472709287147756985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262612315139524765171323 10893918472709287147756985)
          ·
            refine ⟨8170438854531965360817739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10893918472709287147756985 8170438854531965360817739)
            ·
              refine ⟨12255658281797948041226609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170438854531965360817739 12255658281797948041226609)
              ·
                refine ⟨9191743711348461030919957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12255658281797948041226609 9191743711348461030919957)
                ·
                  refine ⟨430862986469459110824373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9191743711348461030919957 430862986469459110824373)
                  ·
                    rfl

theorem cell21_1887981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1887981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1887981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1887981 prefixEnd_1887981 := by exact prefixLift 1887981
  have htrace : WordTrace (prefixWord ++ tailWord_1887981) baseStart_1887981 baseEnd_1887981 := by
    simpa [prefixWord, tailWord_1887981, baseEnd_1887981] using wordTrace_append hprefix tailTrace_1887981
  have hstable : (prefixWord ++ tailWord_1887981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887981).length < 2 ^ (prefixWord ++ tailWord_1887981).sum := by decide
  have hdescent : baseEnd_1887981 < baseStart_1887981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888060 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_1888060 : Nat := 118140960795 + 1888060 * 2 ^ 59
def prefixEnd_1888060 : Nat := 4983230072969 + 3 ^ 40 * 1888060 * 2
def baseEnd_1888060 : Nat := 430881015345772529007545

theorem tailTrace_1888060 : CollatzResearch.WordTrace tailWord_1888060 prefixEnd_1888060 430881015345772529007545 := by
  unfold tailWord_1888060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431602769944274910578817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45908803693259033214105089 34431602769944274910578817)
  ·
    refine ⟨25823702077458206182934113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34431602769944274910578817 25823702077458206182934113)
    ·
      refine ⟨19367776558093654637200585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25823702077458206182934113 19367776558093654637200585)
      ·
        refine ⟨14525832418570240977900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19367776558093654637200585 14525832418570240977900439)
        ·
          refine ⟨21788748627855361466850659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525832418570240977900439 21788748627855361466850659)
          ·
            refine ⟨32683122941783042200275989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21788748627855361466850659 32683122941783042200275989)
            ·
              refine ⟨1532021387896080103137937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32683122941783042200275989 1532021387896080103137937)
              ·
                refine ⟨1149016040922060077353453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532021387896080103137937 1149016040922060077353453)
                ·
                  refine ⟨430881015345772529007545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149016040922060077353453 430881015345772529007545)
                  ·
                    rfl

theorem cell21_1888060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_1888060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888060 prefixEnd_1888060 := by exact prefixLift 1888060
  have htrace : WordTrace (prefixWord ++ tailWord_1888060) baseStart_1888060 baseEnd_1888060 := by
    simpa [prefixWord, tailWord_1888060, baseEnd_1888060] using wordTrace_append hprefix tailTrace_1888060
  have hstable : (prefixWord ++ tailWord_1888060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888060).length < 2 ^ (prefixWord ++ tailWord_1888060).sum := by decide
  have hdescent : baseEnd_1888060 < baseStart_1888060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888071 : List Nat := [1, 1, 4, 1, 2, 1, 5, 6]
def baseStart_1888071 : Nat := 118140960795 + 1888071 * 2 ^ 59
def prefixEnd_1888071 : Nat := 4983230072969 + 3 ^ 40 * 1888071 * 2
def baseEnd_1888071 : Nat := 143627841898546318108063

theorem tailTrace_1888071 : CollatzResearch.WordTrace tailWord_1888071 prefixEnd_1888071 143627841898546318108063 := by
  unfold tailWord_1888071
  simp only [CollatzResearch.WordTrace]
  refine ⟨68863606742848698699808067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45909071161899132466538711 68863606742848698699808067)
  ·
    refine ⟨103295410114273048049712101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68863606742848698699808067 103295410114273048049712101)
    ·
      refine ⟨19367889396426196509321019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103295410114273048049712101 19367889396426196509321019)
      ·
        refine ⟨29051834094639294763981529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19367889396426196509321019 29051834094639294763981529)
        ·
          refine ⟨21788875570979471072986147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29051834094639294763981529 21788875570979471072986147)
          ·
            refine ⟨32683313356469206609479221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21788875570979471072986147 32683313356469206609479221)
            ·
              refine ⟨3064060627168988119638677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32683313356469206609479221 3064060627168988119638677)
              ·
                refine ⟨143627841898546318108063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3064060627168988119638677 143627841898546318108063)
                ·
                  rfl

theorem cell21_1888071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_1888071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888071 prefixEnd_1888071 := by exact prefixLift 1888071
  have htrace : WordTrace (prefixWord ++ tailWord_1888071) baseStart_1888071 baseEnd_1888071 := by
    simpa [prefixWord, tailWord_1888071, baseEnd_1888071] using wordTrace_append hprefix tailTrace_1888071
  have hstable : (prefixWord ++ tailWord_1888071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888071).length < 2 ^ (prefixWord ++ tailWord_1888071).sum := by decide
  have hdescent : baseEnd_1888071 < baseStart_1888071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888268 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1888268 : Nat := 118140960795 + 1888268 * 2 ^ 59
def prefixEnd_1888268 : Nat := 4983230072969 + 3 ^ 40 * 1888268 * 2
def baseEnd_1888268 : Nat := 430928483779610389540453

theorem tailTrace_1888268 : CollatzResearch.WordTrace tailWord_1888268 prefixEnd_1888268 430928483779610389540453 := by
  unfold tailWord_1888268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34435395961567500672364729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45913861282090000896486305 34435395961567500672364729)
  ·
    refine ⟨25826546971175625504273547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34435395961567500672364729 25826546971175625504273547)
    ·
      refine ⟨38739820456763438256410321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826546971175625504273547 38739820456763438256410321)
      ·
        refine ⟨29054865342572578692307741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38739820456763438256410321 29054865342572578692307741)
        ·
          refine ⟨10895574503464717009615403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29054865342572578692307741 10895574503464717009615403)
          ·
            refine ⟨16343361755197075514423105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895574503464717009615403 16343361755197075514423105)
            ·
              refine ⟨12257521316397806635817329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16343361755197075514423105 12257521316397806635817329)
              ·
                refine ⟨9193140987298354976862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12257521316397806635817329 9193140987298354976862997)
                ·
                  refine ⟨430928483779610389540453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9193140987298354976862997 430928483779610389540453)
                  ·
                    rfl

theorem cell21_1888268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1888268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888268 prefixEnd_1888268 := by exact prefixLift 1888268
  have htrace : WordTrace (prefixWord ++ tailWord_1888268) baseStart_1888268 baseEnd_1888268 := by
    simpa [prefixWord, tailWord_1888268, baseEnd_1888268] using wordTrace_append hprefix tailTrace_1888268
  have hstable : (prefixWord ++ tailWord_1888268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888268).length < 2 ^ (prefixWord ++ tailWord_1888268).sum := by decide
  have hdescent : baseEnd_1888268 < baseStart_1888268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888285 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1888285 : Nat := 118140960795 + 1888285 * 2 ^ 59
def prefixEnd_1888285 : Nat := 4983230072969 + 3 ^ 40 * 1888285 * 2
def baseEnd_1888285 : Nat := 430932363411222137757085

theorem tailTrace_1888285 : CollatzResearch.WordTrace tailWord_1888285 prefixEnd_1888285 430932363411222137757085 := by
  unfold tailWord_1888285
  simp only [CollatzResearch.WordTrace]
  refine ⟨68871411964073413248098309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45914274642715608832065539 68871411964073413248098309)
  ·
    refine ⟨12913389743263764984018433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68871411964073413248098309 12913389743263764984018433)
    ·
      refine ⟨9685042307447823738013825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12913389743263764984018433 9685042307447823738013825)
      ·
        refine ⟨7263781730585867803510369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9685042307447823738013825 7263781730585867803510369)
        ·
          refine ⟨5447836297939400852632777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263781730585867803510369 5447836297939400852632777)
          ·
            refine ⟨4085877223454550639474583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447836297939400852632777 4085877223454550639474583)
            ·
              refine ⟨6128815835181825959211875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085877223454550639474583 6128815835181825959211875)
              ·
                refine ⟨9193223752772738938817813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128815835181825959211875 9193223752772738938817813)
                ·
                  refine ⟨430932363411222137757085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9193223752772738938817813 430932363411222137757085)
                  ·
                    rfl

theorem cell21_1888285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1888285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888285 prefixEnd_1888285 := by exact prefixLift 1888285
  have htrace : WordTrace (prefixWord ++ tailWord_1888285) baseStart_1888285 baseEnd_1888285 := by
    simpa [prefixWord, tailWord_1888285, baseEnd_1888285] using wordTrace_append hprefix tailTrace_1888285
  have hstable : (prefixWord ++ tailWord_1888285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888285).length < 2 ^ (prefixWord ++ tailWord_1888285).sum := by decide
  have hdescent : baseEnd_1888285 < baseStart_1888285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888344 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1888344 : Nat := 118140960795 + 1888344 * 2 ^ 59
def prefixEnd_1888344 : Nat := 4983230072969 + 3 ^ 40 * 1888344 * 2
def baseEnd_1888344 : Nat := 430945828015051146273631

theorem tailTrace_1888344 : CollatzResearch.WordTrace tailWord_1888344 prefixEnd_1888344 430945828015051146273631 := by
  unfold tailWord_1888344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436781935429833162248043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45915709247239777549664057 34436781935429833162248043)
  ·
    refine ⟨51655172903144749743372065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34436781935429833162248043 51655172903144749743372065)
    ·
      refine ⟨38741379677358562307529049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51655172903144749743372065 38741379677358562307529049)
      ·
        refine ⟨29056034758018921730646787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38741379677358562307529049 29056034758018921730646787)
        ·
          refine ⟨43584052137028382595970181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29056034758018921730646787 43584052137028382595970181)
          ·
            refine ⟨8172009775692821736744409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43584052137028382595970181 8172009775692821736744409)
            ·
              refine ⟨6129007331769616302558307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8172009775692821736744409 6129007331769616302558307)
              ·
                refine ⟨9193510997654424453837461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129007331769616302558307 9193510997654424453837461)
                ·
                  refine ⟨430945828015051146273631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9193510997654424453837461 430945828015051146273631)
                  ·
                    rfl

theorem cell21_1888344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1888344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888344 prefixEnd_1888344 := by exact prefixLift 1888344
  have htrace : WordTrace (prefixWord ++ tailWord_1888344) baseStart_1888344 baseEnd_1888344 := by
    simpa [prefixWord, tailWord_1888344, baseEnd_1888344] using wordTrace_append hprefix tailTrace_1888344
  have hstable : (prefixWord ++ tailWord_1888344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888344).length < 2 ^ (prefixWord ++ tailWord_1888344).sum := by decide
  have hdescent : baseEnd_1888344 < baseStart_1888344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888350 : List Nat := [4, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1888350 : Nat := 118140960795 + 1888350 * 2 ^ 59
def prefixEnd_1888350 : Nat := 4983230072969 + 3 ^ 40 * 1888350 * 2
def baseEnd_1888350 : Nat := 143649065765598823057873

theorem tailTrace_1888350 : CollatzResearch.WordTrace tailWord_1888350 prefixEnd_1888350 143649065765598823057873 := by
  unfold tailWord_1888350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609222838604741168651813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45915855139225286232809669 8609222838604741168651813)
  ·
    refine ⟨1614229282238388969122215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8609222838604741168651813 1614229282238388969122215)
    ·
      refine ⟨2421343923357583453683323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614229282238388969122215 2421343923357583453683323)
      ·
        refine ⟨3632015885036375180524985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421343923357583453683323 3632015885036375180524985)
        ·
          refine ⟨2724011913777281385393739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632015885036375180524985 2724011913777281385393739)
          ·
            refine ⟨4086017870665922078090609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724011913777281385393739 4086017870665922078090609)
            ·
              refine ⟨3064513402999441558567957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086017870665922078090609 3064513402999441558567957)
              ·
                refine ⟨143649065765598823057873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3064513402999441558567957 143649065765598823057873)
                ·
                  rfl

theorem cell21_1888350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1888350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888350 prefixEnd_1888350 := by exact prefixLift 1888350
  have htrace : WordTrace (prefixWord ++ tailWord_1888350) baseStart_1888350 baseEnd_1888350 := by
    simpa [prefixWord, tailWord_1888350, baseEnd_1888350] using wordTrace_append hprefix tailTrace_1888350
  have hstable : (prefixWord ++ tailWord_1888350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888350).length < 2 ^ (prefixWord ++ tailWord_1888350).sum := by decide
  have hdescent : baseEnd_1888350 < baseStart_1888350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888398 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1888398 : Nat := 118140960795 + 1888398 * 2 ^ 59
def prefixEnd_1888398 : Nat := 4983230072969 + 3 ^ 40 * 1888398 * 2
def baseEnd_1888398 : Nat := 430958151550759052373521

theorem tailTrace_1888398 : CollatzResearch.WordTrace tailWord_1888398 prefixEnd_1888398 430958151550759052373521 := by
  unfold tailWord_1888398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609441676583004193370231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45917022275109355697974565 8609441676583004193370231)
  ·
    refine ⟨12914162514874506290055347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609441676583004193370231 12914162514874506290055347)
    ·
      refine ⟨19371243772311759435083021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914162514874506290055347 19371243772311759435083021)
      ·
        refine ⟨7264216414616909788156133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19371243772311759435083021 7264216414616909788156133)
        ·
          refine ⟨1362040577740670585279275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7264216414616909788156133 1362040577740670585279275)
          ·
            refine ⟨2043060866611005877918913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362040577740670585279275 2043060866611005877918913)
            ·
              refine ⟨1532295649958254408439185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043060866611005877918913 1532295649958254408439185)
              ·
                refine ⟨1149221737468690806329389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532295649958254408439185 1149221737468690806329389)
                ·
                  refine ⟨430958151550759052373521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149221737468690806329389 430958151550759052373521)
                  ·
                    rfl

theorem cell21_1888398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1888398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888398 prefixEnd_1888398 := by exact prefixLift 1888398
  have htrace : WordTrace (prefixWord ++ tailWord_1888398) baseStart_1888398 baseEnd_1888398 := by
    simpa [prefixWord, tailWord_1888398, baseEnd_1888398] using wordTrace_append hprefix tailTrace_1888398
  have hstable : (prefixWord ++ tailWord_1888398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888398).length < 2 ^ (prefixWord ++ tailWord_1888398).sum := by decide
  have hdescent : baseEnd_1888398 < baseStart_1888398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888423 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_1888423 : Nat := 118140960795 + 1888423 * 2 ^ 59
def prefixEnd_1888423 : Nat := 4983230072969 + 3 ^ 40 * 1888423 * 2
def baseEnd_1888423 : Nat := 430963856891364564456803

theorem tailTrace_1888423 : CollatzResearch.WordTrace tailWord_1888423 prefixEnd_1888423 430963856891364564456803 := by
  unfold tailWord_1888423
  simp only [CollatzResearch.WordTrace]
  refine ⟨68876445237573462816621923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45917630158382308544414615 68876445237573462816621923)
  ·
    refine ⟨103314667856360194224932885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68876445237573462816621923 103314667856360194224932885)
    ·
      refine ⟨4842875055766884104293729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103314667856360194224932885 4842875055766884104293729)
      ·
        refine ⟨3632156291825163078220297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4842875055766884104293729 3632156291825163078220297)
        ·
          refine ⟨2724117218868872308665223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632156291825163078220297 2724117218868872308665223)
          ·
            refine ⟨4086175828303308462997835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724117218868872308665223 4086175828303308462997835)
            ·
              refine ⟨6129263742454962694496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086175828303308462997835 6129263742454962694496753)
              ·
                refine ⟨4596947806841222020872565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129263742454962694496753 4596947806841222020872565)
                ·
                  refine ⟨430963856891364564456803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4596947806841222020872565 430963856891364564456803)
                  ·
                    rfl

theorem cell21_1888423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_1888423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888423 prefixEnd_1888423 := by exact prefixLift 1888423
  have htrace : WordTrace (prefixWord ++ tailWord_1888423) baseStart_1888423 baseEnd_1888423 := by
    simpa [prefixWord, tailWord_1888423, baseEnd_1888423] using wordTrace_append hprefix tailTrace_1888423
  have hstable : (prefixWord ++ tailWord_1888423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888423).length < 2 ^ (prefixWord ++ tailWord_1888423).sum := by decide
  have hdescent : baseEnd_1888423 < baseStart_1888423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888465 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_1888465 : Nat := 118140960795 + 1888465 * 2 ^ 59
def prefixEnd_1888465 : Nat := 4983230072969 + 3 ^ 40 * 1888465 * 2
def baseEnd_1888465 : Nat := 430973441863581824756717

theorem tailTrace_1888465 : CollatzResearch.WordTrace tailWord_1888465 prefixEnd_1888465 430973441863581824756717 := by
  unfold tailWord_1888465
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877977103421303989650849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45918651402280869326433899 68877977103421303989650849)
  ·
    refine ⟨51658482827565977992238137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68877977103421303989650849 51658482827565977992238137)
    ·
      refine ⟨38743862120674483494178603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51658482827565977992238137 38743862120674483494178603)
      ·
        refine ⟨58115793181011725241267905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38743862120674483494178603 58115793181011725241267905)
        ·
          refine ⟨43586844885758793930950929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58115793181011725241267905 43586844885758793930950929)
          ·
            refine ⟨32690133664319095448213197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43586844885758793930950929 32690133664319095448213197)
            ·
              refine ⟨12258800124119660793079949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32690133664319095448213197 12258800124119660793079949)
              ·
                refine ⟨4597050046544872797404981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12258800124119660793079949 4597050046544872797404981)
                ·
                  refine ⟨430973441863581824756717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597050046544872797404981 430973441863581824756717)
                  ·
                    rfl

theorem cell21_1888465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_1888465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888465 prefixEnd_1888465 := by exact prefixLift 1888465
  have htrace : WordTrace (prefixWord ++ tailWord_1888465) baseStart_1888465 baseEnd_1888465 := by
    simpa [prefixWord, tailWord_1888465, baseEnd_1888465] using wordTrace_append hprefix tailTrace_1888465
  have hstable : (prefixWord ++ tailWord_1888465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888465).length < 2 ^ (prefixWord ++ tailWord_1888465).sum := by decide
  have hdescent : baseEnd_1888465 < baseStart_1888465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888516 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_1888516 : Nat := 118140960795 + 1888516 * 2 ^ 59
def prefixEnd_1888516 : Nat := 4983230072969 + 3 ^ 40 * 1888516 * 2
def baseEnd_1888516 : Nat := 430985080758417069406613

theorem tailTrace_1888516 : CollatzResearch.WordTrace tailWord_1888516 prefixEnd_1888516 430985080758417069406613 := by
  unfold tailWord_1888516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34439918613118269849878701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45919891484157693133171601 34439918613118269849878701)
  ·
    refine ⟨12914969479919351193704513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34439918613118269849878701 12914969479919351193704513)
    ·
      refine ⟨9686227109939513395278385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12914969479919351193704513 9686227109939513395278385)
      ·
        refine ⟨7264670332454635046458789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9686227109939513395278385 7264670332454635046458789)
        ·
          refine ⟨1362125687335244071211023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7264670332454635046458789 1362125687335244071211023)
          ·
            refine ⟨2043188531002866106816535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362125687335244071211023 2043188531002866106816535)
            ·
              refine ⟨3064782796504299160224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043188531002866106816535 3064782796504299160224803)
              ·
                refine ⟨4597174194756448740337205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064782796504299160224803 4597174194756448740337205)
                ·
                  refine ⟨430985080758417069406613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597174194756448740337205 430985080758417069406613)
                  ·
                    rfl

theorem cell21_1888516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_1888516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888516 prefixEnd_1888516 := by exact prefixLift 1888516
  have htrace : WordTrace (prefixWord ++ tailWord_1888516) baseStart_1888516 baseEnd_1888516 := by
    simpa [prefixWord, tailWord_1888516, baseEnd_1888516] using wordTrace_append hprefix tailTrace_1888516
  have hstable : (prefixWord ++ tailWord_1888516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888516).length < 2 ^ (prefixWord ++ tailWord_1888516).sum := by decide
  have hdescent : baseEnd_1888516 < baseStart_1888516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888679 : List Nat := [1, 1, 6, 1, 1, 4, 7]
def baseStart_1888679 : Nat := 118140960795 + 1888679 * 2 ^ 59
def prefixEnd_1888679 : Nat := 4983230072969 + 3 ^ 40 * 1888679 * 2
def baseEnd_1888679 : Nat := 47891364397685000909957

theorem tailTrace_1888679 : CollatzResearch.WordTrace tailWord_1888679 prefixEnd_1888679 47891364397685000909957 := by
  unfold tailWord_1888679
  simp only [CollatzResearch.WordTrace]
  refine ⟨68885782324646018537941091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45923854883097345691960727 68885782324646018537941091)
  ·
    refine ⟨103328673486969027806911637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68885782324646018537941091 103328673486969027806911637)
    ·
      refine ⟨4843531569701673178448983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103328673486969027806911637 4843531569701673178448983)
      ·
        refine ⟨7265297354552509767673475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843531569701673178448983 7265297354552509767673475)
        ·
          refine ⟨10897946031828764651510213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265297354552509767673475 10897946031828764651510213)
          ·
            refine ⟨2043364880967893372158165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10897946031828764651510213 2043364880967893372158165)
            ·
              refine ⟨47891364397685000909957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2043364880967893372158165 47891364397685000909957)
              ·
                rfl

theorem cell21_1888679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 7].length) (baseStart_1888679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888679 prefixEnd_1888679 := by exact prefixLift 1888679
  have htrace : WordTrace (prefixWord ++ tailWord_1888679) baseStart_1888679 baseEnd_1888679 := by
    simpa [prefixWord, tailWord_1888679, baseEnd_1888679] using wordTrace_append hprefix tailTrace_1888679
  have hstable : (prefixWord ++ tailWord_1888679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888679).length < 2 ^ (prefixWord ++ tailWord_1888679).sum := by decide
  have hdescent : baseEnd_1888679 < baseStart_1888679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888685 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1888685 : Nat := 118140960795 + 1888685 * 2 ^ 59
def prefixEnd_1888685 : Nat := 4983230072969 + 3 ^ 40 * 1888685 * 2
def baseEnd_1888685 : Nat := 431023648860910331089601

theorem tailTrace_1888685 : CollatzResearch.WordTrace tailWord_1888685 prefixEnd_1888685 431023648860910331089601 := by
  unfold tailWord_1888685
  simp only [CollatzResearch.WordTrace]
  refine ⟨68886001162624281562659509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45924000775082854375106339 68886001162624281562659509)
  ·
    refine ⟨6458062608996026396499329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68886001162624281562659509 6458062608996026396499329)
    ·
      refine ⟨4843546956747019797374497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6458062608996026396499329 4843546956747019797374497)
      ·
        refine ⟨3632660217560264848030873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4843546956747019797374497 3632660217560264848030873)
        ·
          refine ⟨2724495163170198636023155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632660217560264848030873 2724495163170198636023155)
          ·
            refine ⟨4086742744755297954034733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724495163170198636023155 4086742744755297954034733)
            ·
              refine ⟨1532528529283236732763025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4086742744755297954034733 1532528529283236732763025)
              ·
                refine ⟨1149396396962427549572269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532528529283236732763025 1149396396962427549572269)
                ·
                  refine ⟨431023648860910331089601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149396396962427549572269 431023648860910331089601)
                  ·
                    rfl

theorem cell21_1888685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1888685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888685 prefixEnd_1888685 := by exact prefixLift 1888685
  have htrace : WordTrace (prefixWord ++ tailWord_1888685) baseStart_1888685 baseEnd_1888685 := by
    simpa [prefixWord, tailWord_1888685, baseEnd_1888685] using wordTrace_append hprefix tailTrace_1888685
  have hstable : (prefixWord ++ tailWord_1888685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888685).length < 2 ^ (prefixWord ++ tailWord_1888685).sum := by decide
  have hdescent : baseEnd_1888685 < baseStart_1888685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888744 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_1888744 : Nat := 118140960795 + 1888744 * 2 ^ 59
def prefixEnd_1888744 : Nat := 4983230072969 + 3 ^ 40 * 1888744 * 2
def baseEnd_1888744 : Nat := 431037113464739339606147

theorem tailTrace_1888744 : CollatzResearch.WordTrace tailWord_1888744 prefixEnd_1888744 431037113464739339606147 := by
  unfold tailWord_1888744
  simp only [CollatzResearch.WordTrace]
  refine ⟨34444076534705267319528643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45925435379607023092704857 34444076534705267319528643)
  ·
    refine ⟨51666114802057900979292965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34444076534705267319528643 51666114802057900979292965)
    ·
      refine ⟨9687396525385856433617431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51666114802057900979292965 9687396525385856433617431)
      ·
        refine ⟨14531094788078784650426147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687396525385856433617431 14531094788078784650426147)
        ·
          refine ⟨21796642182118176975639221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14531094788078784650426147 21796642182118176975639221)
          ·
            refine ⟨2043435204573579091466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21796642182118176975639221 2043435204573579091466177)
            ·
              refine ⟨1532576403430184318599633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043435204573579091466177 1532576403430184318599633)
              ·
                refine ⟨1149432302572638238949725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532576403430184318599633 1149432302572638238949725)
                ·
                  refine ⟨431037113464739339606147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149432302572638238949725 431037113464739339606147)
                  ·
                    rfl

theorem cell21_1888744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_1888744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888744 prefixEnd_1888744 := by exact prefixLift 1888744
  have htrace : WordTrace (prefixWord ++ tailWord_1888744) baseStart_1888744 baseEnd_1888744 := by
    simpa [prefixWord, tailWord_1888744, baseEnd_1888744] using wordTrace_append hprefix tailTrace_1888744
  have hstable : (prefixWord ++ tailWord_1888744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888744).length < 2 ^ (prefixWord ++ tailWord_1888744).sum := by decide
  have hdescent : baseEnd_1888744 < baseStart_1888744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888769 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1888769 : Nat := 118140960795 + 1888769 * 2 ^ 59
def prefixEnd_1888769 : Nat := 4983230072969 + 3 ^ 40 * 1888769 * 2
def baseEnd_1888769 : Nat := 431042818805344851689429

theorem tailTrace_1888769 : CollatzResearch.WordTrace tailWord_1888769 prefixEnd_1888769 431042818805344851689429 := by
  unfold tailWord_1888769
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889064894319963908717361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45926043262879975939144907 68889064894319963908717361)
  ·
    refine ⟨51666798670739972931538021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68889064894319963908717361 51666798670739972931538021)
    ·
      refine ⟨9687524750763744924663379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51666798670739972931538021 9687524750763744924663379)
      ·
        refine ⟨14531287126145617386995069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687524750763744924663379 14531287126145617386995069)
        ·
          refine ⟨5449232672304606520123151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14531287126145617386995069 5449232672304606520123151)
          ·
            refine ⟨8173849008456909780184727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449232672304606520123151 8173849008456909780184727)
            ·
              refine ⟨12260773512685364670277091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173849008456909780184727 12260773512685364670277091)
              ·
                refine ⟨18391160269028047005415637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260773512685364670277091 18391160269028047005415637)
                ·
                  refine ⟨431042818805344851689429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18391160269028047005415637 431042818805344851689429)
                  ·
                    rfl

theorem cell21_1888769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1888769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888769 prefixEnd_1888769 := by exact prefixLift 1888769
  have htrace : WordTrace (prefixWord ++ tailWord_1888769) baseStart_1888769 baseEnd_1888769 := by
    simpa [prefixWord, tailWord_1888769, baseEnd_1888769] using wordTrace_append hprefix tailTrace_1888769
  have hstable : (prefixWord ++ tailWord_1888769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888769).length < 2 ^ (prefixWord ++ tailWord_1888769).sum := by decide
  have hdescent : baseEnd_1888769 < baseStart_1888769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888772 : List Nat := [2, 3, 2, 3, 1, 2, 3, 5]
def baseStart_1888772 : Nat := 118140960795 + 1888772 * 2 ^ 59
def prefixEnd_1888772 : Nat := 4983230072969 + 3 ^ 40 * 1888772 * 2
def baseEnd_1888772 : Nat := 143681167815405837713141

theorem tailTrace_1888772 : CollatzResearch.WordTrace tailWord_1888772 prefixEnd_1888772 143681167815405837713141 := by
  unfold tailWord_1888772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34444587156654547710538285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45926116208872730280717713 34444587156654547710538285)
  ·
    refine ⟨12916720183745455391451857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34444587156654547710538285 12916720183745455391451857)
    ·
      refine ⟨9687540137809091543588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12916720183745455391451857 9687540137809091543588893)
      ·
        refine ⟨3632827551678409328845835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9687540137809091543588893 3632827551678409328845835)
        ·
          refine ⟨5449241327517613993268753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632827551678409328845835 5449241327517613993268753)
          ·
            refine ⟨4086930995638210494951565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5449241327517613993268753 4086930995638210494951565)
            ·
              refine ⟨1532599123364328935606837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4086930995638210494951565 1532599123364328935606837)
              ·
                refine ⟨143681167815405837713141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1532599123364328935606837 143681167815405837713141)
                ·
                  rfl

theorem cell21_1888772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_1888772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888772 prefixEnd_1888772 := by exact prefixLift 1888772
  have htrace : WordTrace (prefixWord ++ tailWord_1888772) baseStart_1888772 baseEnd_1888772 := by
    simpa [prefixWord, tailWord_1888772, baseEnd_1888772] using wordTrace_append hprefix tailTrace_1888772
  have hstable : (prefixWord ++ tailWord_1888772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888772).length < 2 ^ (prefixWord ++ tailWord_1888772).sum := by decide
  have hdescent : baseEnd_1888772 < baseStart_1888772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888997 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1888997 : Nat := 118140960795 + 1888997 * 2 ^ 59
def prefixEnd_1888997 : Nat := 4983230072969 + 3 ^ 40 * 1888997 * 2
def baseEnd_1888997 : Nat := 431094851511667121888963

theorem tailTrace_1888997 : CollatzResearch.WordTrace tailWord_1888997 prefixEnd_1888997 431094851511667121888963 := by
  unfold tailWord_1888997
  simp only [CollatzResearch.WordTrace]
  refine ⟨68897380737493958848017245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45931587158329305898678163 68897380737493958848017245)
  ·
    refine ⟨25836517776560234568006467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68897380737493958848017245 25836517776560234568006467)
    ·
      refine ⟨38754776664840351852009701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25836517776560234568006467 38754776664840351852009701)
      ·
        refine ⟨7266520624657565972251819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38754776664840351852009701 7266520624657565972251819)
        ·
          refine ⟨10899780936986348958377729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266520624657565972251819 10899780936986348958377729)
          ·
            refine ⟨8174835702739761718783297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10899780936986348958377729 8174835702739761718783297)
            ·
              refine ⟨6131126777054821289087473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174835702739761718783297 6131126777054821289087473)
              ·
                refine ⟨4598345082791115966815605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6131126777054821289087473 4598345082791115966815605)
                ·
                  refine ⟨431094851511667121888963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4598345082791115966815605 431094851511667121888963)
                  ·
                    rfl

theorem cell21_1888997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1888997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1888997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1888997 prefixEnd_1888997 := by exact prefixLift 1888997
  have htrace : WordTrace (prefixWord ++ tailWord_1888997) baseStart_1888997 baseEnd_1888997 := by
    simpa [prefixWord, tailWord_1888997, baseEnd_1888997] using wordTrace_append hprefix tailTrace_1888997
  have hstable : (prefixWord ++ tailWord_1888997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888997).length < 2 ^ (prefixWord ++ tailWord_1888997).sum := by decide
  have hdescent : baseEnd_1888997 < baseStart_1888997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889000 : List Nat := [2, 1, 4, 1, 4, 2, 2, 5]
def baseStart_1889000 : Nat := 118140960795 + 1889000 * 2 ^ 59
def prefixEnd_1889000 : Nat := 4983230072969 + 3 ^ 40 * 1889000 * 2
def baseEnd_1889000 : Nat := 143698512050846594446319

theorem tailTrace_1889000 : CollatzResearch.WordTrace tailWord_1889000 prefixEnd_1889000 143698512050846594446319 := by
  unfold tailWord_1889000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34448745078241545180188227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45931660104322060240250969 34448745078241545180188227)
  ·
    refine ⟨51673117617362317770282341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34448745078241545180188227 51673117617362317770282341)
    ·
      refine ⟨9688709553255434581927939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51673117617362317770282341 9688709553255434581927939)
      ·
        refine ⟨14533064329883151872891909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688709553255434581927939 14533064329883151872891909)
        ·
          refine ⟨2724949561853090976167233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14533064329883151872891909 2724949561853090976167233)
          ·
            refine ⟨2043712171389818232125425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2724949561853090976167233 2043712171389818232125425)
            ·
              refine ⟨1532784128542363674094069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043712171389818232125425 1532784128542363674094069)
              ·
                refine ⟨143698512050846594446319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1532784128542363674094069 143698512050846594446319)
                ·
                  rfl

theorem cell21_1889000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_1889000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889000 prefixEnd_1889000 := by exact prefixLift 1889000
  have htrace : WordTrace (prefixWord ++ tailWord_1889000) baseStart_1889000 baseEnd_1889000 := by
    simpa [prefixWord, tailWord_1889000, baseEnd_1889000] using wordTrace_append hprefix tailTrace_1889000
  have hstable : (prefixWord ++ tailWord_1889000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889000).length < 2 ^ (prefixWord ++ tailWord_1889000).sum := by decide
  have hdescent : baseEnd_1889000 < baseStart_1889000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889028 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1889028 : Nat := 118140960795 + 1889028 * 2 ^ 59
def prefixEnd_1889028 : Nat := 4983230072969 + 3 ^ 40 * 1889028 * 2
def baseEnd_1889028 : Nat := 431101926134017956872233

theorem tailTrace_1889028 : CollatzResearch.WordTrace tailWord_1889028 prefixEnd_1889028 431101926134017956872233 := by
  unfold tailWord_1889028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34449255700190825571197869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45932340933587767428263825 34449255700190825571197869)
  ·
    refine ⟨12918470887571559589199201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34449255700190825571197869 12918470887571559589199201)
    ·
      refine ⟨9688853165678669691899401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12918470887571559589199201 9688853165678669691899401)
      ·
        refine ⟨7266639874259002268924551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9688853165678669691899401 7266639874259002268924551)
        ·
          refine ⟨10899959811388503403386827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266639874259002268924551 10899959811388503403386827)
          ·
            refine ⟨16349939717082755105080241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899959811388503403386827 16349939717082755105080241)
            ·
              refine ⟨12262454787812066328810181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16349939717082755105080241 12262454787812066328810181)
              ·
                refine ⟨2299210272714762436651909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12262454787812066328810181 2299210272714762436651909)
                ·
                  refine ⟨431101926134017956872233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299210272714762436651909 431101926134017956872233)
                  ·
                    rfl

theorem cell21_1889028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1889028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889028 prefixEnd_1889028 := by exact prefixLift 1889028
  have htrace : WordTrace (prefixWord ++ tailWord_1889028) baseStart_1889028 baseEnd_1889028 := by
    simpa [prefixWord, tailWord_1889028, baseEnd_1889028] using wordTrace_append hprefix tailTrace_1889028
  have hstable : (prefixWord ++ tailWord_1889028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889028).length < 2 ^ (prefixWord ++ tailWord_1889028).sum := by decide
  have hdescent : baseEnd_1889028 < baseStart_1889028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889132 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1889132 : Nat := 118140960795 + 1889132 * 2 ^ 59
def prefixEnd_1889132 : Nat := 4983230072969 + 3 ^ 40 * 1889132 * 2
def baseEnd_1889132 : Nat := 431125660350936887138687

theorem tailTrace_1889132 : CollatzResearch.WordTrace tailWord_1889132 prefixEnd_1889132 431125660350936887138687 := by
  unfold tailWord_1889132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451152296002438452090825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45934869728003251269454433 34451152296002438452090825)
  ·
    refine ⟨25838364222001828839068119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34451152296002438452090825 25838364222001828839068119)
    ·
      refine ⟨38757546333002743258602179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25838364222001828839068119 38757546333002743258602179)
      ·
        refine ⟨58136319499504114887903269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38757546333002743258602179 58136319499504114887903269)
        ·
          refine ⟨10900559906157021541481863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58136319499504114887903269 10900559906157021541481863)
          ·
            refine ⟨16350839859235532312222795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900559906157021541481863 16350839859235532312222795)
            ·
              refine ⟨24526259788853298468334193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16350839859235532312222795 24526259788853298468334193)
              ·
                refine ⟨18394694841639973851250645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24526259788853298468334193 18394694841639973851250645)
                ·
                  refine ⟨431125660350936887138687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18394694841639973851250645 431125660350936887138687)
                  ·
                    rfl

theorem cell21_1889132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1889132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889132 prefixEnd_1889132 := by exact prefixLift 1889132
  have htrace : WordTrace (prefixWord ++ tailWord_1889132) baseStart_1889132 baseEnd_1889132 := by
    simpa [prefixWord, tailWord_1889132, baseEnd_1889132] using wordTrace_append hprefix tailTrace_1889132
  have hstable : (prefixWord ++ tailWord_1889132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889132).length < 2 ^ (prefixWord ++ tailWord_1889132).sum := by decide
  have hdescent : baseEnd_1889132 < baseStart_1889132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889163 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_1889163 : Nat := 118140960795 + 1889163 * 2 ^ 59
def prefixEnd_1889163 : Nat := 4983230072969 + 3 ^ 40 * 1889163 * 2
def baseEnd_1889163 : Nat := 431132734973287722121957

theorem tailTrace_1889163 : CollatzResearch.WordTrace tailWord_1889163 prefixEnd_1889163 431132734973287722121957 := by
  unfold tailWord_1889163
  simp only [CollatzResearch.WordTrace]
  refine ⟨68903435254892569198560143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45935623503261712799040095 68903435254892569198560143)
  ·
    refine ⟨103355152882338853797840215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68903435254892569198560143 103355152882338853797840215)
    ·
      refine ⟨155032729323508280696760323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103355152882338853797840215 155032729323508280696760323)
      ·
        refine ⟨232549093985262421045140485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155032729323508280696760323 232549093985262421045140485)
        ·
          refine ⟨43602955122236703945963841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232549093985262421045140485 43602955122236703945963841)
          ·
            refine ⟨32702216341677527959472881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43602955122236703945963841 32702216341677527959472881)
            ·
              refine ⟨24526662256258145969604661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32702216341677527959472881 24526662256258145969604661)
              ·
                refine ⟨2299374586524201184650437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24526662256258145969604661 2299374586524201184650437)
                ·
                  refine ⟨431132734973287722121957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299374586524201184650437 431132734973287722121957)
                  ·
                    rfl

theorem cell21_1889163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_1889163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889163 prefixEnd_1889163 := by exact prefixLift 1889163
  have htrace : WordTrace (prefixWord ++ tailWord_1889163) baseStart_1889163 baseEnd_1889163 := by
    simpa [prefixWord, tailWord_1889163, baseEnd_1889163] using wordTrace_append hprefix tailTrace_1889163
  have hstable : (prefixWord ++ tailWord_1889163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889163).length < 2 ^ (prefixWord ++ tailWord_1889163).sum := by decide
  have hdescent : baseEnd_1889163 < baseStart_1889163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889183 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 3]
def baseStart_1889183 : Nat := 118140960795 + 1889183 * 2 ^ 59
def prefixEnd_1889183 : Nat := 4983230072969 + 3 ^ 40 * 1889183 * 2
def baseEnd_1889183 : Nat := 431137299245772131788583

theorem tailTrace_1889183 : CollatzResearch.WordTrace tailWord_1889183 prefixEnd_1889183 431137299245772131788583 := by
  unfold tailWord_1889183
  simp only [CollatzResearch.WordTrace]
  refine ⟨68904164714820112614288203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45936109809880075076192135 68904164714820112614288203)
  ·
    refine ⟨103356247072230168921432305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68904164714820112614288203 103356247072230168921432305)
    ·
      refine ⟨77517185304172626691074229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103356247072230168921432305 77517185304172626691074229)
      ·
        refine ⟨7267236122266183752288209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77517185304172626691074229 7267236122266183752288209)
        ·
          refine ⟨5450427091699637814216157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267236122266183752288209 5450427091699637814216157)
          ·
            refine ⟨2043910159387364180331059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450427091699637814216157 2043910159387364180331059)
            ·
              refine ⟨3065865239081046270496589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043910159387364180331059 3065865239081046270496589)
              ·
                refine ⟨1149699464655392351436221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3065865239081046270496589 1149699464655392351436221)
                ·
                  refine ⟨431137299245772131788583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149699464655392351436221 431137299245772131788583)
                  ·
                    rfl

theorem cell21_1889183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].length) (baseStart_1889183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889183 prefixEnd_1889183 := by exact prefixLift 1889183
  have htrace : WordTrace (prefixWord ++ tailWord_1889183) baseStart_1889183 baseEnd_1889183 := by
    simpa [prefixWord, tailWord_1889183, baseEnd_1889183] using wordTrace_append hprefix tailTrace_1889183
  have hstable : (prefixWord ++ tailWord_1889183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889183).length < 2 ^ (prefixWord ++ tailWord_1889183).sum := by decide
  have hdescent : baseEnd_1889183 < baseStart_1889183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889315 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_1889315 : Nat := 118140960795 + 1889315 * 2 ^ 59
def prefixEnd_1889315 : Nat := 4983230072969 + 3 ^ 40 * 1889315 * 2
def baseEnd_1889315 : Nat := 431167423444169235588313

theorem tailTrace_1889315 : CollatzResearch.WordTrace tailWord_1889315 prefixEnd_1889315 431167423444169235588313 := by
  unfold tailWord_1889315
  simp only [CollatzResearch.WordTrace]
  refine ⟨68908979150341899158093399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45939319433561266105395599 68908979150341899158093399)
  ·
    refine ⟨103363468725512848737140099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68908979150341899158093399 103363468725512848737140099)
    ·
      refine ⟨155045203088269273105710149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103363468725512848737140099 155045203088269273105710149)
      ·
        refine ⟨29070975579050488707320653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155045203088269273105710149 29070975579050488707320653)
        ·
          refine ⟨10901615842143933265245245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29070975579050488707320653 10901615842143933265245245)
          ·
            refine ⟨4088105940803974974466967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10901615842143933265245245 4088105940803974974466967)
            ·
              refine ⟨6132158911205962461700451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088105940803974974466967 6132158911205962461700451)
              ·
                refine ⟨9198238366808943692550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132158911205962461700451 9198238366808943692550677)
                ·
                  refine ⟨431167423444169235588313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9198238366808943692550677 431167423444169235588313)
                  ·
                    rfl

theorem cell21_1889315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_1889315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889315 prefixEnd_1889315 := by exact prefixLift 1889315
  have htrace : WordTrace (prefixWord ++ tailWord_1889315) baseStart_1889315 baseEnd_1889315 := by
    simpa [prefixWord, tailWord_1889315, baseEnd_1889315] using wordTrace_append hprefix tailTrace_1889315
  have hstable : (prefixWord ++ tailWord_1889315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889315).length < 2 ^ (prefixWord ++ tailWord_1889315).sum := by decide
  have hdescent : baseEnd_1889315 < baseStart_1889315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889329 : List Nat := [1, 2, 2, 3, 1, 2, 2, 8]
def baseStart_1889329 : Nat := 118140960795 + 1889329 * 2 ^ 59
def prefixEnd_1889329 : Nat := 4983230072969 + 3 ^ 40 * 1889329 * 2
def baseEnd_1889329 : Nat := 143723539478302774118317

theorem tailTrace_1889329 : CollatzResearch.WordTrace tailWord_1889329 prefixEnd_1889329 143723539478302774118317 := by
  unfold tailWord_1889329
  simp only [CollatzResearch.WordTrace]
  refine ⟨68909489772291179549103041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45939659848194119699402027 68909489772291179549103041)
  ·
    refine ⟨51682117329218384661827281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68909489772291179549103041 51682117329218384661827281)
    ·
      refine ⟨38761587996913788496370461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51682117329218384661827281 38761587996913788496370461)
      ·
        refine ⟨14535595498842670686138923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38761587996913788496370461 14535595498842670686138923)
        ·
          refine ⟨21803393248264006029208385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14535595498842670686138923 21803393248264006029208385)
          ·
            refine ⟨16352544936198004521906289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21803393248264006029208385 16352544936198004521906289)
            ·
              refine ⟨12264408702148503391429717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16352544936198004521906289 12264408702148503391429717)
              ·
                refine ⟨143723539478302774118317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12264408702148503391429717 143723539478302774118317)
                ·
                  rfl

theorem cell21_1889329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_1889329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889329 prefixEnd_1889329 := by exact prefixLift 1889329
  have htrace : WordTrace (prefixWord ++ tailWord_1889329) baseStart_1889329 baseEnd_1889329 := by
    simpa [prefixWord, tailWord_1889329, baseEnd_1889329] using wordTrace_append hprefix tailTrace_1889329
  have hstable : (prefixWord ++ tailWord_1889329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889329).length < 2 ^ (prefixWord ++ tailWord_1889329).sum := by decide
  have hdescent : baseEnd_1889329 < baseStart_1889329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889377 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 3]
def baseStart_1889377 : Nat := 118140960795 + 1889377 * 2 ^ 59
def prefixEnd_1889377 : Nat := 4983230072969 + 3 ^ 40 * 1889377 * 2
def baseEnd_1889377 : Nat := 431181572688870905554853

theorem tailTrace_1889377 : CollatzResearch.WordTrace tailWord_1889377 prefixEnd_1889377 431181572688870905554853 := by
  unfold tailWord_1889377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68911240476117283746850385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45940826984078189164566923 68911240476117283746850385)
  ·
    refine ⟨51683430357087962810137789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68911240476117283746850385 51683430357087962810137789)
    ·
      refine ⟨19381286383907986053801671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51683430357087962810137789 19381286383907986053801671)
      ·
        refine ⟨29071929575861979080702507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381286383907986053801671 29071929575861979080702507)
        ·
          refine ⟨43607894363792968621053761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29071929575861979080702507 43607894363792968621053761)
          ·
            refine ⟨32705920772844726465790321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43607894363792968621053761 32705920772844726465790321)
            ·
              refine ⟨24529440579633544849342741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32705920772844726465790321 24529440579633544849342741)
              ·
                refine ⟨1149817527170322414812941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24529440579633544849342741 1149817527170322414812941)
                ·
                  refine ⟨431181572688870905554853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149817527170322414812941 431181572688870905554853)
                  ·
                    rfl

theorem cell21_1889377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_1889377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889377 prefixEnd_1889377 := by exact prefixLift 1889377
  have htrace : WordTrace (prefixWord ++ tailWord_1889377) baseStart_1889377 baseEnd_1889377 := by
    simpa [prefixWord, tailWord_1889377, baseEnd_1889377] using wordTrace_append hprefix tailTrace_1889377
  have hstable : (prefixWord ++ tailWord_1889377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889377).length < 2 ^ (prefixWord ++ tailWord_1889377).sum := by decide
  have hdescent : baseEnd_1889377 < baseStart_1889377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889391 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_1889391 : Nat := 118140960795 + 1889391 * 2 ^ 59
def prefixEnd_1889391 : Nat := 4983230072969 + 3 ^ 40 * 1889391 * 2
def baseEnd_1889391 : Nat := 431184767679609992321491

theorem tailTrace_1889391 : CollatzResearch.WordTrace tailWord_1889391 prefixEnd_1889391 431184767679609992321491 := by
  unfold tailWord_1889391
  simp only [CollatzResearch.WordTrace]
  refine ⟨68911751098066564137860027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45941167398711042758573351 68911751098066564137860027)
  ·
    refine ⟨103367626647099846206790041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68911751098066564137860027 103367626647099846206790041)
    ·
      refine ⟨77525719985324884655092531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103367626647099846206790041 77525719985324884655092531)
      ·
        refine ⟨116288579977987326982638797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77525719985324884655092531 116288579977987326982638797)
        ·
          refine ⟨43608217491745247618489549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116288579977987326982638797 43608217491745247618489549)
          ·
            refine ⟨16353081559404467856933581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43608217491745247618489549 16353081559404467856933581)
            ·
              refine ⟨6132405584776675446350093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16353081559404467856933581 6132405584776675446350093)
              ·
                refine ⟨2299652094291253292381285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6132405584776675446350093 2299652094291253292381285)
                ·
                  refine ⟨431184767679609992321491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299652094291253292381285 431184767679609992321491)
                  ·
                    rfl

theorem cell21_1889391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_1889391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889391 prefixEnd_1889391 := by exact prefixLift 1889391
  have htrace : WordTrace (prefixWord ++ tailWord_1889391) baseStart_1889391 baseEnd_1889391 := by
    simpa [prefixWord, tailWord_1889391, baseEnd_1889391] using wordTrace_append hprefix tailTrace_1889391
  have hstable : (prefixWord ++ tailWord_1889391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889391).length < 2 ^ (prefixWord ++ tailWord_1889391).sum := by decide
  have hdescent : baseEnd_1889391 < baseStart_1889391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889405 : List Nat := [1, 4, 1, 1, 3, 1, 1, 9]
def baseStart_1889405 : Nat := 118140960795 + 1889405 * 2 ^ 59
def prefixEnd_1889405 : Nat := 4983230072969 + 3 ^ 40 * 1889405 * 2
def baseEnd_1889405 : Nat := 143729320890116359696043

theorem tailTrace_1889405 : CollatzResearch.WordTrace tailWord_1889405 prefixEnd_1889405 143729320890116359696043 := by
  unfold tailWord_1889405
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912261720015844528869669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45941507813343896352579779 68912261720015844528869669)
  ·
    refine ⟨12921049072502970849163063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68912261720015844528869669 12921049072502970849163063)
    ·
      refine ⟨19381573608754456273744595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921049072502970849163063 19381573608754456273744595)
      ·
        refine ⟨29072360413131684410616893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381573608754456273744595 29072360413131684410616893)
        ·
          refine ⟨10902135154924381653981335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29072360413131684410616893 10902135154924381653981335)
          ·
            refine ⟨16353202732386572480972003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902135154924381653981335 16353202732386572480972003)
            ·
              refine ⟨24529804098579858721458005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16353202732386572480972003 24529804098579858721458005)
              ·
                refine ⟨143729320890116359696043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24529804098579858721458005 143729320890116359696043)
                ·
                  rfl

theorem cell21_1889405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_1889405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889405 prefixEnd_1889405 := by exact prefixLift 1889405
  have htrace : WordTrace (prefixWord ++ tailWord_1889405) baseStart_1889405 baseEnd_1889405 := by
    simpa [prefixWord, tailWord_1889405, baseEnd_1889405] using wordTrace_append hprefix tailTrace_1889405
  have hstable : (prefixWord ++ tailWord_1889405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889405).length < 2 ^ (prefixWord ++ tailWord_1889405).sum := by decide
  have hdescent : baseEnd_1889405 < baseStart_1889405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889439 : List Nat := [1, 1, 2, 6, 2, 2, 1, 6]
def baseStart_1889439 : Nat := 118140960795 + 1889439 * 2 ^ 59
def prefixEnd_1889439 : Nat := 4983230072969 + 3 ^ 40 * 1889439 * 2
def baseEnd_1889439 : Nat := 143731907311190858507131

theorem tailTrace_1889439 : CollatzResearch.WordTrace tailWord_1889439 prefixEnd_1889439 143731907311190858507131 := by
  unfold tailWord_1889439
  simp only [CollatzResearch.WordTrace]
  refine ⟨68913501801892668335607371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45942334534595112223738247 68913501801892668335607371)
  ·
    refine ⟨103370252702839002503411057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68913501801892668335607371 103370252702839002503411057)
    ·
      refine ⟨77527689527129251877558293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103370252702839002503411057 77527689527129251877558293)
      ·
        refine ⟨3634110446584183681760545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77527689527129251877558293 3634110446584183681760545)
        ·
          refine ⟨2725582834938137761320409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634110446584183681760545 2725582834938137761320409)
          ·
            refine ⟨2044187126203603320990307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725582834938137761320409 2044187126203603320990307)
            ·
              refine ⟨3066280689305404981485461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044187126203603320990307 3066280689305404981485461)
              ·
                refine ⟨143731907311190858507131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3066280689305404981485461 143731907311190858507131)
                ·
                  rfl

theorem cell21_1889439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_1889439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889439 prefixEnd_1889439 := by exact prefixLift 1889439
  have htrace : WordTrace (prefixWord ++ tailWord_1889439) baseStart_1889439 baseEnd_1889439 := by
    simpa [prefixWord, tailWord_1889439, baseEnd_1889439] using wordTrace_append hprefix tailTrace_1889439
  have hstable : (prefixWord ++ tailWord_1889439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889439).length < 2 ^ (prefixWord ++ tailWord_1889439).sum := by decide
  have hdescent : baseEnd_1889439 < baseStart_1889439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889470 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1889470 : Nat := 118140960795 + 1889470 * 2 ^ 59
def prefixEnd_1889470 : Nat := 4983230072969 + 3 ^ 40 * 1889470 * 2
def baseEnd_1889470 : Nat := 431202796555923410504663

theorem tailTrace_1889470 : CollatzResearch.WordTrace tailWord_1889470 prefixEnd_1889470 431202796555923410504663 := by
  unfold tailWord_1889470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614329058097545078748233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45943088309853573753323909 8614329058097545078748233)
  ·
    refine ⟨6460746793573158809061175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8614329058097545078748233 6460746793573158809061175)
    ·
      refine ⟨9691120190359738213591763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460746793573158809061175 9691120190359738213591763)
      ·
        refine ⟨14536680285539607320387645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691120190359738213591763 14536680285539607320387645)
        ·
          refine ⟨5451255107077352745145367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14536680285539607320387645 5451255107077352745145367)
          ·
            refine ⟨8176882660616029117718051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451255107077352745145367 8176882660616029117718051)
            ·
              refine ⟨12265323990924043676577077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176882660616029117718051 12265323990924043676577077)
              ·
                refine ⟨1149874124149129094679101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12265323990924043676577077 1149874124149129094679101)
                ·
                  refine ⟨431202796555923410504663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149874124149129094679101 431202796555923410504663)
                  ·
                    rfl

theorem cell21_1889470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1889470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889470 prefixEnd_1889470 := by exact prefixLift 1889470
  have htrace : WordTrace (prefixWord ++ tailWord_1889470) baseStart_1889470 baseEnd_1889470 := by
    simpa [prefixWord, tailWord_1889470, baseEnd_1889470] using wordTrace_append hprefix tailTrace_1889470
  have hstable : (prefixWord ++ tailWord_1889470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889470).length < 2 ^ (prefixWord ++ tailWord_1889470).sum := by decide
  have hdescent : baseEnd_1889470 < baseStart_1889470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889512 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1889512 : Nat := 118140960795 + 1889512 * 2 ^ 59
def prefixEnd_1889512 : Nat := 4983230072969 + 3 ^ 40 * 1889512 * 2
def baseEnd_1889512 : Nat := 431212381528140670804577

theorem tailTrace_1889512 : CollatzResearch.WordTrace tailWord_1889512 prefixEnd_1889512 431212381528140670804577 := by
  unfold tailWord_1889512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34458082165314100901507395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45944109553752134535343193 34458082165314100901507395)
  ·
    refine ⟨51687123247971151352261093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34458082165314100901507395 51687123247971151352261093)
    ·
      refine ⟨9691335608994590878548955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51687123247971151352261093 9691335608994590878548955)
      ·
        refine ⟨14537003413491886317823433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691335608994590878548955 14537003413491886317823433)
        ·
          refine ⟨10902752560118914738367575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537003413491886317823433 10902752560118914738367575)
          ·
            refine ⟨16354128840178372107551363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902752560118914738367575 16354128840178372107551363)
            ·
              refine ⟨24531193260267558161327045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354128840178372107551363 24531193260267558161327045)
              ·
                refine ⟨4599598736300167155248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24531193260267558161327045 4599598736300167155248821)
                ·
                  refine ⟨431212381528140670804577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599598736300167155248821 431212381528140670804577)
                  ·
                    rfl

theorem cell21_1889512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1889512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889512 prefixEnd_1889512 := by exact prefixLift 1889512
  have htrace : WordTrace (prefixWord ++ tailWord_1889512) baseStart_1889512 baseEnd_1889512 := by
    simpa [prefixWord, tailWord_1889512, baseEnd_1889512] using wordTrace_append hprefix tailTrace_1889512
  have hstable : (prefixWord ++ tailWord_1889512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889512).length < 2 ^ (prefixWord ++ tailWord_1889512).sum := by decide
  have hdescent : baseEnd_1889512 < baseStart_1889512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889560 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_1889560 : Nat := 118140960795 + 1889560 * 2 ^ 59
def prefixEnd_1889560 : Nat := 4983230072969 + 3 ^ 40 * 1889560 * 2
def baseEnd_1889560 : Nat := 431223335782103254004479

theorem tailTrace_1889560 : CollatzResearch.WordTrace tailWord_1889560 prefixEnd_1889560 431223335782103254004479 := by
  unfold tailWord_1889560
  simp only [CollatzResearch.WordTrace]
  refine ⟨34458957517227153000381067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45945276689636204000508089 34458957517227153000381067)
  ·
    refine ⟨51688436275840729500571601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34458957517227153000381067 51688436275840729500571601)
    ·
      refine ⟨38766327206880547125428701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51688436275840729500571601 38766327206880547125428701)
      ·
        refine ⟨14537372702580205172035763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38766327206880547125428701 14537372702580205172035763)
        ·
          refine ⟨21806059053870307758053645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537372702580205172035763 21806059053870307758053645)
          ·
            refine ⟨8177272145201365409270117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21806059053870307758053645 8177272145201365409270117)
            ·
              refine ⟨1533238527225256014238147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8177272145201365409270117 1533238527225256014238147)
              ·
                refine ⟨2299857790837884021357221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533238527225256014238147 2299857790837884021357221)
                ·
                  refine ⟨431223335782103254004479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299857790837884021357221 431223335782103254004479)
                  ·
                    rfl

theorem cell21_1889560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_1889560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889560 prefixEnd_1889560 := by exact prefixLift 1889560
  have htrace : WordTrace (prefixWord ++ tailWord_1889560) baseStart_1889560 baseEnd_1889560 := by
    simpa [prefixWord, tailWord_1889560, baseEnd_1889560] using wordTrace_append hprefix tailTrace_1889560
  have hstable : (prefixWord ++ tailWord_1889560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889560).length < 2 ^ (prefixWord ++ tailWord_1889560).sum := by decide
  have hdescent : baseEnd_1889560 < baseStart_1889560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
