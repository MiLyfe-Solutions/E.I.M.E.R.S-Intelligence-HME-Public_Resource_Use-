import V185TrunkScan22Chunk402

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3594915 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_3594915 : Nat := 118140960795 + 3594915 * 2 ^ 59
def prefixEnd_3594915 : Nat := 4983230072969 + 3 ^ 40 * 3594915 * 2
def baseEnd_3594915 : Nat := 1230612871371938408153195

theorem tailTrace_3594915 : CollatzResearch.WordTrace tailWord_3594915 prefixEnd_3594915 1230612871371938408153195 := by
  unfold tailWord_3594915
  simp only [CollatzResearch.WordTrace]
  refine ⟨131117321771244392447050199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87411547847496261631366799 131117321771244392447050199)
  ·
    refine ⟨196675982656866588670575299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131117321771244392447050199 196675982656866588670575299)
    ·
      refine ⟨295013973985299883005862949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196675982656866588670575299 295013973985299883005862949)
      ·
        refine ⟨55315120122243728063599303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295013973985299883005862949 55315120122243728063599303)
        ·
          refine ⟨82972680183365592095398955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55315120122243728063599303 82972680183365592095398955)
          ·
            refine ⟨124459020275048388143098433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82972680183365592095398955 124459020275048388143098433)
            ·
              refine ⟨93344265206286291107323825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124459020275048388143098433 93344265206286291107323825)
              ·
                refine ⟨70008198904714718330492869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93344265206286291107323825 70008198904714718330492869)
                ·
                  refine ⟨13126537294634009686967413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70008198904714718330492869 13126537294634009686967413)
                  ·
                    refine ⟨1230612871371938408153195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13126537294634009686967413 1230612871371938408153195)
                    ·
                      rfl

theorem cell22_3594915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_3594915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594915 prefixEnd_3594915 := by exact prefixLift 3594915
  have htrace : WordTrace (prefixWord ++ tailWord_3594915) baseStart_3594915 baseEnd_3594915 := by
    simpa [prefixWord, tailWord_3594915, baseEnd_3594915] using wordTrace_append hprefix tailTrace_3594915
  have hstable : (prefixWord ++ tailWord_3594915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594915).length < 2 ^ (prefixWord ++ tailWord_3594915).sum := by decide
  have hdescent : baseEnd_3594915 < baseStart_3594915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594977 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3594977 : Nat := 118140960795 + 3594977 * 2 ^ 59
def prefixEnd_3594977 : Nat := 4983230072969 + 3 ^ 40 * 3594977 * 2
def baseEnd_3594977 : Nat := 1230634095238990913103005

theorem tailTrace_3594977 : CollatzResearch.WordTrace tailWord_3594977 prefixEnd_3594977 1230634095238990913103005 := by
  unfold tailWord_3594977
  simp only [CollatzResearch.WordTrace]
  refine ⟨131119583097019777035807185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87413055398013184690538123 131119583097019777035807185)
  ·
    refine ⟨98339687322764832776855389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131119583097019777035807185 98339687322764832776855389)
    ·
      refine ⟨36877382746036812291320771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98339687322764832776855389 36877382746036812291320771)
      ·
        refine ⟨55316074119055218436981157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36877382746036812291320771 55316074119055218436981157)
        ·
          refine ⟨10371763897322853456933967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55316074119055218436981157 10371763897322853456933967)
          ·
            refine ⟨15557645845984280185400951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10371763897322853456933967 15557645845984280185400951)
            ·
              refine ⟨23336468768976420278101427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15557645845984280185400951 23336468768976420278101427)
              ·
                refine ⟨35004703153464630417152141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23336468768976420278101427 35004703153464630417152141)
                ·
                  refine ⟨13126763682549236406432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35004703153464630417152141 13126763682549236406432053)
                  ·
                    refine ⟨1230634095238990913103005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13126763682549236406432053 1230634095238990913103005)
                    ·
                      rfl

theorem cell22_3594977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3594977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594977 prefixEnd_3594977 := by exact prefixLift 3594977
  have htrace : WordTrace (prefixWord ++ tailWord_3594977) baseStart_3594977 baseEnd_3594977 := by
    simpa [prefixWord, tailWord_3594977, baseEnd_3594977] using wordTrace_append hprefix tailTrace_3594977
  have hstable : (prefixWord ++ tailWord_3594977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594977).length < 2 ^ (prefixWord ++ tailWord_3594977).sum := by decide
  have hdescent : baseEnd_3594977 < baseStart_3594977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594981 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_3594981 : Nat := 118140960795 + 3594981 * 2 ^ 59
def prefixEnd_3594981 : Nat := 4983230072969 + 3 ^ 40 * 3594981 * 2
def baseEnd_3594981 : Nat := 1230635464520736236002993

theorem tailTrace_3594981 : CollatzResearch.WordTrace tailWord_3594981 prefixEnd_3594981 1230635464520736236002993 := by
  unfold tailWord_3594981
  simp only [CollatzResearch.WordTrace]
  refine ⟨131119728989005285718952797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87413152659336857145968531 131119728989005285718952797)
  ·
    refine ⟨49169898370876982144607299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131119728989005285718952797 49169898370876982144607299)
    ·
      refine ⟨73754847556315473216910949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49169898370876982144607299 73754847556315473216910949)
      ·
        refine ⟨13829033916809151228170803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73754847556315473216910949 13829033916809151228170803)
        ·
          refine ⟨20743550875213726842256205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829033916809151228170803 20743550875213726842256205)
          ·
            refine ⟨7778831578205147565846077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20743550875213726842256205 7778831578205147565846077)
            ·
              refine ⟨2917061841826930337192279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7778831578205147565846077 2917061841826930337192279)
              ·
                refine ⟨4375592762740395505788419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917061841826930337192279 4375592762740395505788419)
                ·
                  refine ⟨6563389144110593258682629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375592762740395505788419 6563389144110593258682629)
                  ·
                    refine ⟨1230635464520736236002993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563389144110593258682629 1230635464520736236002993)
                    ·
                      rfl

theorem cell22_3594981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_3594981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594981 prefixEnd_3594981 := by exact prefixLift 3594981
  have htrace : WordTrace (prefixWord ++ tailWord_3594981) baseStart_3594981 baseEnd_3594981 := by
    simpa [prefixWord, tailWord_3594981, baseEnd_3594981] using wordTrace_append hprefix tailTrace_3594981
  have hstable : (prefixWord ++ tailWord_3594981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594981).length < 2 ^ (prefixWord ++ tailWord_3594981).sum := by decide
  have hdescent : baseEnd_3594981 < baseStart_3594981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594992 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_3594992 : Nat := 118140960795 + 3594992 * 2 ^ 59
def prefixEnd_3594992 : Nat := 4983230072969 + 3 ^ 40 * 3594992 * 2
def baseEnd_3594992 : Nat := 1230639230045535873977959

theorem tailTrace_3594992 : CollatzResearch.WordTrace tailWord_3594992 prefixEnd_3594992 1230639230045535873977959 := by
  unfold tailWord_3594992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65560065095982717298801615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87413420127976956398402153 65560065095982717298801615)
  ·
    refine ⟨98340097643974075948202423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65560065095982717298801615 98340097643974075948202423)
    ·
      refine ⟨147510146465961113922303635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98340097643974075948202423 147510146465961113922303635)
      ·
        refine ⟨221265219698941670883455453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147510146465961113922303635 221265219698941670883455453)
        ·
          refine ⟨82974457387103126581295795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221265219698941670883455453 82974457387103126581295795)
          ·
            refine ⟨124461686080654689871943693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82974457387103126581295795 124461686080654689871943693)
            ·
              refine ⟨46673132280245508701978885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124461686080654689871943693 46673132280245508701978885)
              ·
                refine ⟨8751212302546032881621041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46673132280245508701978885 8751212302546032881621041)
                ·
                  refine ⟨6563409226909524661215781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8751212302546032881621041 6563409226909524661215781)
                  ·
                    refine ⟨1230639230045535873977959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563409226909524661215781 1230639230045535873977959)
                    ·
                      rfl

theorem cell22_3594992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_3594992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594992 prefixEnd_3594992 := by exact prefixLift 3594992
  have htrace : WordTrace (prefixWord ++ tailWord_3594992) baseStart_3594992 baseEnd_3594992 := by
    simpa [prefixWord, tailWord_3594992, baseEnd_3594992] using wordTrace_append hprefix tailTrace_3594992
  have hstable : (prefixWord ++ tailWord_3594992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594992).length < 2 ^ (prefixWord ++ tailWord_3594992).sum := by decide
  have hdescent : baseEnd_3594992 < baseStart_3594992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595026 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3595026 : Nat := 118140960795 + 3595026 * 2 ^ 59
def prefixEnd_3595026 : Nat := 4983230072969 + 3 ^ 40 * 3595026 * 2
def baseEnd_3595026 : Nat := 1230650868940371118627855

theorem tailTrace_3595026 : CollatzResearch.WordTrace tailWord_3595026 prefixEnd_3595026 1230650868940371118627855 := by
  unfold tailWord_3595026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780342568460564601085233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87414246849228172269560621 32780342568460564601085233)
  ·
    refine ⟨24585256926345423450813925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32780342568460564601085233 24585256926345423450813925)
    ·
      refine ⟨4609735673689766897027611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24585256926345423450813925 4609735673689766897027611)
      ·
        refine ⟨6914603510534650345541417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609735673689766897027611 6914603510534650345541417)
        ·
          refine ⟨5185952632900987759156063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6914603510534650345541417 5185952632900987759156063)
          ·
            refine ⟨7778928949351481638734095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185952632900987759156063 7778928949351481638734095)
            ·
              refine ⟨11668393424027222458101143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778928949351481638734095 11668393424027222458101143)
              ·
                refine ⟨17502590136040833687151715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11668393424027222458101143 17502590136040833687151715)
                ·
                  refine ⟨26253885204061250530727573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17502590136040833687151715 26253885204061250530727573)
                  ·
                    refine ⟨1230650868940371118627855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26253885204061250530727573 1230650868940371118627855)
                    ·
                      rfl

theorem cell22_3595026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3595026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595026 prefixEnd_3595026 := by exact prefixLift 3595026
  have htrace : WordTrace (prefixWord ++ tailWord_3595026) baseStart_3595026 baseEnd_3595026 := by
    simpa [prefixWord, tailWord_3595026, baseEnd_3595026] using wordTrace_append hprefix tailTrace_3595026
  have hstable : (prefixWord ++ tailWord_3595026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595026).length < 2 ^ (prefixWord ++ tailWord_3595026).sum := by decide
  have hdescent : baseEnd_3595026 < baseStart_3595026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595052 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_3595052 : Nat := 118140960795 + 3595052 * 2 ^ 59
def prefixEnd_3595052 : Nat := 4983230072969 + 3 ^ 40 * 3595052 * 2
def baseEnd_3595052 : Nat := 410219923090571905825925

theorem tailTrace_3595052 : CollatzResearch.WordTrace tailWord_3595052 prefixEnd_3595052 410219923090571905825925 := by
  unfold tailWord_3595052
  simp only [CollatzResearch.WordTrace]
  refine ⟨65561159285874032422393705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87414879047832043229858273 65561159285874032422393705)
  ·
    refine ⟨49170869464405524316795279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65561159285874032422393705 49170869464405524316795279)
    ·
      refine ⟨73756304196608286475192919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49170869464405524316795279 73756304196608286475192919)
      ·
        refine ⟨110634456294912429712789379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73756304196608286475192919 110634456294912429712789379)
        ·
          refine ⟨165951684442368644569184069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110634456294912429712789379 165951684442368644569184069)
          ·
            refine ⟨31115940832944120856722013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165951684442368644569184069 31115940832944120856722013)
            ·
              refine ⟨11668477812354045321270755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31115940832944120856722013 11668477812354045321270755)
              ·
                refine ⟨17502716718531067981906133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11668477812354045321270755 17502716718531067981906133)
                ·
                  refine ⟨410219923090571905825925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17502716718531067981906133 410219923090571905825925)
                  ·
                    rfl

theorem cell22_3595052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_3595052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595052 prefixEnd_3595052 := by exact prefixLift 3595052
  have htrace : WordTrace (prefixWord ++ tailWord_3595052) baseStart_3595052 baseEnd_3595052 := by
    simpa [prefixWord, tailWord_3595052, baseEnd_3595052] using wordTrace_append hprefix tailTrace_3595052
  have hstable : (prefixWord ++ tailWord_3595052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595052).length < 2 ^ (prefixWord ++ tailWord_3595052).sum := by decide
  have hdescent : baseEnd_3595052 < baseStart_3595052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595127 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3595127 : Nat := 118140960795 + 3595127 * 2 ^ 59
def prefixEnd_3595127 : Nat := 4983230072969 + 3 ^ 40 * 3595127 * 2
def baseEnd_3595127 : Nat := 1230685443304440521852545

theorem tailTrace_3595127 : CollatzResearch.WordTrace tailWord_3595127 prefixEnd_3595127 1230685443304440521852545 := by
  unfold tailWord_3595127
  simp only [CollatzResearch.WordTrace]
  refine ⟨131125054046476352653767635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87416702697650901769178423 131125054046476352653767635)
  ·
    refine ⟨196687581069714528980651453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131125054046476352653767635 196687581069714528980651453)
    ·
      refine ⟨73757842901142948367744295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196687581069714528980651453 73757842901142948367744295)
      ·
        refine ⟨110636764351714422551616443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73757842901142948367744295 110636764351714422551616443)
        ·
          refine ⟨165955146527571633827424665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110636764351714422551616443 165955146527571633827424665)
          ·
            refine ⟨124466359895678725370568499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165955146527571633827424665 124466359895678725370568499)
            ·
              refine ⟨186699539843518088055852749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124466359895678725370568499 186699539843518088055852749)
              ·
                refine ⟨70012327441319283020944781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186699539843518088055852749 70012327441319283020944781)
                ·
                  refine ⟨26254622790494731132854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70012327441319283020944781 26254622790494731132854293)
                  ·
                    refine ⟨1230685443304440521852545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26254622790494731132854293 1230685443304440521852545)
                    ·
                      rfl

theorem cell22_3595127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3595127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595127 prefixEnd_3595127 := by exact prefixLift 3595127
  have htrace : WordTrace (prefixWord ++ tailWord_3595127) baseStart_3595127 baseEnd_3595127 := by
    simpa [prefixWord, tailWord_3595127, baseEnd_3595127] using wordTrace_append hprefix tailTrace_3595127
  have hstable : (prefixWord ++ tailWord_3595127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595127).length < 2 ^ (prefixWord ++ tailWord_3595127).sum := by decide
  have hdescent : baseEnd_3595127 < baseStart_3595127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595146 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3595146 : Nat := 118140960795 + 3595146 * 2 ^ 59
def prefixEnd_3595146 : Nat := 4983230072969 + 3 ^ 40 * 3595146 * 2
def baseEnd_3595146 : Nat := 1230691947392730805627487

theorem tailTrace_3595146 : CollatzResearch.WordTrace tailWord_3595146 prefixEnd_3595146 1230691947392730805627487 := by
  unfold tailWord_3595146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32781436758351879724677323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87417164688938345932472861 32781436758351879724677323)
  ·
    refine ⟨49172155137527819587015985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32781436758351879724677323 49172155137527819587015985)
    ·
      refine ⟨36879116353145864690261989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49172155137527819587015985 36879116353145864690261989)
      ·
        refine ⟨6914834316214849629424123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36879116353145864690261989 6914834316214849629424123)
        ·
          refine ⟨10372251474322274444136185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914834316214849629424123 10372251474322274444136185)
          ·
            refine ⟨7779188605741705833102139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372251474322274444136185 7779188605741705833102139)
            ·
              refine ⟨11668782908612558749653209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779188605741705833102139 11668782908612558749653209)
              ·
                refine ⟨8751587181459419062239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11668782908612558749653209 8751587181459419062239907)
                ·
                  refine ⟨13127380772189128593359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751587181459419062239907 13127380772189128593359861)
                  ·
                    refine ⟨1230691947392730805627487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13127380772189128593359861 1230691947392730805627487)
                    ·
                      rfl

theorem cell22_3595146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3595146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595146 prefixEnd_3595146 := by exact prefixLift 3595146
  have htrace : WordTrace (prefixWord ++ tailWord_3595146) baseStart_3595146 baseEnd_3595146 := by
    simpa [prefixWord, tailWord_3595146, baseEnd_3595146] using wordTrace_append hprefix tailTrace_3595146
  have hstable : (prefixWord ++ tailWord_3595146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595146).length < 2 ^ (prefixWord ++ tailWord_3595146).sum := by decide
  have hdescent : baseEnd_3595146 < baseStart_3595146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595189 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3595189 : Nat := 118140960795 + 3595189 * 2 ^ 59
def prefixEnd_3595189 : Nat := 4983230072969 + 3 ^ 40 * 3595189 * 2
def baseEnd_3595189 : Nat := 1230706667171493026802355

theorem tailTrace_3595189 : CollatzResearch.WordTrace tailWord_3595189 prefixEnd_3595189 1230706667171493026802355 := by
  unfold tailWord_3595189
  simp only [CollatzResearch.WordTrace]
  refine ⟨131127315372251737242524621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87418210248167824828349747 131127315372251737242524621)
  ·
    refine ⟨49172743264594401465946733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131127315372251737242524621 49172743264594401465946733)
    ·
      refine ⟨18439778724222900549730025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49172743264594401465946733 18439778724222900549730025)
      ·
        refine ⟨13829834043167175412297519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18439778724222900549730025 13829834043167175412297519)
        ·
          refine ⟨20744751064750763118446279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829834043167175412297519 20744751064750763118446279)
          ·
            refine ⟨31117126597126144677669419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744751064750763118446279 31117126597126144677669419)
            ·
              refine ⟨46675689895689217016504129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31117126597126144677669419 46675689895689217016504129)
              ·
                refine ⟨35006767421766912762378097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46675689895689217016504129 35006767421766912762378097)
                ·
                  refine ⟨26255075566325184571783573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35006767421766912762378097 26255075566325184571783573)
                  ·
                    refine ⟨1230706667171493026802355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26255075566325184571783573 1230706667171493026802355)
                    ·
                      rfl

theorem cell22_3595189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3595189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595189 prefixEnd_3595189 := by exact prefixLift 3595189
  have htrace : WordTrace (prefixWord ++ tailWord_3595189) baseStart_3595189 baseEnd_3595189 := by
    simpa [prefixWord, tailWord_3595189, baseEnd_3595189] using wordTrace_append hprefix tailTrace_3595189
  have hstable : (prefixWord ++ tailWord_3595189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595189).length < 2 ^ (prefixWord ++ tailWord_3595189).sum := by decide
  have hdescent : baseEnd_3595189 < baseStart_3595189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595221 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3595221 : Nat := 118140960795 + 3595221 * 2 ^ 59
def prefixEnd_3595221 : Nat := 4983230072969 + 3 ^ 40 * 3595221 * 2
def baseEnd_3595221 : Nat := 410239207141818536667419

theorem tailTrace_3595221 : CollatzResearch.WordTrace tailWord_3595221 prefixEnd_3595221 410239207141818536667419 := by
  unfold tailWord_3595221
  simp only [CollatzResearch.WordTrace]
  refine ⟨131128482508135806707689517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87418988338757204471793011 131128482508135806707689517)
  ·
    refine ⟨49173180940550927515383569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131128482508135806707689517 49173180940550927515383569)
    ·
      refine ⟨36879885705413195636537677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49173180940550927515383569 36879885705413195636537677)
      ·
        refine ⟨13829957139529948363701629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36879885705413195636537677 13829957139529948363701629)
        ·
          refine ⟨5186233927323730636388111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13829957139529948363701629 5186233927323730636388111)
          ·
            refine ⟨7779350890985595954582167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186233927323730636388111 7779350890985595954582167)
            ·
              refine ⟨11669026336478393931873251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779350890985595954582167 11669026336478393931873251)
              ·
                refine ⟨17503539504717590897809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669026336478393931873251 17503539504717590897809877)
                ·
                  refine ⟨410239207141818536667419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17503539504717590897809877 410239207141818536667419)
                  ·
                    rfl

theorem cell22_3595221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3595221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595221 prefixEnd_3595221 := by exact prefixLift 3595221
  have htrace : WordTrace (prefixWord ++ tailWord_3595221) baseStart_3595221 baseEnd_3595221 := by
    simpa [prefixWord, tailWord_3595221, baseEnd_3595221] using wordTrace_append hprefix tailTrace_3595221
  have hstable : (prefixWord ++ tailWord_3595221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595221).length < 2 ^ (prefixWord ++ tailWord_3595221).sum := by decide
  have hdescent : baseEnd_3595221 < baseStart_3595221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595334 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3595334 : Nat := 118140960795 + 3595334 * 2 ^ 59
def prefixEnd_3595334 : Nat := 4983230072969 + 3 ^ 40 * 3595334 * 2
def baseEnd_3595334 : Nat := 410252101211586993975637

theorem tailTrace_3595334 : CollatzResearch.WordTrace tailWord_3595334 prefixEnd_3595334 410252101211586993975637 := by
  unfold tailWord_3595334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097893873647700843954783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87421735971150951337702037 4097893873647700843954783)
  ·
    refine ⟨6146840810471551265932175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097893873647700843954783 6146840810471551265932175)
    ·
      refine ⟨9220261215707326898898263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146840810471551265932175 9220261215707326898898263)
      ·
        refine ⟨13830391823560990348347395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9220261215707326898898263 13830391823560990348347395)
        ·
          refine ⟨20745587735341485522521093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13830391823560990348347395 20745587735341485522521093)
          ·
            refine ⟨3889797700376528535472705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20745587735341485522521093 3889797700376528535472705)
            ·
              refine ⟨2917348275282396401604529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889797700376528535472705 2917348275282396401604529)
              ·
                refine ⟨2188011206461797301203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917348275282396401604529 2188011206461797301203397)
                ·
                  refine ⟨410252101211586993975637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188011206461797301203397 410252101211586993975637)
                  ·
                    rfl

theorem cell22_3595334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3595334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595334 prefixEnd_3595334 := by exact prefixLift 3595334
  have htrace : WordTrace (prefixWord ++ tailWord_3595334) baseStart_3595334 baseEnd_3595334 := by
    simpa [prefixWord, tailWord_3595334, baseEnd_3595334] using wordTrace_append hprefix tailTrace_3595334
  have hstable : (prefixWord ++ tailWord_3595334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595334).length < 2 ^ (prefixWord ++ tailWord_3595334).sum := by decide
  have hdescent : baseEnd_3595334 < baseStart_3595334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595401 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 6]
def baseStart_3595401 : Nat := 118140960795 + 3595401 * 2 ^ 59
def prefixEnd_3595401 : Nat := 4983230072969 + 3 ^ 40 * 3595401 * 2
def baseEnd_3595401 : Nat := 410259746367998380167235

theorem tailTrace_3595401 : CollatzResearch.WordTrace tailWord_3595401 prefixEnd_3595401 410259746367998380167235 := by
  unfold tailWord_3595401
  simp only [CollatzResearch.WordTrace]
  refine ⟨131135047647483697449242057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87423365098322464966161371 131135047647483697449242057)
  ·
    refine ⟨98351285735612773086931543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131135047647483697449242057 98351285735612773086931543)
    ·
      refine ⟨147526928603419159630397315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98351285735612773086931543 147526928603419159630397315)
      ·
        refine ⟨221290392905128739445595973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147526928603419159630397315 221290392905128739445595973)
        ·
          refine ⟨41491948669711638646049245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221290392905128739445595973 41491948669711638646049245)
          ·
            refine ⟨15559480751141864492268467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41491948669711638646049245 15559480751141864492268467)
            ·
              refine ⟨23339221126712796738402701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15559480751141864492268467 23339221126712796738402701)
              ·
                refine ⟨8752207922517298776901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23339221126712796738402701 8752207922517298776901013)
                ·
                  refine ⟨410259746367998380167235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752207922517298776901013 410259746367998380167235)
                  ·
                    rfl

theorem cell22_3595401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_3595401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595401 prefixEnd_3595401 := by exact prefixLift 3595401
  have htrace : WordTrace (prefixWord ++ tailWord_3595401) baseStart_3595401 baseEnd_3595401 := by
    simpa [prefixWord, tailWord_3595401, baseEnd_3595401] using wordTrace_append hprefix tailTrace_3595401
  have hstable : (prefixWord ++ tailWord_3595401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595401).length < 2 ^ (prefixWord ++ tailWord_3595401).sum := by decide
  have hdescent : baseEnd_3595401 < baseStart_3595401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595418 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_3595418 : Nat := 118140960795 + 3595418 * 2 ^ 59
def prefixEnd_3595418 : Nat := 4983230072969 + 3 ^ 40 * 3595418 * 2
def baseEnd_3595418 : Nat := 410261686183804254275551

theorem tailTrace_3595418 : CollatzResearch.WordTrace tailWord_3595418 prefixEnd_3595418 410261686183804254275551 := by
  unfold tailWord_3595418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32783916922105527338152727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87423778458948072901740605 32783916922105527338152727)
  ·
    refine ⟨49175875383158291007229091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32783916922105527338152727 49175875383158291007229091)
    ·
      refine ⟨73763813074737436510843637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49175875383158291007229091 73763813074737436510843637)
      ·
        refine ⟨6915357475756634672891591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73763813074737436510843637 6915357475756634672891591)
        ·
          refine ⟨10373036213634952009337387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915357475756634672891591 10373036213634952009337387)
          ·
            refine ⟨15559554320452428014006081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373036213634952009337387 15559554320452428014006081)
            ·
              refine ⟨11669665740339321010504561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15559554320452428014006081 11669665740339321010504561)
              ·
                refine ⟨8752249305254490757878421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669665740339321010504561 8752249305254490757878421)
                ·
                  refine ⟨410261686183804254275551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752249305254490757878421 410261686183804254275551)
                  ·
                    rfl

theorem cell22_3595418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_3595418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595418 prefixEnd_3595418 := by exact prefixLift 3595418
  have htrace : WordTrace (prefixWord ++ tailWord_3595418) baseStart_3595418 baseEnd_3595418 := by
    simpa [prefixWord, tailWord_3595418, baseEnd_3595418] using wordTrace_append hprefix tailTrace_3595418
  have hstable : (prefixWord ++ tailWord_3595418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595418).length < 2 ^ (prefixWord ++ tailWord_3595418).sum := by decide
  have hdescent : baseEnd_3595418 < baseStart_3595418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595420 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3595420 : Nat := 118140960795 + 3595420 * 2 ^ 59
def prefixEnd_3595420 : Nat := 4983230072969 + 3 ^ 40 * 3595420 * 2
def baseEnd_3595420 : Nat := 1230785743192285424276647

theorem tailTrace_3595420 : CollatzResearch.WordTrace tailWord_3595420 prefixEnd_3595420 1230785743192285424276647 := by
  unfold tailWord_3595420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65567870317207431847091857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87423827089609909129455809 65567870317207431847091857)
  ·
    refine ⟨49175902737905573885318893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65567870317207431847091857 49175902737905573885318893)
    ·
      refine ⟨18440963526714590206994585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49175902737905573885318893 18440963526714590206994585)
      ·
        refine ⟨13830722645035942655245939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18440963526714590206994585 13830722645035942655245939)
        ·
          refine ⟨20746083967553913982868909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13830722645035942655245939 20746083967553913982868909)
          ·
            refine ⟨7779781487832717743575841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20746083967553913982868909 7779781487832717743575841)
            ·
              refine ⟨5834836115874538307681881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779781487832717743575841 5834836115874538307681881)
              ·
                refine ⟨4376127086905903730761411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834836115874538307681881 4376127086905903730761411)
                ·
                  refine ⟨6564190630358855596142117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376127086905903730761411 6564190630358855596142117)
                  ·
                    refine ⟨1230785743192285424276647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564190630358855596142117 1230785743192285424276647)
                    ·
                      rfl

theorem cell22_3595420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3595420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595420 prefixEnd_3595420 := by exact prefixLift 3595420
  have htrace : WordTrace (prefixWord ++ tailWord_3595420) baseStart_3595420 baseEnd_3595420 := by
    simpa [prefixWord, tailWord_3595420, baseEnd_3595420] using wordTrace_append hprefix tailTrace_3595420
  have hstable : (prefixWord ++ tailWord_3595420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595420).length < 2 ^ (prefixWord ++ tailWord_3595420).sum := by decide
  have hdescent : baseEnd_3595420 < baseStart_3595420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595452 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_3595452 : Nat := 118140960795 + 3595452 * 2 ^ 59
def prefixEnd_3595452 : Nat := 4983230072969 + 3 ^ 40 * 3595452 * 2
def baseEnd_3595452 : Nat := 410265565815416002492183

theorem tailTrace_3595452 : CollatzResearch.WordTrace tailWord_3595452 prefixEnd_3595452 410265565815416002492183 := by
  unfold tailWord_3595452
  simp only [CollatzResearch.WordTrace]
  refine ⟨65568453885149466579674305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87424605180199288772899073 65568453885149466579674305)
  ·
    refine ⟨49176340413862099934755729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65568453885149466579674305 49176340413862099934755729)
    ·
      refine ⟨36882255310396574951066797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49176340413862099934755729 36882255310396574951066797)
      ·
        refine ⟨13830845741398715606650049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36882255310396574951066797 13830845741398715606650049)
        ·
          refine ⟨10373134306049036704987537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13830845741398715606650049 10373134306049036704987537)
          ·
            refine ⟨7779850729536777528740653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10373134306049036704987537 7779850729536777528740653)
            ·
              refine ⟨2917444023576291573277745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7779850729536777528740653 2917444023576291573277745)
              ·
                refine ⟨2188083017682218679958309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917444023576291573277745 2188083017682218679958309)
                ·
                  refine ⟨410265565815416002492183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188083017682218679958309 410265565815416002492183)
                  ·
                    rfl

theorem cell22_3595452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_3595452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595452 prefixEnd_3595452 := by exact prefixLift 3595452
  have htrace : WordTrace (prefixWord ++ tailWord_3595452) baseStart_3595452 baseEnd_3595452 := by
    simpa [prefixWord, tailWord_3595452, baseEnd_3595452] using wordTrace_append hprefix tailTrace_3595452
  have hstable : (prefixWord ++ tailWord_3595452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595452).length < 2 ^ (prefixWord ++ tailWord_3595452).sum := by decide
  have hdescent : baseEnd_3595452 < baseStart_3595452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595523 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_3595523 : Nat := 118140960795 + 3595523 * 2 ^ 59
def prefixEnd_3595523 : Nat := 4983230072969 + 3 ^ 40 * 3595523 * 2
def baseEnd_3595523 : Nat := 1230821002197227488951331

theorem tailTrace_3595523 : CollatzResearch.WordTrace tailWord_3595523 prefixEnd_3595523 1230821002197227488951331 := by
  unfold tailWord_3595523
  simp only [CollatzResearch.WordTrace]
  refine ⟨131139497353041712285183223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87426331568694474856788815 131139497353041712285183223)
  ·
    refine ⟨196709246029562568427774835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131139497353041712285183223 196709246029562568427774835)
    ·
      refine ⟨295063869044343852641662253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196709246029562568427774835 295063869044343852641662253)
      ·
        refine ⟨110648950891628944740623345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295063869044343852641662253 110648950891628944740623345)
        ·
          refine ⟨82986713168721708555467509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110648950891628944740623345 82986713168721708555467509)
          ·
            refine ⟨7780004359567660177075079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82986713168721708555467509 7780004359567660177075079)
            ·
              refine ⟨11670006539351490265612619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780004359567660177075079 11670006539351490265612619)
              ·
                refine ⟨17505009809027235398418929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11670006539351490265612619 17505009809027235398418929)
                ·
                  refine ⟨13128757356770426548814197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17505009809027235398418929 13128757356770426548814197)
                  ·
                    refine ⟨1230821002197227488951331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13128757356770426548814197 1230821002197227488951331)
                    ·
                      rfl

theorem cell22_3595523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_3595523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595523 prefixEnd_3595523 := by exact prefixLift 3595523
  have htrace : WordTrace (prefixWord ++ tailWord_3595523) baseStart_3595523 baseEnd_3595523 := by
    simpa [prefixWord, tailWord_3595523, baseEnd_3595523] using wordTrace_append hprefix tailTrace_3595523
  have hstable : (prefixWord ++ tailWord_3595523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595523).length < 2 ^ (prefixWord ++ tailWord_3595523).sum := by decide
  have hdescent : baseEnd_3595523 < baseStart_3595523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595555 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 1, 4]
def baseStart_3595555 : Nat := 118140960795 + 3595555 * 2 ^ 59
def prefixEnd_3595555 : Nat := 4983230072969 + 3 ^ 40 * 3595555 * 2
def baseEnd_3595555 : Nat := 1230831956451190072151233

theorem tailTrace_3595555 : CollatzResearch.WordTrace tailWord_3595555 prefixEnd_3595555 1230831956451190072151233 := by
  unfold tailWord_3595555
  simp only [CollatzResearch.WordTrace]
  refine ⟨131140664488925781750348119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87427109659283854500232079 131140664488925781750348119)
  ·
    refine ⟨196710996733388672625522179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131140664488925781750348119 196710996733388672625522179)
    ·
      refine ⟨295066495100083008938283269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196710996733388672625522179 295066495100083008938283269)
      ·
        refine ⟨55324967831265564175928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295066495100083008938283269 55324967831265564175928113)
        ·
          refine ⟨41493725873449173131946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55324967831265564175928113 41493725873449173131946085)
          ·
            refine ⟨7780073601271719962239891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41493725873449173131946085 7780073601271719962239891)
            ·
              refine ⟨11670110401907579943359837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780073601271719962239891 11670110401907579943359837)
              ·
                refine ⟨4376291400715342478759939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670110401907579943359837 4376291400715342478759939)
                ·
                  refine ⟨6564437101073013718139909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376291400715342478759939 6564437101073013718139909)
                  ·
                    refine ⟨1230831956451190072151233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564437101073013718139909 1230831956451190072151233)
                    ·
                      rfl

theorem cell22_3595555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_3595555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595555 prefixEnd_3595555 := by exact prefixLift 3595555
  have htrace : WordTrace (prefixWord ++ tailWord_3595555) baseStart_3595555 baseEnd_3595555 := by
    simpa [prefixWord, tailWord_3595555, baseEnd_3595555] using wordTrace_append hprefix tailTrace_3595555
  have hstable : (prefixWord ++ tailWord_3595555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595555).length < 2 ^ (prefixWord ++ tailWord_3595555).sum := by decide
  have hdescent : baseEnd_3595555 < baseStart_3595555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595570 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3595570 : Nat := 118140960795 + 3595570 * 2 ^ 59
def prefixEnd_3595570 : Nat := 4983230072969 + 3 ^ 40 * 3595570 * 2
def baseEnd_3595570 : Nat := 410279030419245011008729

theorem tailTrace_3595570 : CollatzResearch.WordTrace tailWord_3595570 prefixEnd_3595570 410279030419245011008729 := by
  unfold tailWord_3595570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785302895967859828036041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87427474389247626208096109 32785302895967859828036041)
  ·
    refine ⟨24588977171975894871027031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32785302895967859828036041 24588977171975894871027031)
    ·
      refine ⟨36883465757963842306540547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588977171975894871027031 36883465757963842306540547)
      ·
        refine ⟨55325198636945763459810821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36883465757963842306540547 55325198636945763459810821)
        ·
          refine ⟨10373474744427330648714529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55325198636945763459810821 10373474744427330648714529)
          ·
            refine ⟨7780106058320497986535897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10373474744427330648714529 7780106058320497986535897)
            ·
              refine ⟨5835079543740373489901923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780106058320497986535897 5835079543740373489901923)
              ·
                refine ⟨8752619315610560234852885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835079543740373489901923 8752619315610560234852885)
                ·
                  refine ⟨410279030419245011008729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752619315610560234852885 410279030419245011008729)
                  ·
                    rfl

theorem cell22_3595570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3595570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595570 prefixEnd_3595570 := by exact prefixLift 3595570
  have htrace : WordTrace (prefixWord ++ tailWord_3595570) baseStart_3595570 baseEnd_3595570 := by
    simpa [prefixWord, tailWord_3595570, baseEnd_3595570] using wordTrace_append hprefix tailTrace_3595570
  have hstable : (prefixWord ++ tailWord_3595570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595570).length < 2 ^ (prefixWord ++ tailWord_3595570).sum := by decide
  have hdescent : baseEnd_3595570 < baseStart_3595570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595583 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3595583 : Nat := 118140960795 + 3595583 * 2 ^ 59
def prefixEnd_3595583 : Nat := 4983230072969 + 3 ^ 40 * 3595583 * 2
def baseEnd_3595583 : Nat := 1230841541423407332451147

theorem tailTrace_3595583 : CollatzResearch.WordTrace tailWord_3595583 prefixEnd_3595583 1230841541423407332451147 := by
  unfold tailWord_3595583
  simp only [CollatzResearch.WordTrace]
  refine ⟨131141685732824342532367403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87427790488549561688244935 131141685732824342532367403)
  ·
    refine ⟨196712528599236513798551105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131141685732824342532367403 196712528599236513798551105)
    ·
      refine ⟨147534396449427385348913329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196712528599236513798551105 147534396449427385348913329)
      ·
        refine ⟨110650797337070539011684997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147534396449427385348913329 110650797337070539011684997)
        ·
          refine ⟨20747024500700726064690937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110650797337070539011684997 20747024500700726064690937)
          ·
            refine ⟨15560268375525544548518203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20747024500700726064690937 15560268375525544548518203)
            ·
              refine ⟨23340402563288316822777305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15560268375525544548518203 23340402563288316822777305)
              ·
                refine ⟨17505301922466237617082979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23340402563288316822777305 17505301922466237617082979)
                ·
                  refine ⟨26257952883699356425624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17505301922466237617082979 26257952883699356425624469)
                  ·
                    refine ⟨1230841541423407332451147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26257952883699356425624469 1230841541423407332451147)
                    ·
                      rfl

theorem cell22_3595583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3595583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595583 prefixEnd_3595583 := by exact prefixLift 3595583
  have htrace : WordTrace (prefixWord ++ tailWord_3595583) baseStart_3595583 baseEnd_3595583 := by
    simpa [prefixWord, tailWord_3595583, baseEnd_3595583] using wordTrace_append hprefix tailTrace_3595583
  have hstable : (prefixWord ++ tailWord_3595583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595583).length < 2 ^ (prefixWord ++ tailWord_3595583).sum := by decide
  have hdescent : baseEnd_3595583 < baseStart_3595583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595598 : List Nat := [4, 1, 1, 1, 1, 1, 5, 8]
def baseStart_3595598 : Nat := 118140960795 + 3595598 * 2 ^ 59
def prefixEnd_3595598 : Nat := 4983230072969 + 3 ^ 40 * 3595598 * 2
def baseEnd_3595598 : Nat := 136760741803328032591789

theorem tailTrace_3595598 : CollatzResearch.WordTrace tailWord_3595598 prefixEnd_3595598 136760741803328032591789 := by
  unfold tailWord_3595598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392779103471250011770431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87428155218513333396108965 16392779103471250011770431)
  ·
    refine ⟨24589168655206875017655647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16392779103471250011770431 24589168655206875017655647)
    ·
      refine ⟨36883752982810312526483471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24589168655206875017655647 36883752982810312526483471)
      ·
        refine ⟨55325629474215468789725207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36883752982810312526483471 55325629474215468789725207)
        ·
          refine ⟨82988444211323203184587811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55325629474215468789725207 82988444211323203184587811)
          ·
            refine ⟨124482666316984804776881717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82988444211323203184587811 124482666316984804776881717)
            ·
              refine ⟨11670249967217325447832661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124482666316984804776881717 11670249967217325447832661)
              ·
                refine ⟨136760741803328032591789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11670249967217325447832661 136760741803328032591789)
                ·
                  rfl

theorem cell22_3595598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_3595598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595598 prefixEnd_3595598 := by exact prefixLift 3595598
  have htrace : WordTrace (prefixWord ++ tailWord_3595598) baseStart_3595598 baseEnd_3595598 := by
    simpa [prefixWord, tailWord_3595598, baseEnd_3595598] using wordTrace_append hprefix tailTrace_3595598
  have hstable : (prefixWord ++ tailWord_3595598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595598).length < 2 ^ (prefixWord ++ tailWord_3595598).sum := by decide
  have hdescent : baseEnd_3595598 < baseStart_3595598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595677 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3595677 : Nat := 118140960795 + 3595677 * 2 ^ 59
def prefixEnd_3595677 : Nat := 4983230072969 + 3 ^ 40 * 3595677 * 2
def baseEnd_3595677 : Nat := 410291239848140806866953

theorem tailTrace_3595677 : CollatzResearch.WordTrace tailWord_3595677 prefixEnd_3595677 410291239848140806866953 := by
  unfold tailWord_3595677
  simp only [CollatzResearch.WordTrace]
  refine ⟨131145114194483796586289285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87430076129655864390859523 131145114194483796586289285)
  ·
    refine ⟨24589708911465711859929241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131145114194483796586289285 24589708911465711859929241)
    ·
      refine ⟨18442281683599283894946931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24589708911465711859929241 18442281683599283894946931)
      ·
        refine ⟨27663422525398925842420397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18442281683599283894946931 27663422525398925842420397)
        ·
          refine ⟨10373783447024597190907649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27663422525398925842420397 10373783447024597190907649)
          ·
            refine ⟨7780337585268447893180737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10373783447024597190907649 7780337585268447893180737)
            ·
              refine ⟨5835253188951335919885553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780337585268447893180737 5835253188951335919885553)
              ·
                refine ⟨4376439891713501939914165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835253188951335919885553 4376439891713501939914165)
                ·
                  refine ⟨410291239848140806866953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4376439891713501939914165 410291239848140806866953)
                  ·
                    rfl

theorem cell22_3595677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3595677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595677 prefixEnd_3595677 := by exact prefixLift 3595677
  have htrace : WordTrace (prefixWord ++ tailWord_3595677) baseStart_3595677 baseEnd_3595677 := by
    simpa [prefixWord, tailWord_3595677, baseEnd_3595677] using wordTrace_append hprefix tailTrace_3595677
  have hstable : (prefixWord ++ tailWord_3595677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595677).length < 2 ^ (prefixWord ++ tailWord_3595677).sum := by decide
  have hdescent : baseEnd_3595677 < baseStart_3595677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595720 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_3595720 : Nat := 118140960795 + 3595720 * 2 ^ 59
def prefixEnd_3595720 : Nat := 4983230072969 + 3 ^ 40 * 3595720 * 2
def baseEnd_3595720 : Nat := 1230888439323184641775727

theorem tailTrace_3595720 : CollatzResearch.WordTrace tailWord_3595720 prefixEnd_3595720 1230888439323184641775727 := by
  unfold tailWord_3595720
  simp only [CollatzResearch.WordTrace]
  refine ⟨65573341266664007465052307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87431121688885343286736409 65573341266664007465052307)
  ·
    refine ⟨98360011899996011197578461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65573341266664007465052307 98360011899996011197578461)
    ·
      refine ⟨36885004462498504199091923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98360011899996011197578461 36885004462498504199091923)
      ·
        refine ⟨55327506693747756298637885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36885004462498504199091923 55327506693747756298637885)
        ·
          refine ⟨20747815010155408611989207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55327506693747756298637885 20747815010155408611989207)
          ·
            refine ⟨31121722515233112917983811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20747815010155408611989207 31121722515233112917983811)
            ·
              refine ⟨46682583772849669376975717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31121722515233112917983811 46682583772849669376975717)
              ·
                refine ⟨8752984457409313008182947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46682583772849669376975717 8752984457409313008182947)
                ·
                  refine ⟨13129476686113969512274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752984457409313008182947 13129476686113969512274421)
                  ·
                    refine ⟨1230888439323184641775727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13129476686113969512274421 1230888439323184641775727)
                    ·
                      rfl

theorem cell22_3595720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_3595720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595720 prefixEnd_3595720 := by exact prefixLift 3595720
  have htrace : WordTrace (prefixWord ++ tailWord_3595720) baseStart_3595720 baseEnd_3595720 := by
    simpa [prefixWord, tailWord_3595720, baseEnd_3595720] using wordTrace_append hprefix tailTrace_3595720
  have hstable : (prefixWord ++ tailWord_3595720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595720).length < 2 ^ (prefixWord ++ tailWord_3595720).sum := by decide
  have hdescent : baseEnd_3595720 < baseStart_3595720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595722 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_3595722 : Nat := 118140960795 + 3595722 * 2 ^ 59
def prefixEnd_3595722 : Nat := 4983230072969 + 3 ^ 40 * 3595722 * 2
def baseEnd_3595722 : Nat := 410296374654685767741907

theorem tailTrace_3595722 : CollatzResearch.WordTrace tailWord_3595722 prefixEnd_3595722 410296374654685767741907 := by
  unfold tailWord_3595722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786688869830192317919355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87431170319547179514451613 32786688869830192317919355)
  ·
    refine ⟨49180033304745288476879033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32786688869830192317919355 49180033304745288476879033)
    ·
      refine ⟨36885024978558966357659275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49180033304745288476879033 36885024978558966357659275)
      ·
        refine ⟨55327537467838449536488913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36885024978558966357659275 55327537467838449536488913)
        ·
          refine ⟨41495653100878837152366685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55327537467838449536488913 41495653100878837152366685)
          ·
            refine ⟨15560869912829563932137507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41495653100878837152366685 15560869912829563932137507)
            ·
              refine ⟨23341304869244345898206261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15560869912829563932137507 23341304869244345898206261)
              ·
                refine ⟨2188247331491657427956837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23341304869244345898206261 2188247331491657427956837)
                ·
                  refine ⟨410296374654685767741907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188247331491657427956837 410296374654685767741907)
                  ·
                    rfl

theorem cell22_3595722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_3595722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595722 prefixEnd_3595722 := by exact prefixLift 3595722
  have htrace : WordTrace (prefixWord ++ tailWord_3595722) baseStart_3595722 baseEnd_3595722 := by
    simpa [prefixWord, tailWord_3595722, baseEnd_3595722] using wordTrace_append hprefix tailTrace_3595722
  have hstable : (prefixWord ++ tailWord_3595722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595722).length < 2 ^ (prefixWord ++ tailWord_3595722).sum := by decide
  have hdescent : baseEnd_3595722 < baseStart_3595722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595724 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_3595724 : Nat := 118140960795 + 3595724 * 2 ^ 59
def prefixEnd_3595724 : Nat := 4983230072969 + 3 ^ 40 * 3595724 * 2
def baseEnd_3595724 : Nat := 1230889808604929964675715

theorem tailTrace_3595724 : CollatzResearch.WordTrace tailWord_3595724 prefixEnd_3595724 1230889808604929964675715 := by
  unfold tailWord_3595724
  simp only [CollatzResearch.WordTrace]
  refine ⟨65573414212656761806625113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87431218950209015742166817 65573414212656761806625113)
  ·
    refine ⟨49180060659492571354968835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65573414212656761806625113 49180060659492571354968835)
    ·
      refine ⟨73770090989238857032453253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49180060659492571354968835 73770090989238857032453253)
      ·
        refine ⟨13831892060482285693584985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73770090989238857032453253 13831892060482285693584985)
        ·
          refine ⟨10373919045361714270188739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13831892060482285693584985 10373919045361714270188739)
          ·
            refine ⟨15560878568042571405283109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373919045361714270188739 15560878568042571405283109)
            ·
              refine ⟨2917664731507982138490583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15560878568042571405283109 2917664731507982138490583)
              ·
                refine ⟨4376497097261973207735875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917664731507982138490583 4376497097261973207735875)
                ·
                  refine ⟨6564745645892959811603813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376497097261973207735875 6564745645892959811603813)
                  ·
                    refine ⟨1230889808604929964675715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564745645892959811603813 1230889808604929964675715)
                    ·
                      rfl

theorem cell22_3595724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_3595724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595724 prefixEnd_3595724 := by exact prefixLift 3595724
  have htrace : WordTrace (prefixWord ++ tailWord_3595724) baseStart_3595724 baseEnd_3595724 := by
    simpa [prefixWord, tailWord_3595724, baseEnd_3595724] using wordTrace_append hprefix tailTrace_3595724
  have hstable : (prefixWord ++ tailWord_3595724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595724).length < 2 ^ (prefixWord ++ tailWord_3595724).sum := by decide
  have hdescent : baseEnd_3595724 < baseStart_3595724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595735 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3595735 : Nat := 118140960795 + 3595735 * 2 ^ 59
def prefixEnd_3595735 : Nat := 4983230072969 + 3 ^ 40 * 3595735 * 2
def baseEnd_3595735 : Nat := 1230893574129729602650681

theorem tailTrace_3595735 : CollatzResearch.WordTrace tailWord_3595735 prefixEnd_3595735 1230893574129729602650681 := by
  unfold tailWord_3595735
  simp only [CollatzResearch.WordTrace]
  refine ⟨131147229628273672491900659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87431486418849114994600439 131147229628273672491900659)
  ·
    refine ⟨196720844442410508737850989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131147229628273672491900659 196720844442410508737850989)
    ·
      refine ⟨73770316665903940776694121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196720844442410508737850989 73770316665903940776694121)
      ·
        refine ⟨55327737499427955582520591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73770316665903940776694121 55327737499427955582520591)
        ·
          refine ⟨82991606249141933373780887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55327737499427955582520591 82991606249141933373780887)
          ·
            refine ⟨124487409373712900060671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82991606249141933373780887 124487409373712900060671331)
            ·
              refine ⟨186731114060569350091006997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124487409373712900060671331 186731114060569350091006997)
              ·
                refine ⟨8753020971589188285515953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186731114060569350091006997 8753020971589188285515953)
                ·
                  refine ⟨6564765728691891214136965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8753020971589188285515953 6564765728691891214136965)
                  ·
                    refine ⟨1230893574129729602650681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564765728691891214136965 1230893574129729602650681)
                    ·
                      rfl

theorem cell22_3595735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3595735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595735 prefixEnd_3595735 := by exact prefixLift 3595735
  have htrace : WordTrace (prefixWord ++ tailWord_3595735) baseStart_3595735 baseEnd_3595735 := by
    simpa [prefixWord, tailWord_3595735, baseEnd_3595735] using wordTrace_append hprefix tailTrace_3595735
  have hstable : (prefixWord ++ tailWord_3595735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595735).length < 2 ^ (prefixWord ++ tailWord_3595735).sum := by decide
  have hdescent : baseEnd_3595735 < baseStart_3595735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595737 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_3595737 : Nat := 118140960795 + 3595737 * 2 ^ 59
def prefixEnd_3595737 : Nat := 4983230072969 + 3 ^ 40 * 3595737 * 2
def baseEnd_3595737 : Nat := 1230894258770602264100675

theorem tailTrace_3595737 : CollatzResearch.WordTrace tailWord_3595737 prefixEnd_3595737 1230894258770602264100675 := by
  unfold tailWord_3595737
  simp only [CollatzResearch.WordTrace]
  refine ⟨131147302574266426833473465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87431535049510951222315643 131147302574266426833473465)
  ·
    refine ⟨98360476930699820125105099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131147302574266426833473465 98360476930699820125105099)
    ·
      refine ⟨147540715396049730187657649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98360476930699820125105099 147540715396049730187657649)
      ·
        refine ⟨110655536547037297640743237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147540715396049730187657649 110655536547037297640743237)
        ·
          refine ⟨20747913102569493307639357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110655536547037297640743237 20747913102569493307639357)
          ·
            refine ⟨7780467413463559990364759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20747913102569493307639357 7780467413463559990364759)
            ·
              refine ⟨11670701120195339985547139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780467413463559990364759 11670701120195339985547139)
              ·
                refine ⟨17506051680293009978320709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11670701120195339985547139 17506051680293009978320709)
                ·
                  refine ⟨3282384690054939370935133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17506051680293009978320709 3282384690054939370935133)
                  ·
                    refine ⟨1230894258770602264100675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282384690054939370935133 1230894258770602264100675)
                    ·
                      rfl

theorem cell22_3595737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_3595737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595737 prefixEnd_3595737 := by exact prefixLift 3595737
  have htrace : WordTrace (prefixWord ++ tailWord_3595737) baseStart_3595737 baseEnd_3595737 := by
    simpa [prefixWord, tailWord_3595737, baseEnd_3595737] using wordTrace_append hprefix tailTrace_3595737
  have hstable : (prefixWord ++ tailWord_3595737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595737).length < 2 ^ (prefixWord ++ tailWord_3595737).sum := by decide
  have hdescent : baseEnd_3595737 < baseStart_3595737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595754 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3595754 : Nat := 118140960795 + 3595754 * 2 ^ 59
def prefixEnd_3595754 : Nat := 4983230072969 + 3 ^ 40 * 3595754 * 2
def baseEnd_3595754 : Nat := 1230900078218019886425623

theorem tailTrace_3595754 : CollatzResearch.WordTrace tailWord_3595754 prefixEnd_3595754 1230900078218019886425623 := by
  unfold tailWord_3595754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786980653801209684210579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87431948410136559157894877 32786980653801209684210579)
  ·
    refine ⟨49180470980701814526315869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32786980653801209684210579 49180470980701814526315869)
    ·
      refine ⟨18442676617763180447368451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49180470980701814526315869 18442676617763180447368451)
      ·
        refine ⟨27664014926644770671052677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18442676617763180447368451 27664014926644770671052677)
        ·
          refine ⟨5187002798745894500822377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27664014926644770671052677 5187002798745894500822377)
          ·
            refine ⟨3890252099059420875616783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5187002798745894500822377 3890252099059420875616783)
            ·
              refine ⟨5835378148589131313425175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890252099059420875616783 5835378148589131313425175)
              ·
                refine ⟨8753067222883696970137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835378148589131313425175 8753067222883696970137763)
                ·
                  refine ⟨13129600834325545455206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753067222883696970137763 13129600834325545455206645)
                  ·
                    refine ⟨1230900078218019886425623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13129600834325545455206645 1230900078218019886425623)
                    ·
                      rfl

theorem cell22_3595754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3595754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595754 prefixEnd_3595754 := by exact prefixLift 3595754
  have htrace : WordTrace (prefixWord ++ tailWord_3595754) baseStart_3595754 baseEnd_3595754 := by
    simpa [prefixWord, tailWord_3595754, baseEnd_3595754] using wordTrace_append hprefix tailTrace_3595754
  have hstable : (prefixWord ++ tailWord_3595754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595754).length < 2 ^ (prefixWord ++ tailWord_3595754).sum := by decide
  have hdescent : baseEnd_3595754 < baseStart_3595754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595795 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 7]
def baseStart_3595795 : Nat := 118140960795 + 3595795 * 2 ^ 59
def prefixEnd_3595795 : Nat := 4983230072969 + 3 ^ 40 * 3595795 * 2
def baseEnd_3595795 : Nat := 410304704451969815383499

theorem tailTrace_3595795 : CollatzResearch.WordTrace tailWord_3595795 prefixEnd_3595795 410304704451969815383499 := by
  unfold tailWord_3595795
  simp only [CollatzResearch.WordTrace]
  refine ⟨131149418008056302739084839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87432945338704201826056559 131149418008056302739084839)
  ·
    refine ⟨196724127012084454108627259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131149418008056302739084839 196724127012084454108627259)
    ·
      refine ⟨295086190518126681162940889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196724127012084454108627259 295086190518126681162940889)
      ·
        refine ⟨221314642888595010872205667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295086190518126681162940889 221314642888595010872205667)
        ·
          refine ⟨331971964332892516308308501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221314642888595010872205667 331971964332892516308308501)
          ·
            refine ⟨15561185828104336701951961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 331971964332892516308308501 15561185828104336701951961)
            ·
              refine ⟨11670889371078252526463971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15561185828104336701951961 11670889371078252526463971)
              ·
                refine ⟨17506334056617378789695957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11670889371078252526463971 17506334056617378789695957)
                ·
                  refine ⟨410304704451969815383499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17506334056617378789695957 410304704451969815383499)
                  ·
                    rfl

theorem cell22_3595795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_3595795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595795 prefixEnd_3595795 := by exact prefixLift 3595795
  have htrace : WordTrace (prefixWord ++ tailWord_3595795) baseStart_3595795 baseEnd_3595795 := by
    simpa [prefixWord, tailWord_3595795, baseEnd_3595795] using wordTrace_append hprefix tailTrace_3595795
  have hstable : (prefixWord ++ tailWord_3595795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595795).length < 2 ^ (prefixWord ++ tailWord_3595795).sum := by decide
  have hdescent : baseEnd_3595795 < baseStart_3595795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595855 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3595855 : Nat := 118140960795 + 3595855 * 2 ^ 59
def prefixEnd_3595855 : Nat := 4983230072969 + 3 ^ 40 * 3595855 * 2
def baseEnd_3595855 : Nat := 1230934652582089289650313

theorem tailTrace_3595855 : CollatzResearch.WordTrace tailWord_3595855 prefixEnd_3595855 1230934652582089289650313 := by
  unfold tailWord_3595855
  simp only [CollatzResearch.WordTrace]
  refine ⟨131151606387838932986269019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87434404258559288657512679 131151606387838932986269019)
  ·
    refine ⟨196727409581758399479403529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131151606387838932986269019 196727409581758399479403529)
    ·
      refine ⟨147545557186318799609552647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196727409581758399479403529 147545557186318799609552647)
      ·
        refine ⟨221318335779478199414328971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147545557186318799609552647 221318335779478199414328971)
        ·
          refine ⟨331977503669217299121493457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221318335779478199414328971 331977503669217299121493457)
          ·
            refine ⟨248983127751912974341120093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331977503669217299121493457 248983127751912974341120093)
            ·
              refine ⟨93368672906967365377920035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248983127751912974341120093 93368672906967365377920035)
              ·
                refine ⟨140053009360451048066880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93368672906967365377920035 140053009360451048066880053)
                ·
                  refine ⟨13129969627542285756270005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140053009360451048066880053 13129969627542285756270005)
                  ·
                    refine ⟨1230934652582089289650313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13129969627542285756270005 1230934652582089289650313)
                    ·
                      rfl

theorem cell22_3595855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3595855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595855 prefixEnd_3595855 := by exact prefixLift 3595855
  have htrace : WordTrace (prefixWord ++ tailWord_3595855) baseStart_3595855 baseEnd_3595855 := by
    simpa [prefixWord, tailWord_3595855, baseEnd_3595855] using wordTrace_append hprefix tailTrace_3595855
  have hstable : (prefixWord ++ tailWord_3595855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595855).length < 2 ^ (prefixWord ++ tailWord_3595855).sum := by decide
  have hdescent : baseEnd_3595855 < baseStart_3595855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595872 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_3595872 : Nat := 118140960795 + 3595872 * 2 ^ 59
def prefixEnd_3595872 : Nat := 4983230072969 + 3 ^ 40 * 3595872 * 2
def baseEnd_3595872 : Nat := 1230940472029506911975261

theorem tailTrace_3595872 : CollatzResearch.WordTrace tailWord_3595872 prefixEnd_3595872 1230940472029506911975261 := by
  unfold tailWord_3595872
  simp only [CollatzResearch.WordTrace]
  refine ⟨65576113214388672444818935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87434817619184896593091913 65576113214388672444818935)
  ·
    refine ⟨98364169821583008667228403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65576113214388672444818935 98364169821583008667228403)
    ·
      refine ⟨147546254732374513000842605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98364169821583008667228403 147546254732374513000842605)
      ·
        refine ⟨55329845524640442375315977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147546254732374513000842605 55329845524640442375315977)
        ·
          refine ⟨41497384143480331781486983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55329845524640442375315977 41497384143480331781486983)
          ·
            refine ⟨62246076215220497672230475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41497384143480331781486983 62246076215220497672230475)
            ·
              refine ⟨93369114322830746508345713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62246076215220497672230475 93369114322830746508345713)
              ·
                refine ⟨70026835742123059881259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93369114322830746508345713 70026835742123059881259285)
                ·
                  refine ⟨3282507925412018431934029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70026835742123059881259285 3282507925412018431934029)
                  ·
                    refine ⟨1230940472029506911975261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282507925412018431934029 1230940472029506911975261)
                    ·
                      rfl

theorem cell22_3595872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_3595872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595872 prefixEnd_3595872 := by exact prefixLift 3595872
  have htrace : WordTrace (prefixWord ++ tailWord_3595872) baseStart_3595872 baseEnd_3595872 := by
    simpa [prefixWord, tailWord_3595872, baseEnd_3595872] using wordTrace_append hprefix tailTrace_3595872
  have hstable : (prefixWord ++ tailWord_3595872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595872).length < 2 ^ (prefixWord ++ tailWord_3595872).sum := by decide
  have hdescent : baseEnd_3595872 < baseStart_3595872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595893 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3595893 : Nat := 118140960795 + 3595893 * 2 ^ 59
def prefixEnd_3595893 : Nat := 4983230072969 + 3 ^ 40 * 3595893 * 2
def baseEnd_3595893 : Nat := 1230947660758669857200197

theorem tailTrace_3595893 : CollatzResearch.WordTrace tailWord_3595893 prefixEnd_3595893 1230947660758669857200197 := by
  unfold tailWord_3595893
  simp only [CollatzResearch.WordTrace]
  refine ⟨131152992361701265476152333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87435328241134176984101555 131152992361701265476152333)
  ·
    refine ⟨49182372135637974553557125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131152992361701265476152333 49182372135637974553557125)
    ·
      refine ⟨9221694775432120228791961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49182372135637974553557125 9221694775432120228791961)
      ·
        refine ⟨6916271081574090171593971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9221694775432120228791961 6916271081574090171593971)
        ·
          refine ⟨10374406622361135257390957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6916271081574090171593971 10374406622361135257390957)
          ·
            refine ⟨3890402483385425721521609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10374406622361135257390957 3890402483385425721521609)
            ·
              refine ⟨2917801862539069291141207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3890402483385425721521609 2917801862539069291141207)
              ·
                refine ⟨4376702793808603936711811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917801862539069291141207 4376702793808603936711811)
                ·
                  refine ⟨6565054190712905905067717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376702793808603936711811 6565054190712905905067717)
                  ·
                    refine ⟨1230947660758669857200197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565054190712905905067717 1230947660758669857200197)
                    ·
                      rfl

theorem cell22_3595893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3595893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595893 prefixEnd_3595893 := by exact prefixLift 3595893
  have htrace : WordTrace (prefixWord ++ tailWord_3595893) baseStart_3595893 baseEnd_3595893 := by
    simpa [prefixWord, tailWord_3595893, baseEnd_3595893] using wordTrace_append hprefix tailTrace_3595893
  have hstable : (prefixWord ++ tailWord_3595893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595893).length < 2 ^ (prefixWord ++ tailWord_3595893).sum := by decide
  have hdescent : baseEnd_3595893 < baseStart_3595893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595968 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_3595968 : Nat := 118140960795 + 3595968 * 2 ^ 59
def prefixEnd_3595968 : Nat := 4983230072969 + 3 ^ 40 * 3595968 * 2
def baseEnd_3595968 : Nat := 1230973334791394661574967

theorem tailTrace_3595968 : CollatzResearch.WordTrace tailWord_3595968 prefixEnd_3595968 1230973334791394661574967 := by
  unfold tailWord_3595968
  simp only [CollatzResearch.WordTrace]
  refine ⟨65577863918214776642566279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87437151890953035523421705 65577863918214776642566279)
  ·
    refine ⟨98366795877322164963849419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65577863918214776642566279 98366795877322164963849419)
    ·
      refine ⟨147550193815983247445774129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98366795877322164963849419 147550193815983247445774129)
      ·
        refine ⟨110662645361987435584330597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147550193815983247445774129 110662645361987435584330597)
        ·
          refine ⟨20749246005372644172061987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110662645361987435584330597 20749246005372644172061987)
          ·
            refine ⟨31123869008058966258092981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20749246005372644172061987 31123869008058966258092981)
            ·
              refine ⟨2917862719505528086696217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31123869008058966258092981 2917862719505528086696217)
              ·
                refine ⟨2188397039629146065022163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917862719505528086696217 2188397039629146065022163)
                ·
                  refine ⟨3282595559443719097533245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188397039629146065022163 3282595559443719097533245)
                  ·
                    refine ⟨1230973334791394661574967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282595559443719097533245 1230973334791394661574967)
                    ·
                      rfl

theorem cell22_3595968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_3595968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595968 prefixEnd_3595968 := by exact prefixLift 3595968
  have htrace : WordTrace (prefixWord ++ tailWord_3595968) baseStart_3595968 baseEnd_3595968 := by
    simpa [prefixWord, tailWord_3595968, baseEnd_3595968] using wordTrace_append hprefix tailTrace_3595968
  have hstable : (prefixWord ++ tailWord_3595968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595968).length < 2 ^ (prefixWord ++ tailWord_3595968).sum := by decide
  have hdescent : baseEnd_3595968 < baseStart_3595968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595992 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_3595992 : Nat := 118140960795 + 3595992 * 2 ^ 59
def prefixEnd_3595992 : Nat := 4983230072969 + 3 ^ 40 * 3595992 * 2
def baseEnd_3595992 : Nat := 410327183493955532991631

theorem tailTrace_3595992 : CollatzResearch.WordTrace tailWord_3595992 prefixEnd_3595992 410327183493955532991631 := by
  unfold tailWord_3595992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65578301594171302692003115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87437735458895070256004153 65578301594171302692003115)
  ·
    refine ⟨98367452391256954038004673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65578301594171302692003115 98367452391256954038004673)
    ·
      refine ⟨73775589293442715528503505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98367452391256954038004673 73775589293442715528503505)
      ·
        refine ⟨55331691970082036646377629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73775589293442715528503505 55331691970082036646377629)
        ·
          refine ⟨20749384488780763742391611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55331691970082036646377629 20749384488780763742391611)
          ·
            refine ⟨31124076733171145613587417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20749384488780763742391611 31124076733171145613587417)
            ·
              refine ⟨23343057549878359210190563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31124076733171145613587417 23343057549878359210190563)
              ·
                refine ⟨35014586324817538815285845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23343057549878359210190563 35014586324817538815285845)
                ·
                  refine ⟨410327183493955532991631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35014586324817538815285845 410327183493955532991631)
                  ·
                    rfl

theorem cell22_3595992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_3595992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595992 prefixEnd_3595992 := by exact prefixLift 3595992
  have htrace : WordTrace (prefixWord ++ tailWord_3595992) baseStart_3595992 baseEnd_3595992 := by
    simpa [prefixWord, tailWord_3595992, baseEnd_3595992] using wordTrace_append hprefix tailTrace_3595992
  have hstable : (prefixWord ++ tailWord_3595992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595992).length < 2 ^ (prefixWord ++ tailWord_3595992).sum := by decide
  have hdescent : baseEnd_3595992 < baseStart_3595992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3595994 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_3595994 : Nat := 118140960795 + 3595994 * 2 ^ 59
def prefixEnd_3595994 : Nat := 4983230072969 + 3 ^ 40 * 3595994 * 2
def baseEnd_3595994 : Nat := 1230982235122739260424887

theorem tailTrace_3595994 : CollatzResearch.WordTrace tailWord_3595994 prefixEnd_3595994 1230982235122739260424887 := by
  unfold tailWord_3595994
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789169033583839931394759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87437784089556906483719357 32789169033583839931394759)
  ·
    refine ⟨49183753550375759897092139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789169033583839931394759 49183753550375759897092139)
    ·
      refine ⟨73775630325563639845638209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49183753550375759897092139 73775630325563639845638209)
      ·
        refine ⟨55331722744172729884228657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73775630325563639845638209 55331722744172729884228657)
        ·
          refine ⟨41498792058129547413171493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55331722744172729884228657 41498792058129547413171493)
          ·
            refine ⟨7781023510899290139969655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41498792058129547413171493 7781023510899290139969655)
            ·
              refine ⟨11671535266348935209954483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7781023510899290139969655 11671535266348935209954483)
              ·
                refine ⟨17507302899523402814931725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11671535266348935209954483 17507302899523402814931725)
                ·
                  refine ⟨6565238587321276055599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17507302899523402814931725 6565238587321276055599397)
                  ·
                    refine ⟨1230982235122739260424887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565238587321276055599397 1230982235122739260424887)
                    ·
                      rfl

theorem cell22_3595994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_3595994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3595994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3595994 prefixEnd_3595994 := by exact prefixLift 3595994
  have htrace : WordTrace (prefixWord ++ tailWord_3595994) baseStart_3595994 baseEnd_3595994 := by
    simpa [prefixWord, tailWord_3595994, baseEnd_3595994] using wordTrace_append hprefix tailTrace_3595994
  have hstable : (prefixWord ++ tailWord_3595994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3595994).length < 2 ^ (prefixWord ++ tailWord_3595994).sum := by decide
  have hdescent : baseEnd_3595994 < baseStart_3595994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3595994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596009 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 4]
def baseStart_3596009 : Nat := 118140960795 + 3596009 * 2 ^ 59
def prefixEnd_3596009 : Nat := 4983230072969 + 3 ^ 40 * 3596009 * 2
def baseEnd_3596009 : Nat := 410329123309761407099947

theorem tailTrace_3596009 : CollatzResearch.WordTrace tailWord_3596009 prefixEnd_3596009 410329123309761407099947 := by
  unfold tailWord_3596009
  simp only [CollatzResearch.WordTrace]
  refine ⟨131157223229281017287375081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87438148819520678191583387 131157223229281017287375081)
  ·
    refine ⟨98367917421960762965531311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131157223229281017287375081 98367917421960762965531311)
    ·
      refine ⟨147551876132941144448296967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98367917421960762965531311 147551876132941144448296967)
      ·
        refine ⟨221327814199411716672445451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147551876132941144448296967 221327814199411716672445451)
        ·
          refine ⟨331991721299117575008668177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221327814199411716672445451 331991721299117575008668177)
          ·
            refine ⟨248993790974338181256501133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331991721299117575008668177 248993790974338181256501133)
            ·
              refine ⟨93372671615376817971187925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248993790974338181256501133 93372671615376817971187925)
              ·
                refine ⟨2188421990985394171199717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93372671615376817971187925 2188421990985394171199717)
                ·
                  refine ⟨410329123309761407099947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188421990985394171199717 410329123309761407099947)
                  ·
                    rfl

theorem cell22_3596009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_3596009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596009 prefixEnd_3596009 := by exact prefixLift 3596009
  have htrace : WordTrace (prefixWord ++ tailWord_3596009) baseStart_3596009 baseEnd_3596009 := by
    simpa [prefixWord, tailWord_3596009, baseEnd_3596009] using wordTrace_append hprefix tailTrace_3596009
  have hstable : (prefixWord ++ tailWord_3596009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596009).length < 2 ^ (prefixWord ++ tailWord_3596009).sum := by decide
  have hdescent : baseEnd_3596009 < baseStart_3596009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596159 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3596159 : Nat := 118140960795 + 3596159 * 2 ^ 59
def prefixEnd_3596159 : Nat := 4983230072969 + 3 ^ 40 * 3596159 * 2
def baseEnd_3596159 : Nat := 1231038717994733830049381

theorem tailTrace_3596159 : CollatzResearch.WordTrace tailWord_3596159 prefixEnd_3596159 1231038717994733830049381 := by
  unfold tailWord_3596159
  simp only [CollatzResearch.WordTrace]
  refine ⟨131162694178737592905335531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87441796119158395270223687 131162694178737592905335531)
  ·
    refine ⟨196744041268106389358003297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131162694178737592905335531 196744041268106389358003297)
    ·
      refine ⟨147558030951079792018502473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196744041268106389358003297 147558030951079792018502473)
      ·
        refine ⟨110668523213309844013876855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147558030951079792018502473 110668523213309844013876855)
        ·
          refine ⟨166002784819964766020815283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110668523213309844013876855 166002784819964766020815283)
          ·
            refine ⟨249004177229947149031222925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166002784819964766020815283 249004177229947149031222925)
            ·
              refine ⟨93376566461230180886708597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249004177229947149031222925 93376566461230180886708597)
              ·
                refine ⟨8754053105740329458128931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93376566461230180886708597 8754053105740329458128931)
                ·
                  refine ⟨13131079658610494187193397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754053105740329458128931 13131079658610494187193397)
                  ·
                    refine ⟨1231038717994733830049381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13131079658610494187193397 1231038717994733830049381)
                    ·
                      rfl

theorem cell22_3596159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3596159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596159 prefixEnd_3596159 := by exact prefixLift 3596159
  have htrace : WordTrace (prefixWord ++ tailWord_3596159) baseStart_3596159 baseEnd_3596159 := by
    simpa [prefixWord, tailWord_3596159, baseEnd_3596159] using wordTrace_append hprefix tailTrace_3596159
  have hstable : (prefixWord ++ tailWord_3596159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596159).length < 2 ^ (prefixWord ++ tailWord_3596159).sum := by decide
  have hdescent : baseEnd_3596159 < baseStart_3596159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596163 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 1, 4]
def baseStart_3596163 : Nat := 118140960795 + 3596163 * 2 ^ 59
def prefixEnd_3596163 : Nat := 4983230072969 + 3 ^ 40 * 3596163 * 2
def baseEnd_3596163 : Nat := 1231040087276479152949369

theorem tailTrace_3596163 : CollatzResearch.WordTrace tailWord_3596163 prefixEnd_3596163 1231040087276479152949369 := by
  unfold tailWord_3596163
  simp only [CollatzResearch.WordTrace]
  refine ⟨131162840070723101588481143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87441893380482067725654095 131162840070723101588481143)
  ·
    refine ⟨196744260106084652382721715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131162840070723101588481143 196744260106084652382721715)
    ·
      refine ⟨295116390159126978574082573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196744260106084652382721715 295116390159126978574082573)
      ·
        refine ⟨110668646309672616965280965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295116390159126978574082573 110668646309672616965280965)
        ·
          refine ⟨20750371183063615680990181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110668646309672616965280965 20750371183063615680990181)
          ·
            refine ⟨3890694596824427940185659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20750371183063615680990181 3890694596824427940185659)
            ·
              refine ⟨5836041895236641910278489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890694596824427940185659 5836041895236641910278489)
              ·
                refine ⟨4377031421427481432708867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836041895236641910278489 4377031421427481432708867)
                ·
                  refine ⟨6565547132141222149063301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377031421427481432708867 6565547132141222149063301)
                  ·
                    refine ⟨1231040087276479152949369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565547132141222149063301 1231040087276479152949369)
                    ·
                      rfl

theorem cell22_3596163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].length) (baseStart_3596163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596163 prefixEnd_3596163 := by exact prefixLift 3596163
  have htrace : WordTrace (prefixWord ++ tailWord_3596163) baseStart_3596163 baseEnd_3596163 := by
    simpa [prefixWord, tailWord_3596163, baseEnd_3596163] using wordTrace_append hprefix tailTrace_3596163
  have hstable : (prefixWord ++ tailWord_3596163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596163).length < 2 ^ (prefixWord ++ tailWord_3596163).sum := by decide
  have hdescent : baseEnd_3596163 < baseStart_3596163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596180 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3596180 : Nat := 118140960795 + 3596180 * 2 ^ 59
def prefixEnd_3596180 : Nat := 4983230072969 + 3 ^ 40 * 3596180 * 2
def baseEnd_3596180 : Nat := 1231045906723896775274317

theorem tailTrace_3596180 : CollatzResearch.WordTrace tailWord_3596180 prefixEnd_3596180 1231045906723896775274317 := by
  unfold tailWord_3596180
  simp only [CollatzResearch.WordTrace]
  refine ⟨65581730055830756745924997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87442306741107675661233329 65581730055830756745924997)
  ·
    refine ⟨12296574385468266889860937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65581730055830756745924997 12296574385468266889860937)
    ·
      refine ⟨9222430789101200167395703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12296574385468266889860937 9222430789101200167395703)
      ·
        refine ⟨13833646183651800251093555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222430789101200167395703 13833646183651800251093555)
        ·
          refine ⟨20750469275477700376640333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13833646183651800251093555 20750469275477700376640333)
          ·
            refine ⟨7781425978304137641240125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20750469275477700376640333 7781425978304137641240125)
            ·
              refine ⟨2918034741864051615465047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7781425978304137641240125 2918034741864051615465047)
              ·
                refine ⟨4377052112796077423197571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918034741864051615465047 4377052112796077423197571)
                ·
                  refine ⟨6565578169194116134796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377052112796077423197571 6565578169194116134796357)
                  ·
                    refine ⟨1231045906723896775274317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565578169194116134796357 1231045906723896775274317)
                    ·
                      rfl

theorem cell22_3596180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3596180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596180 prefixEnd_3596180 := by exact prefixLift 3596180
  have htrace : WordTrace (prefixWord ++ tailWord_3596180) baseStart_3596180 baseEnd_3596180 := by
    simpa [prefixWord, tailWord_3596180, baseEnd_3596180] using wordTrace_append hprefix tailTrace_3596180
  have hstable : (prefixWord ++ tailWord_3596180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596180).length < 2 ^ (prefixWord ++ tailWord_3596180).sum := by decide
  have hdescent : baseEnd_3596180 < baseStart_3596180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596189 : List Nat := [1, 4, 2, 1, 2, 12]
def baseStart_3596189 : Nat := 118140960795 + 3596189 * 2 ^ 59
def prefixEnd_3596189 : Nat := 4983230072969 + 3 ^ 40 * 3596189 * 2
def baseEnd_3596189 : Nat := 15198135649479305577769

theorem tailTrace_3596189 : CollatzResearch.WordTrace tailWord_3596189 prefixEnd_3596189 15198135649479305577769 := by
  unfold tailWord_3596189
  simp only [CollatzResearch.WordTrace]
  refine ⟨131163788368628908028927621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87442525579085938685951747 131163788368628908028927621)
  ·
    refine ⟨24593210319117920255423929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131163788368628908028927621 24593210319117920255423929)
    ·
      refine ⟨18444907739338440191567947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24593210319117920255423929 18444907739338440191567947)
      ·
        refine ⟨27667361609007660287351921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444907739338440191567947 27667361609007660287351921)
        ·
          refine ⟨20750521206755745215513941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667361609007660287351921 20750521206755745215513941)
          ·
            refine ⟨15198135649479305577769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20750521206755745215513941 15198135649479305577769)
            ·
              rfl

theorem cell22_3596189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 12].length) (baseStart_3596189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596189 prefixEnd_3596189 := by exact prefixLift 3596189
  have htrace : WordTrace (prefixWord ++ tailWord_3596189) baseStart_3596189 baseEnd_3596189 := by
    simpa [prefixWord, tailWord_3596189, baseEnd_3596189] using wordTrace_append hprefix tailTrace_3596189
  have hstable : (prefixWord ++ tailWord_3596189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596189).length < 2 ^ (prefixWord ++ tailWord_3596189).sum := by decide
  have hdescent : baseEnd_3596189 < baseStart_3596189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596255 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 1, 3]
def baseStart_3596255 : Nat := 118140960795 + 3596255 * 2 ^ 59
def prefixEnd_3596255 : Nat := 4983230072969 + 3 ^ 40 * 3596255 * 2
def baseEnd_3596255 : Nat := 1231071580756621579649087

theorem tailTrace_3596255 : CollatzResearch.WordTrace tailWord_3596255 prefixEnd_3596255 1231071580756621579649087 := by
  unfold tailWord_3596255
  simp only [CollatzResearch.WordTrace]
  refine ⟨131166195586389801300830219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87444130390926534200553479 131166195586389801300830219)
  ·
    refine ⟨196749293379584701951245329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131166195586389801300830219 196749293379584701951245329)
    ·
      refine ⟨147561970034688526463433997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196749293379584701951245329 147561970034688526463433997)
      ·
        refine ⟨55335738763008197423787749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147561970034688526463433997 55335738763008197423787749)
        ·
          refine ⟨10375451018064037016960203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55335738763008197423787749 10375451018064037016960203)
          ·
            refine ⟨15563176527096055525440305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375451018064037016960203 15563176527096055525440305)
            ·
              refine ⟨11672382395322041644080229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15563176527096055525440305 11672382395322041644080229)
              ·
                refine ⟨2188571699122882808265043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11672382395322041644080229 2188571699122882808265043)
                ·
                  refine ⟨3282857548684324212397565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188571699122882808265043 3282857548684324212397565)
                  ·
                    refine ⟨1231071580756621579649087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282857548684324212397565 1231071580756621579649087)
                    ·
                      rfl

theorem cell22_3596255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_3596255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596255 prefixEnd_3596255 := by exact prefixLift 3596255
  have htrace : WordTrace (prefixWord ++ tailWord_3596255) baseStart_3596255 baseEnd_3596255 := by
    simpa [prefixWord, tailWord_3596255, baseEnd_3596255] using wordTrace_append hprefix tailTrace_3596255
  have hstable : (prefixWord ++ tailWord_3596255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596255).length < 2 ^ (prefixWord ++ tailWord_3596255).sum := by decide
  have hdescent : baseEnd_3596255 < baseStart_3596255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596266 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3596266 : Nat := 118140960795 + 3596266 * 2 ^ 59
def prefixEnd_3596266 : Nat := 4983230072969 + 3 ^ 40 * 3596266 * 2
def baseEnd_3596266 : Nat := 1231075346281421217624053

theorem tailTrace_3596266 : CollatzResearch.WordTrace tailWord_3596266 prefixEnd_3596266 1231075346281421217624053 := by
  unfold tailWord_3596266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32791649197337487544870163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87444397859566633452987101 32791649197337487544870163)
  ·
    refine ⟨49187473796006231317305245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32791649197337487544870163 49187473796006231317305245)
    ·
      refine ⟨18445302673502336743989467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49187473796006231317305245 18445302673502336743989467)
      ·
        refine ⟨27667954010253505115984201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18445302673502336743989467 27667954010253505115984201)
        ·
          refine ⟨20750965507690128836988151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667954010253505115984201 20750965507690128836988151)
          ·
            refine ⟨31126448261535193255482227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20750965507690128836988151 31126448261535193255482227)
            ·
              refine ⟨46689672392302789883223341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31126448261535193255482227 46689672392302789883223341)
              ·
                refine ⟨17508627147113546206208753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46689672392302789883223341 17508627147113546206208753)
                ·
                  refine ⟨13131470360335159654656565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17508627147113546206208753 13131470360335159654656565)
                  ·
                    refine ⟨1231075346281421217624053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13131470360335159654656565 1231075346281421217624053)
                    ·
                      rfl

theorem cell22_3596266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3596266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596266 prefixEnd_3596266 := by exact prefixLift 3596266
  have htrace : WordTrace (prefixWord ++ tailWord_3596266) baseStart_3596266 baseEnd_3596266 := by
    simpa [prefixWord, tailWord_3596266, baseEnd_3596266] using wordTrace_append hprefix tailTrace_3596266
  have hstable : (prefixWord ++ tailWord_3596266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596266).length < 2 ^ (prefixWord ++ tailWord_3596266).sum := by decide
  have hdescent : baseEnd_3596266 < baseStart_3596266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596341 : List Nat := [1, 3, 3, 1, 1, 1, 4, 8]
def baseStart_3596341 : Nat := 118140960795 + 3596341 * 2 ^ 59
def prefixEnd_3596341 : Nat := 4983230072969 + 3 ^ 40 * 3596341 * 2
def baseEnd_3596341 : Nat := 136789002257127335777647

theorem tailTrace_3596341 : CollatzResearch.WordTrace tailWord_3596341 prefixEnd_3596341 136789002257127335777647 := by
  unfold tailWord_3596341
  simp only [CollatzResearch.WordTrace]
  refine ⟨131169332264078237988460877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87446221509385491992307251 131169332264078237988460877)
  ·
    refine ⟨49188499599029339245672829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131169332264078237988460877 49188499599029339245672829)
    ·
      refine ⟨18445687349636002217127311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49188499599029339245672829 18445687349636002217127311)
      ·
        refine ⟨27668531024454003325690967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18445687349636002217127311 27668531024454003325690967)
        ·
          refine ⟨41502796536681004988536451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27668531024454003325690967 41502796536681004988536451)
          ·
            refine ⟨62254194805021507482804677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41502796536681004988536451 62254194805021507482804677)
            ·
              refine ⟨11672661525941532653025877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62254194805021507482804677 11672661525941532653025877)
              ·
                refine ⟨136789002257127335777647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11672661525941532653025877 136789002257127335777647)
                ·
                  rfl

theorem cell22_3596341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 8].length) (baseStart_3596341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596341 prefixEnd_3596341 := by exact prefixLift 3596341
  have htrace : WordTrace (prefixWord ++ tailWord_3596341) baseStart_3596341 baseEnd_3596341 := by
    simpa [prefixWord, tailWord_3596341, baseEnd_3596341] using wordTrace_append hprefix tailTrace_3596341
  have hstable : (prefixWord ++ tailWord_3596341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596341).length < 2 ^ (prefixWord ++ tailWord_3596341).sum := by decide
  have hdescent : baseEnd_3596341 < baseStart_3596341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596401 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3596401 : Nat := 118140960795 + 3596401 * 2 ^ 59
def prefixEnd_3596401 : Nat := 4983230072969 + 3 ^ 40 * 3596401 * 2
def baseEnd_3596401 : Nat := 1231121559540325865498639

theorem tailTrace_3596401 : CollatzResearch.WordTrace tailWord_3596401 prefixEnd_3596401 1231121559540325865498639 := by
  unfold tailWord_3596401
  simp only [CollatzResearch.WordTrace]
  refine ⟨131171520643860868235645057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87447680429240578823763371 131171520643860868235645057)
  ·
    refine ⟨98378640482895651176733793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131171520643860868235645057 98378640482895651176733793)
    ·
      refine ⟨73783980362171738382550345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98378640482895651176733793 73783980362171738382550345)
      ·
        refine ⟨55337985271628803786912759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73783980362171738382550345 55337985271628803786912759)
        ·
          refine ⟨83006977907443205680369139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55337985271628803786912759 83006977907443205680369139)
          ·
            refine ⟨124510466861164808520553709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83006977907443205680369139 124510466861164808520553709)
            ·
              refine ⟨46691425072936803195207641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124510466861164808520553709 46691425072936803195207641)
              ·
                refine ⟨35018568804702602396405731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46691425072936803195207641 35018568804702602396405731)
                ·
                  refine ⟨52527853207053903594608597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35018568804702602396405731 52527853207053903594608597)
                  ·
                    refine ⟨1231121559540325865498639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52527853207053903594608597 1231121559540325865498639)
                    ·
                      rfl

theorem cell22_3596401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3596401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596401 prefixEnd_3596401 := by exact prefixLift 3596401
  have htrace : WordTrace (prefixWord ++ tailWord_3596401) baseStart_3596401 baseEnd_3596401 := by
    simpa [prefixWord, tailWord_3596401, baseEnd_3596401] using wordTrace_append hprefix tailTrace_3596401
  have hstable : (prefixWord ++ tailWord_3596401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596401).length < 2 ^ (prefixWord ++ tailWord_3596401).sum := by decide
  have hdescent : baseEnd_3596401 < baseStart_3596401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596407 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3596407 : Nat := 118140960795 + 3596407 * 2 ^ 59
def prefixEnd_3596407 : Nat := 4983230072969 + 3 ^ 40 * 3596407 * 2
def baseEnd_3596407 : Nat := 1231123613462943849848621

theorem tailTrace_3596407 : CollatzResearch.WordTrace tailWord_3596407 prefixEnd_3596407 1231123613462943849848621 := by
  unfold tailWord_3596407
  simp only [CollatzResearch.WordTrace]
  refine ⟨131171739481839131260363475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87447826321226087506908983 131171739481839131260363475)
  ·
    refine ⟨196757609222758696890545213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131171739481839131260363475 196757609222758696890545213)
    ·
      refine ⟨73784103458534511333954455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196757609222758696890545213 73784103458534511333954455)
      ·
        refine ⟨110676155187801767000931683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73784103458534511333954455 110676155187801767000931683)
        ·
          refine ⟨166014232781702650501397525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110676155187801767000931683 166014232781702650501397525)
          ·
            refine ⟨7781917161642311742253009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166014232781702650501397525 7781917161642311742253009)
            ·
              refine ⟨5836437871231733806689757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7781917161642311742253009 5836437871231733806689757)
              ·
                refine ⟨2188664201711900177508659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5836437871231733806689757 2188664201711900177508659)
                ·
                  refine ⟨3282996302567850266262989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188664201711900177508659 3282996302567850266262989)
                  ·
                    refine ⟨1231123613462943849848621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282996302567850266262989 1231123613462943849848621)
                    ·
                      rfl

theorem cell22_3596407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3596407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596407 prefixEnd_3596407 := by exact prefixLift 3596407
  have htrace : WordTrace (prefixWord ++ tailWord_3596407) baseStart_3596407 baseEnd_3596407 := by
    simpa [prefixWord, tailWord_3596407, baseEnd_3596407] using wordTrace_append hprefix tailTrace_3596407
  have hstable : (prefixWord ++ tailWord_3596407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596407).length < 2 ^ (prefixWord ++ tailWord_3596407).sum := by decide
  have hdescent : baseEnd_3596407 < baseStart_3596407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596448 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_3596448 : Nat := 118140960795 + 3596448 * 2 ^ 59
def prefixEnd_3596448 : Nat := 4983230072969 + 3 ^ 40 * 3596448 * 2
def baseEnd_3596448 : Nat := 410379216200277803191165

theorem tailTrace_3596448 : CollatzResearch.WordTrace tailWord_3596448 prefixEnd_3596448 410379216200277803191165 := by
  unfold tailWord_3596448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65586617437345297631302999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87448823249793730175070665 65586617437345297631302999)
  ·
    refine ⟨98379926156017946446954499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65586617437345297631302999 98379926156017946446954499)
    ·
      refine ⟨147569889234026919670431749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98379926156017946446954499 147569889234026919670431749)
      ·
        refine ⟨27669354231380047438205953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147569889234026919670431749 27669354231380047438205953)
        ·
          refine ⟨20752015673535035578654465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27669354231380047438205953 20752015673535035578654465)
          ·
            refine ⟨15564011755151276683990849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20752015673535035578654465 15564011755151276683990849)
            ·
              refine ⟨11673008816363457512993137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15564011755151276683990849 11673008816363457512993137)
              ·
                refine ⟨8754756612272593134744853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11673008816363457512993137 8754756612272593134744853)
                ·
                  refine ⟨410379216200277803191165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8754756612272593134744853 410379216200277803191165)
                  ·
                    rfl

theorem cell22_3596448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_3596448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596448 prefixEnd_3596448 := by exact prefixLift 3596448
  have htrace : WordTrace (prefixWord ++ tailWord_3596448) baseStart_3596448 baseEnd_3596448 := by
    simpa [prefixWord, tailWord_3596448, baseEnd_3596448] using wordTrace_append hprefix tailTrace_3596448
  have hstable : (prefixWord ++ tailWord_3596448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596448).length < 2 ^ (prefixWord ++ tailWord_3596448).sum := by decide
  have hdescent : baseEnd_3596448 < baseStart_3596448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596458 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3596458 : Nat := 118140960795 + 3596458 * 2 ^ 59
def prefixEnd_3596458 : Nat := 4983230072969 + 3 ^ 40 * 3596458 * 2
def baseEnd_3596458 : Nat := 1231141071805196716823465

theorem tailTrace_3596458 : CollatzResearch.WordTrace tailWord_3596458 prefixEnd_3596458 1231141071805196716823465 := by
  unfold tailWord_3596458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32793399901163591742617507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87449066403102911313646685 32793399901163591742617507)
  ·
    refine ⟨49190099851745387613926261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32793399901163591742617507 49190099851745387613926261)
    ·
      refine ⟨4611571861101130088805587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49190099851745387613926261 4611571861101130088805587)
      ·
        refine ⟨6917357791651695133208381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611571861101130088805587 6917357791651695133208381)
        ·
          refine ⟨2594009171869385674953143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6917357791651695133208381 2594009171869385674953143)
          ·
            refine ⟨3891013757804078512429715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594009171869385674953143 3891013757804078512429715)
            ·
              refine ⟨5836520636706117768644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891013757804078512429715 5836520636706117768644573)
              ·
                refine ⟨2188695238764794163241715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5836520636706117768644573 2188695238764794163241715)
                ·
                  refine ⟨3283042858147191244862573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188695238764794163241715 3283042858147191244862573)
                  ·
                    refine ⟨1231141071805196716823465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283042858147191244862573 1231141071805196716823465)
                    ·
                      rfl

theorem cell22_3596458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3596458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596458 prefixEnd_3596458 := by exact prefixLift 3596458
  have htrace : WordTrace (prefixWord ++ tailWord_3596458) baseStart_3596458 baseEnd_3596458 := by
    simpa [prefixWord, tailWord_3596458, baseEnd_3596458] using wordTrace_append hprefix tailTrace_3596458
  have hstable : (prefixWord ++ tailWord_3596458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596458).length < 2 ^ (prefixWord ++ tailWord_3596458).sum := by decide
  have hdescent : baseEnd_3596458 < baseStart_3596458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596480 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_3596480 : Nat := 118140960795 + 3596480 * 2 ^ 59
def prefixEnd_3596480 : Nat := 4983230072969 + 3 ^ 40 * 3596480 * 2
def baseEnd_3596480 : Nat := 1231148602854795992773397

theorem tailTrace_3596480 : CollatzResearch.WordTrace tailWord_3596480 prefixEnd_3596480 1231148602854795992773397 := by
  unfold tailWord_3596480
  simp only [CollatzResearch.WordTrace]
  refine ⟨65587201005287332363885447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87449601340383109818513929 65587201005287332363885447)
  ·
    refine ⟨98380801507930998545828171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65587201005287332363885447 98380801507930998545828171)
    ·
      refine ⟨147571202261896497818742257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98380801507930998545828171 147571202261896497818742257)
      ·
        refine ⟨110678401696422373364056693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147571202261896497818742257 110678401696422373364056693)
        ·
          refine ⟨10376100159039597502880315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110678401696422373364056693 10376100159039597502880315)
          ·
            refine ⟨15564150238559396254320473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376100159039597502880315 15564150238559396254320473)
            ·
              refine ⟨11673112678919547190740355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15564150238559396254320473 11673112678919547190740355)
              ·
                refine ⟨17509669018379320786110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673112678919547190740355 17509669018379320786110533)
                ·
                  refine ⟨3283062940946122647395725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17509669018379320786110533 3283062940946122647395725)
                  ·
                    refine ⟨1231148602854795992773397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283062940946122647395725 1231148602854795992773397)
                    ·
                      rfl

theorem cell22_3596480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_3596480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596480 prefixEnd_3596480 := by exact prefixLift 3596480
  have htrace : WordTrace (prefixWord ++ tailWord_3596480) baseStart_3596480 baseEnd_3596480 := by
    simpa [prefixWord, tailWord_3596480, baseEnd_3596480] using wordTrace_append hprefix tailTrace_3596480
  have hstable : (prefixWord ++ tailWord_3596480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596480).length < 2 ^ (prefixWord ++ tailWord_3596480).sum := by decide
  have hdescent : baseEnd_3596480 < baseStart_3596480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596497 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_3596497 : Nat := 118140960795 + 3596497 * 2 ^ 59
def prefixEnd_3596497 : Nat := 4983230072969 + 3 ^ 40 * 3596497 * 2
def baseEnd_3596497 : Nat := 1231154422302213615098345

theorem tailTrace_3596497 : CollatzResearch.WordTrace tailWord_3596497 prefixEnd_3596497 1231154422302213615098345 := by
  unfold tailWord_3596497
  simp only [CollatzResearch.WordTrace]
  refine ⟨131175022051513076631139745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87450014701008717754093163 131175022051513076631139745)
  ·
    refine ⟨98381266538634807473354809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131175022051513076631139745 98381266538634807473354809)
    ·
      refine ⟨73785949903976105605016107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98381266538634807473354809 73785949903976105605016107)
      ·
        refine ⟨110678924855964158407524161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73785949903976105605016107 110678924855964158407524161)
        ·
          refine ⟨83009193641973118805643121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110678924855964158407524161 83009193641973118805643121)
          ·
            refine ⟨62256895231479839104232341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83009193641973118805643121 62256895231479839104232341)
            ·
              refine ⟨2918291963975617458010891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62256895231479839104232341 2918291963975617458010891)
              ·
                refine ⟨4377437945963426187016337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918291963975617458010891 4377437945963426187016337)
                ·
                  refine ⟨3283078459472569640262253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377437945963426187016337 3283078459472569640262253)
                  ·
                    refine ⟨1231154422302213615098345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283078459472569640262253 1231154422302213615098345)
                    ·
                      rfl

theorem cell22_3596497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_3596497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596497 prefixEnd_3596497 := by exact prefixLift 3596497
  have htrace : WordTrace (prefixWord ++ tailWord_3596497) baseStart_3596497 baseEnd_3596497 := by
    simpa [prefixWord, tailWord_3596497, baseEnd_3596497] using wordTrace_append hprefix tailTrace_3596497
  have hstable : (prefixWord ++ tailWord_3596497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596497).length < 2 ^ (prefixWord ++ tailWord_3596497).sum := by decide
  have hdescent : baseEnd_3596497 < baseStart_3596497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596542 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3596542 : Nat := 118140960795 + 3596542 * 2 ^ 59
def prefixEnd_3596542 : Nat := 4983230072969 + 3 ^ 40 * 3596542 * 2
def baseEnd_3596542 : Nat := 1231169826721848497723207

theorem tailTrace_3596542 : CollatzResearch.WordTrace tailWord_3596542 prefixEnd_3596542 1231169826721848497723207 := by
  unfold tailWord_3596542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397082917043756164565985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87451108890900032877685253 16397082917043756164565985)
  ·
    refine ⟨12297812187782817123424489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16397082917043756164565985 12297812187782817123424489)
    ·
      refine ⟨9223359140837112842568367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12297812187782817123424489 9223359140837112842568367)
      ·
        refine ⟨13835038711255669263852551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223359140837112842568367 13835038711255669263852551)
        ·
          refine ⟨20752558066883503895778827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835038711255669263852551 20752558066883503895778827)
          ·
            refine ⟨31128837100325255843668241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20752558066883503895778827 31128837100325255843668241)
            ·
              refine ⟨23346627825243941882751181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31128837100325255843668241 23346627825243941882751181)
              ·
                refine ⟨8754985434466478206031693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23346627825243941882751181 8754985434466478206031693)
                ·
                  refine ⟨3283119537924929327261885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8754985434466478206031693 3283119537924929327261885)
                  ·
                    refine ⟨1231169826721848497723207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283119537924929327261885 1231169826721848497723207)
                    ·
                      rfl

theorem cell22_3596542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3596542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596542 prefixEnd_3596542 := by exact prefixLift 3596542
  have htrace : WordTrace (prefixWord ++ tailWord_3596542) baseStart_3596542 baseEnd_3596542 := by
    simpa [prefixWord, tailWord_3596542, baseEnd_3596542] using wordTrace_append hprefix tailTrace_3596542
  have hstable : (prefixWord ++ tailWord_3596542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596542).length < 2 ^ (prefixWord ++ tailWord_3596542).sum := by decide
  have hdescent : baseEnd_3596542 < baseStart_3596542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596553 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_3596553 : Nat := 118140960795 + 3596553 * 2 ^ 59
def prefixEnd_3596553 : Nat := 4983230072969 + 3 ^ 40 * 3596553 * 2
def baseEnd_3596553 : Nat := 1231173592246648135698173

theorem tailTrace_3596553 : CollatzResearch.WordTrace tailWord_3596553 prefixEnd_3596553 1231173592246648135698173 := by
  unfold tailWord_3596553
  simp only [CollatzResearch.WordTrace]
  refine ⟨131177064539310198195178313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87451376359540132130118875 131177064539310198195178313)
  ·
    refine ⟨98382798404482648646383735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131177064539310198195178313 98382798404482648646383735)
    ·
      refine ⟨147574197606723972969575603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98382798404482648646383735 147574197606723972969575603)
      ·
        refine ⟨221361296410085959454363405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147574197606723972969575603 221361296410085959454363405)
        ·
          refine ⟨83010486153782234795386277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221361296410085959454363405 83010486153782234795386277)
          ·
            refine ⟨15564466153834169024134927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83010486153782234795386277 15564466153834169024134927)
            ·
              refine ⟨23346699230751253536202391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15564466153834169024134927 23346699230751253536202391)
              ·
                refine ⟨35020048846126880304303587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23346699230751253536202391 35020048846126880304303587)
                ·
                  refine ⟨52530073269190320456455381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35020048846126880304303587 52530073269190320456455381)
                  ·
                    refine ⟨1231173592246648135698173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52530073269190320456455381 1231173592246648135698173)
                    ·
                      rfl

theorem cell22_3596553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_3596553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596553 prefixEnd_3596553 := by exact prefixLift 3596553
  have htrace : WordTrace (prefixWord ++ tailWord_3596553) baseStart_3596553 baseEnd_3596553 := by
    simpa [prefixWord, tailWord_3596553, baseEnd_3596553] using wordTrace_append hprefix tailTrace_3596553
  have hstable : (prefixWord ++ tailWord_3596553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596553).length < 2 ^ (prefixWord ++ tailWord_3596553).sum := by decide
  have hdescent : baseEnd_3596553 < baseStart_3596553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596645 : List Nat := [1, 3, 1, 3, 1, 5, 8]
def baseStart_3596645 : Nat := 118140960795 + 3596645 * 2 ^ 59
def prefixEnd_3596645 : Nat := 4983230072969 + 3 ^ 40 * 3596645 * 2
def baseEnd_3596645 : Nat := 45600188360251502311033

theorem tailTrace_3596645 : CollatzResearch.WordTrace tailWord_3596645 prefixEnd_3596645 45600188360251502311033 := by
  unfold tailWord_3596645
  simp only [CollatzResearch.WordTrace]
  refine ⟨131180420054976897907527389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87453613369984598605018259 131180420054976897907527389)
  ·
    refine ⟨49192657520616336715322771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131180420054976897907527389 49192657520616336715322771)
    ·
      refine ⟨73788986280924505072984157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49192657520616336715322771 73788986280924505072984157)
      ·
        refine ⟨27670869855346689402369059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73788986280924505072984157 27670869855346689402369059)
        ·
          refine ⟨41506304783020034103553589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670869855346689402369059 41506304783020034103553589)
          ·
            refine ⟨3891216073408128197208149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41506304783020034103553589 3891216073408128197208149)
            ·
              refine ⟨45600188360251502311033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3891216073408128197208149 45600188360251502311033)
              ·
                rfl

theorem cell22_3596645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 8].length) (baseStart_3596645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596645 prefixEnd_3596645 := by exact prefixLift 3596645
  have htrace : WordTrace (prefixWord ++ tailWord_3596645) baseStart_3596645 baseEnd_3596645 := by
    simpa [prefixWord, tailWord_3596645, baseEnd_3596645] using wordTrace_append hprefix tailTrace_3596645
  have hstable : (prefixWord ++ tailWord_3596645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596645).length < 2 ^ (prefixWord ++ tailWord_3596645).sum := by decide
  have hdescent : baseEnd_3596645 < baseStart_3596645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596647 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3596647 : Nat := 118140960795 + 3596647 * 2 ^ 59
def prefixEnd_3596647 : Nat := 4983230072969 + 3 ^ 40 * 3596647 * 2
def baseEnd_3596647 : Nat := 1231205770367663223847885

theorem tailTrace_3596647 : CollatzResearch.WordTrace tailWord_3596647 prefixEnd_3596647 1231205770367663223847885 := by
  unfold tailWord_3596647
  simp only [CollatzResearch.WordTrace]
  refine ⟨131180493000969652249100195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87453662000646434832733463 131180493000969652249100195)
  ·
    refine ⟨196770739501454478373650293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131180493000969652249100195 196770739501454478373650293)
    ·
      refine ⟨18447256828261357347529715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196770739501454478373650293 18447256828261357347529715)
      ·
        refine ⟨27670885242392036021294573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447256828261357347529715 27670885242392036021294573)
        ·
          refine ⟨10376581965897013507985465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27670885242392036021294573 10376581965897013507985465)
          ·
            refine ⟨7782436474422760130989099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10376581965897013507985465 7782436474422760130989099)
            ·
              refine ⟨11673654711634140196483649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782436474422760130989099 11673654711634140196483649)
              ·
                refine ⟨8755241033725605147362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11673654711634140196483649 8755241033725605147362737)
                ·
                  refine ⟨6566430775294203860522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8755241033725605147362737 6566430775294203860522053)
                  ·
                    refine ⟨1231205770367663223847885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6566430775294203860522053 1231205770367663223847885)
                    ·
                      rfl

theorem cell22_3596647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3596647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596647 prefixEnd_3596647 := by exact prefixLift 3596647
  have htrace : WordTrace (prefixWord ++ tailWord_3596647) baseStart_3596647 baseEnd_3596647 := by
    simpa [prefixWord, tailWord_3596647, baseEnd_3596647] using wordTrace_append hprefix tailTrace_3596647
  have hstable : (prefixWord ++ tailWord_3596647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596647).length < 2 ^ (prefixWord ++ tailWord_3596647).sum := by decide
  have hdescent : baseEnd_3596647 < baseStart_3596647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596707 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 5]
def baseStart_3596707 : Nat := 118140960795 + 3596707 * 2 ^ 59
def prefixEnd_3596707 : Nat := 4983230072969 + 3 ^ 40 * 3596707 * 2
def baseEnd_3596707 : Nat := 410408769864614355782567

theorem tailTrace_3596707 : CollatzResearch.WordTrace tailWord_3596707 prefixEnd_3596707 410408769864614355782567 := by
  unfold tailWord_3596707
  simp only [CollatzResearch.WordTrace]
  refine ⟨131182681380752282496284375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87455120920501521664189583 131182681380752282496284375)
  ·
    refine ⟨196774022071128423744426563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131182681380752282496284375 196774022071128423744426563)
    ·
      refine ⟨295161033106692635616639845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196774022071128423744426563 295161033106692635616639845)
      ·
        refine ⟨55342693707504869178119971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295161033106692635616639845 55342693707504869178119971)
        ·
          refine ⟨83014040561257303767179957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55342693707504869178119971 83014040561257303767179957)
          ·
            refine ⟨7782566302617872228173121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83014040561257303767179957 7782566302617872228173121)
            ·
              refine ⟨5836924726963404171129841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7782566302617872228173121 5836924726963404171129841)
              ·
                refine ⟨4377693545222553128347381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836924726963404171129841 4377693545222553128347381)
                ·
                  refine ⟨410408769864614355782567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377693545222553128347381 410408769864614355782567)
                  ·
                    rfl

theorem cell22_3596707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].length) (baseStart_3596707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596707 prefixEnd_3596707 := by exact prefixLift 3596707
  have htrace : WordTrace (prefixWord ++ tailWord_3596707) baseStart_3596707 baseEnd_3596707 := by
    simpa [prefixWord, tailWord_3596707, baseEnd_3596707] using wordTrace_append hprefix tailTrace_3596707
  have hstable : (prefixWord ++ tailWord_3596707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596707).length < 2 ^ (prefixWord ++ tailWord_3596707).sum := by decide
  have hdescent : baseEnd_3596707 < baseStart_3596707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596711 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3596711 : Nat := 118140960795 + 3596711 * 2 ^ 59
def prefixEnd_3596711 : Nat := 4983230072969 + 3 ^ 40 * 3596711 * 2
def baseEnd_3596711 : Nat := 1231227678875588390247689

theorem tailTrace_3596711 : CollatzResearch.WordTrace tailWord_3596711 prefixEnd_3596711 1231227678875588390247689 := by
  unfold tailWord_3596711
  simp only [CollatzResearch.WordTrace]
  refine ⟨131182827272737791179429987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87455218181825194119619991 131182827272737791179429987)
  ·
    refine ⟨196774240909106686769144981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131182827272737791179429987 196774240909106686769144981)
    ·
      refine ⟨9223792542614375942303671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196774240909106686769144981 9223792542614375942303671)
      ·
        refine ⟨13835688813921563913455507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223792542614375942303671 13835688813921563913455507)
        ·
          refine ⟨20753533220882345870183261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835688813921563913455507 20753533220882345870183261)
          ·
            refine ⟨7782574957830879701318723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20753533220882345870183261 7782574957830879701318723)
            ·
              refine ⟨11673862436746319551978085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782574957830879701318723 11673862436746319551978085)
              ·
                refine ⟨2188849206889934915995891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11673862436746319551978085 2188849206889934915995891)
                ·
                  refine ⟨3283273810334902373993837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188849206889934915995891 3283273810334902373993837)
                  ·
                    refine ⟨1231227678875588390247689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283273810334902373993837 1231227678875588390247689)
                    ·
                      rfl

theorem cell22_3596711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3596711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596711 prefixEnd_3596711 := by exact prefixLift 3596711
  have htrace : WordTrace (prefixWord ++ tailWord_3596711) baseStart_3596711 baseEnd_3596711 := by
    simpa [prefixWord, tailWord_3596711, baseEnd_3596711] using wordTrace_append hprefix tailTrace_3596711
  have hstable : (prefixWord ++ tailWord_3596711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596711).length < 2 ^ (prefixWord ++ tailWord_3596711).sum := by decide
  have hdescent : baseEnd_3596711 < baseStart_3596711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596780 : List Nat := [2, 2, 1, 1, 2, 1, 4, 9]
def baseStart_3596780 : Nat := 118140960795 + 3596780 * 2 ^ 59
def prefixEnd_3596780 : Nat := 4983230072969 + 3 ^ 40 * 3596780 * 2
def baseEnd_3596780 : Nat := 136805699887299467808053

theorem tailTrace_3596780 : CollatzResearch.WordTrace tailWord_3596780 prefixEnd_3596780 136805699887299467808053 := by
  unfold tailWord_3596780
  simp only [CollatzResearch.WordTrace]
  refine ⟨65592671954743907981845897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87456895939658543975794529 65592671954743907981845897)
  ·
    refine ⟨49194503966057930986384423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65592671954743907981845897 49194503966057930986384423)
    ·
      refine ⟨73791755949086896479576635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49194503966057930986384423 73791755949086896479576635)
      ·
        refine ⟨110687633923630344719364953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73791755949086896479576635 110687633923630344719364953)
        ·
          refine ⟨83015725442722758539523715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110687633923630344719364953 83015725442722758539523715)
          ·
            refine ⟨124523588164084137809285573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83015725442722758539523715 124523588164084137809285573)
            ·
              refine ⟨23348172780765775839241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124523588164084137809285573 23348172780765775839241045)
              ·
                refine ⟨136805699887299467808053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23348172780765775839241045 136805699887299467808053)
                ·
                  rfl

theorem cell22_3596780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_3596780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596780 prefixEnd_3596780 := by exact prefixLift 3596780
  have htrace : WordTrace (prefixWord ++ tailWord_3596780) baseStart_3596780 baseEnd_3596780 := by
    simpa [prefixWord, tailWord_3596780, baseEnd_3596780] using wordTrace_append hprefix tailTrace_3596780
  have hstable : (prefixWord ++ tailWord_3596780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596780).length < 2 ^ (prefixWord ++ tailWord_3596780).sum := by decide
  have hdescent : baseEnd_3596780 < baseStart_3596780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596782 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3596782 : Nat := 118140960795 + 3596782 * 2 ^ 59
def prefixEnd_3596782 : Nat := 4983230072969 + 3 ^ 40 * 3596782 * 2
def baseEnd_3596782 : Nat := 1231251983626567871722471

theorem tailTrace_3596782 : CollatzResearch.WordTrace tailWord_3596782 prefixEnd_3596782 1231251983626567871722471 := by
  unfold tailWord_3596782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398177106935071288158075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87456944570320380203509733 16398177106935071288158075)
  ·
    refine ⟨24597265660402606932237113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16398177106935071288158075 24597265660402606932237113)
    ·
      refine ⟨18447949245301955199177835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24597265660402606932237113 18447949245301955199177835)
      ·
        refine ⟨27671923867952932798766753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447949245301955199177835 27671923867952932798766753)
        ·
          refine ⟨20753942900964699599075065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27671923867952932798766753 20753942900964699599075065)
          ·
            refine ⟨15565457175723524699306299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20753942900964699599075065 15565457175723524699306299)
            ·
              refine ⟨23348185763585287048959449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15565457175723524699306299 23348185763585287048959449)
              ·
                refine ⟨17511139322688965286719587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23348185763585287048959449 17511139322688965286719587)
                ·
                  refine ⟨26266708984033447930079381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17511139322688965286719587 26266708984033447930079381)
                  ·
                    refine ⟨1231251983626567871722471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26266708984033447930079381 1231251983626567871722471)
                    ·
                      rfl

theorem cell22_3596782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3596782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596782 prefixEnd_3596782 := by exact prefixLift 3596782
  have htrace : WordTrace (prefixWord ++ tailWord_3596782) baseStart_3596782 baseEnd_3596782 := by
    simpa [prefixWord, tailWord_3596782, baseEnd_3596782] using wordTrace_append hprefix tailTrace_3596782
  have hstable : (prefixWord ++ tailWord_3596782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596782).length < 2 ^ (prefixWord ++ tailWord_3596782).sum := by decide
  have hdescent : baseEnd_3596782 < baseStart_3596782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596887 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 6]
def baseStart_3596887 : Nat := 118140960795 + 3596887 * 2 ^ 59
def prefixEnd_3596887 : Nat := 4983230072969 + 3 ^ 40 * 3596887 * 2
def baseEnd_3596887 : Nat := 410429309090794199282383

theorem tailTrace_3596887 : CollatzResearch.WordTrace tailWord_3596887 prefixEnd_3596887 410429309090794199282383 := by
  unfold tailWord_3596887
  simp only [CollatzResearch.WordTrace]
  refine ⟨131189246520100173237836915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87459497680066782158557943 131189246520100173237836915)
  ·
    refine ⟨196783869780150259856755373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131189246520100173237836915 196783869780150259856755373)
    ·
      refine ⟨73793951167556347446283265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196783869780150259856755373 73793951167556347446283265)
      ·
        refine ⟨55345463375667260584712449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73793951167556347446283265 55345463375667260584712449)
        ·
          refine ⟨41509097531750445438534337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55345463375667260584712449 41509097531750445438534337)
          ·
            refine ⟨31131823148812834078900753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41509097531750445438534337 31131823148812834078900753)
            ·
              refine ⟨23348867361609625559175565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31131823148812834078900753 23348867361609625559175565)
              ·
                refine ⟨8755825260603609584690837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23348867361609625559175565 8755825260603609584690837)
                ·
                  refine ⟨410429309090794199282383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8755825260603609584690837 410429309090794199282383)
                  ·
                    rfl

theorem cell22_3596887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_3596887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596887 prefixEnd_3596887 := by exact prefixLift 3596887
  have htrace : WordTrace (prefixWord ++ tailWord_3596887) baseStart_3596887 baseEnd_3596887 := by
    simpa [prefixWord, tailWord_3596887, baseEnd_3596887] using wordTrace_append hprefix tailTrace_3596887
  have hstable : (prefixWord ++ tailWord_3596887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596887).length < 2 ^ (prefixWord ++ tailWord_3596887).sum := by decide
  have hdescent : baseEnd_3596887 < baseStart_3596887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596921 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 4]
def baseStart_3596921 : Nat := 118140960795 + 3596921 * 2 ^ 59
def prefixEnd_3596921 : Nat := 4983230072969 + 3 ^ 40 * 3596921 * 2
def baseEnd_3596921 : Nat := 410433188722405947499015

theorem tailTrace_3596921 : CollatzResearch.WordTrace tailWord_3596921 prefixEnd_3596921 410433188722405947499015 := by
  unfold tailWord_3596921
  simp only [CollatzResearch.WordTrace]
  refine ⟨131190486601976997044574617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87460324401317998029716411 131190486601976997044574617)
  ·
    refine ⟨98392864951482747783430963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131190486601976997044574617 98392864951482747783430963)
    ·
      refine ⟨147589297427224121675146445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98392864951482747783430963 147589297427224121675146445)
      ·
        refine ⟨55345986535209045628179917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147589297427224121675146445 55345986535209045628179917)
        ·
          refine ⟨20754744950703392110567469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55345986535209045628179917 20754744950703392110567469)
          ·
            refine ⟨7783029356513772041462801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20754744950703392110567469 7783029356513772041462801)
            ·
              refine ⟨5837272017385329031097101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7783029356513772041462801 5837272017385329031097101)
              ·
                refine ⟨2188977006519498386661413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5837272017385329031097101 2188977006519498386661413)
                ·
                  refine ⟨410433188722405947499015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188977006519498386661413 410433188722405947499015)
                  ·
                    rfl

theorem cell22_3596921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_3596921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3596921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3596921 prefixEnd_3596921 := by exact prefixLift 3596921
  have htrace : WordTrace (prefixWord ++ tailWord_3596921) baseStart_3596921 baseEnd_3596921 := by
    simpa [prefixWord, tailWord_3596921, baseEnd_3596921] using wordTrace_append hprefix tailTrace_3596921
  have hstable : (prefixWord ++ tailWord_3596921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596921).length < 2 ^ (prefixWord ++ tailWord_3596921).sum := by decide
  have hdescent : baseEnd_3596921 < baseStart_3596921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597007 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3597007 : Nat := 118140960795 + 3597007 * 2 ^ 59
def prefixEnd_3597007 : Nat := 4983230072969 + 3 ^ 40 * 3597007 * 2
def baseEnd_3597007 : Nat := 1231329005724742284846781

theorem tailTrace_3597007 : CollatzResearch.WordTrace tailWord_3597007 prefixEnd_3597007 1231329005724742284846781 := by
  unfold tailWord_3597007
  simp only [CollatzResearch.WordTrace]
  refine ⟨131193623279665433732205275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87462415519776955821470183 131193623279665433732205275)
  ·
    refine ⟨196790434919498150598307913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131193623279665433732205275 196790434919498150598307913)
    ·
      refine ⟨147592826189623612948730935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196790434919498150598307913 147592826189623612948730935)
      ·
        refine ⟨221389239284435419423096403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147592826189623612948730935 221389239284435419423096403)
        ·
          refine ⟨332083858926653129134644605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221389239284435419423096403 332083858926653129134644605)
          ·
            refine ⟨124531447097494923425491727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332083858926653129134644605 124531447097494923425491727)
            ·
              refine ⟨186797170646242385138237591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124531447097494923425491727 186797170646242385138237591)
              ·
                refine ⟨280195755969363577707356387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186797170646242385138237591 280195755969363577707356387)
                ·
                  refine ⟨420293633954045366561034581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280195755969363577707356387 420293633954045366561034581)
                  ·
                    refine ⟨1231329005724742284846781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 420293633954045366561034581 1231329005724742284846781)
                    ·
                      rfl

theorem cell22_3597007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3597007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597007 prefixEnd_3597007 := by exact prefixLift 3597007
  have htrace : WordTrace (prefixWord ++ tailWord_3597007) baseStart_3597007 baseEnd_3597007 := by
    simpa [prefixWord, tailWord_3597007, baseEnd_3597007] using wordTrace_append hprefix tailTrace_3597007
  have hstable : (prefixWord ++ tailWord_3597007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597007).length < 2 ^ (prefixWord ++ tailWord_3597007).sum := by decide
  have hdescent : baseEnd_3597007 < baseStart_3597007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597071 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 2, 3]
def baseStart_3597071 : Nat := 118140960795 + 3597071 * 2 ^ 59
def prefixEnd_3597071 : Nat := 4983230072969 + 3 ^ 40 * 3597071 * 2
def baseEnd_3597071 : Nat := 1231350914232667451246585

theorem tailTrace_3597071 : CollatzResearch.WordTrace tailWord_3597071 prefixEnd_3597071 1231350914232667451246585 := by
  unfold tailWord_3597071
  simp only [CollatzResearch.WordTrace]
  refine ⟨131195957551433572662535067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87463971700955715108356711 131195957551433572662535067)
  ·
    refine ⟨196793936327150358993802601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131195957551433572662535067 196793936327150358993802601)
    ·
      refine ⟨147595452245362769245351951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196793936327150358993802601 147595452245362769245351951)
      ·
        refine ⟨221393178368044153868027927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147595452245362769245351951 221393178368044153868027927)
        ·
          refine ⟨332089767552066230802041891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221393178368044153868027927 332089767552066230802041891)
          ·
            refine ⟨498134651328099346203062837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332089767552066230802041891 498134651328099346203062837)
            ·
              refine ⟨46700123562009313706537141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 498134651328099346203062837 46700123562009313706537141)
              ·
                refine ⟨4378136583938373159987857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46700123562009313706537141 4378136583938373159987857)
                ·
                  refine ⟨3283602437953779869990893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378136583938373159987857 3283602437953779869990893)
                  ·
                    refine ⟨1231350914232667451246585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283602437953779869990893 1231350914232667451246585)
                    ·
                      rfl

theorem cell22_3597071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_3597071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597071 prefixEnd_3597071 := by exact prefixLift 3597071
  have htrace : WordTrace (prefixWord ++ tailWord_3597071) baseStart_3597071 baseEnd_3597071 := by
    simpa [prefixWord, tailWord_3597071, baseEnd_3597071] using wordTrace_append hprefix tailTrace_3597071
  have hstable : (prefixWord ++ tailWord_3597071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597071).length < 2 ^ (prefixWord ++ tailWord_3597071).sum := by decide
  have hdescent : baseEnd_3597071 < baseStart_3597071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597092 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_3597092 : Nat := 118140960795 + 3597092 * 2 ^ 59
def prefixEnd_3597092 : Nat := 4983230072969 + 3 ^ 40 * 3597092 * 2
def baseEnd_3597092 : Nat := 1231358102961830396471521

theorem tailTrace_3597092 : CollatzResearch.WordTrace tailWord_3597092 prefixEnd_3597092 1231358102961830396471521 := by
  unfold tailWord_3597092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65598361742178746624524765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87464482322904995499366353 65598361742178746624524765)
  ·
    refine ⟨24599385653317029984196787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65598361742178746624524765 24599385653317029984196787)
    ·
      refine ⟨36899078479975544976295181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24599385653317029984196787 36899078479975544976295181)
      ·
        refine ⟨13837154429990829366110693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36899078479975544976295181 13837154429990829366110693)
        ·
          refine ⟨2594466455623280506145755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13837154429990829366110693 2594466455623280506145755)
          ·
            refine ⟨3891699683434920759218633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594466455623280506145755 3891699683434920759218633)
            ·
              refine ⟨2918774762576190569413975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891699683434920759218633 2918774762576190569413975)
              ·
                refine ⟨4378162143864285854120963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918774762576190569413975 4378162143864285854120963)
                ·
                  refine ⟨6567243215796428781181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378162143864285854120963 6567243215796428781181445)
                  ·
                    refine ⟨1231358102961830396471521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6567243215796428781181445 1231358102961830396471521)
                    ·
                      rfl

theorem cell22_3597092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_3597092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597092 prefixEnd_3597092 := by exact prefixLift 3597092
  have htrace : WordTrace (prefixWord ++ tailWord_3597092) baseStart_3597092 baseEnd_3597092 := by
    simpa [prefixWord, tailWord_3597092, baseEnd_3597092] using wordTrace_append hprefix tailTrace_3597092
  have hstable : (prefixWord ++ tailWord_3597092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597092).length < 2 ^ (prefixWord ++ tailWord_3597092).sum := by decide
  have hdescent : baseEnd_3597092 < baseStart_3597092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597144 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3597144 : Nat := 118140960795 + 3597144 * 2 ^ 59
def prefixEnd_3597144 : Nat := 4983230072969 + 3 ^ 40 * 3597144 * 2
def baseEnd_3597144 : Nat := 1231375903624519594171361

theorem tailTrace_3597144 : CollatzResearch.WordTrace tailWord_3597144 prefixEnd_3597144 1231375903624519594171361 := by
  unfold tailWord_3597144
  simp only [CollatzResearch.WordTrace]
  refine ⟨65599310040084553064971243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87465746720112737419961657 65599310040084553064971243)
  ·
    refine ⟨98398965060126829597456865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65599310040084553064971243 98398965060126829597456865)
    ·
      refine ⟨73799223795095122198092649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98398965060126829597456865 73799223795095122198092649)
      ·
        refine ⟨55349417846321341648569487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73799223795095122198092649 55349417846321341648569487)
        ·
          refine ⟨83024126769482012472854231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55349417846321341648569487 83024126769482012472854231)
          ·
            refine ⟨124536190154223018709281347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83024126769482012472854231 124536190154223018709281347)
            ·
              refine ⟨186804285231334528063922021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124536190154223018709281347 186804285231334528063922021)
              ·
                refine ⟨35025803480875224011985379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186804285231334528063922021 35025803480875224011985379)
                ·
                  refine ⟨52538705221312836017978069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35025803480875224011985379 52538705221312836017978069)
                  ·
                    refine ⟨1231375903624519594171361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52538705221312836017978069 1231375903624519594171361)
                    ·
                      rfl

theorem cell22_3597144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3597144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597144 prefixEnd_3597144 := by exact prefixLift 3597144
  have htrace : WordTrace (prefixWord ++ tailWord_3597144) baseStart_3597144 baseEnd_3597144 := by
    simpa [prefixWord, tailWord_3597144, baseEnd_3597144] using wordTrace_append hprefix tailTrace_3597144
  have hstable : (prefixWord ++ tailWord_3597144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597144).length < 2 ^ (prefixWord ++ tailWord_3597144).sum := by decide
  have hdescent : baseEnd_3597144 < baseStart_3597144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597193 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_3597193 : Nat := 118140960795 + 3597193 * 2 ^ 59
def prefixEnd_3597193 : Nat := 4983230072969 + 3 ^ 40 * 3597193 * 2
def baseEnd_3597193 : Nat := 1231392677325899799696211

theorem tailTrace_3597193 : CollatzResearch.WordTrace tailWord_3597193 prefixEnd_3597193 1231392677325899799696211 := by
  unfold tailWord_3597193
  simp only [CollatzResearch.WordTrace]
  refine ⟨131200407256991587498476233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87466938171327724998984155 131200407256991587498476233)
  ·
    refine ⟨98400305442743690623857175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131200407256991587498476233 98400305442743690623857175)
    ·
      refine ⟨147600458164115535935785763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98400305442743690623857175 147600458164115535935785763)
      ·
        refine ⟨221400687246173303903678645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147600458164115535935785763 221400687246173303903678645)
        ·
          refine ⟨20756314429328747240969873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221400687246173303903678645 20756314429328747240969873)
          ·
            refine ⟨15567235821996560430727405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20756314429328747240969873 15567235821996560430727405)
            ·
              refine ⟨5837713433248710161522777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15567235821996560430727405 5837713433248710161522777)
              ·
                refine ⟨4378285074936532621142083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5837713433248710161522777 4378285074936532621142083)
                ·
                  refine ⟨6567427612404798931713125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378285074936532621142083 6567427612404798931713125)
                  ·
                    refine ⟨1231392677325899799696211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6567427612404798931713125 1231392677325899799696211)
                    ·
                      rfl

theorem cell22_3597193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_3597193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597193 prefixEnd_3597193 := by exact prefixLift 3597193
  have htrace : WordTrace (prefixWord ++ tailWord_3597193) baseStart_3597193 baseEnd_3597193 := by
    simpa [prefixWord, tailWord_3597193, baseEnd_3597193] using wordTrace_append hprefix tailTrace_3597193
  have hstable : (prefixWord ++ tailWord_3597193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597193).length < 2 ^ (prefixWord ++ tailWord_3597193).sum := by decide
  have hdescent : baseEnd_3597193 < baseStart_3597193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597343 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 6]
def baseStart_3597343 : Nat := 118140960795 + 3597343 * 2 ^ 59
def prefixEnd_3597343 : Nat := 4983230072969 + 3 ^ 40 * 3597343 * 2
def baseEnd_3597343 : Nat := 410481341797116469481917

theorem tailTrace_3597343 : CollatzResearch.WordTrace tailWord_3597343 prefixEnd_3597343 410481341797116469481917 := by
  unfold tailWord_3597343
  simp only [CollatzResearch.WordTrace]
  refine ⟨131205878206448163116436683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87470585470965442077624455 131205878206448163116436683)
  ·
    refine ⟨196808817309672244674655025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131205878206448163116436683 196808817309672244674655025)
    ·
      refine ⟨147606612982254183505991269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196808817309672244674655025 147606612982254183505991269)
      ·
        refine ⟨27676239934172659407373363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147606612982254183505991269 27676239934172659407373363)
        ·
          refine ⟨41514359901258989111060045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27676239934172659407373363 41514359901258989111060045)
          ·
            refine ⟨15567884962972120916647517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41514359901258989111060045 15567884962972120916647517)
            ·
              refine ⟨5837956861114545343742819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15567884962972120916647517 5837956861114545343742819)
              ·
                refine ⟨8756935291671818015614229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837956861114545343742819 8756935291671818015614229)
                ·
                  refine ⟨410481341797116469481917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8756935291671818015614229 410481341797116469481917)
                  ·
                    rfl

theorem cell22_3597343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_3597343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597343 prefixEnd_3597343 := by exact prefixLift 3597343
  have htrace : WordTrace (prefixWord ++ tailWord_3597343) baseStart_3597343 baseEnd_3597343 := by
    simpa [prefixWord, tailWord_3597343, baseEnd_3597343] using wordTrace_append hprefix tailTrace_3597343
  have hstable : (prefixWord ++ tailWord_3597343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597343).length < 2 ^ (prefixWord ++ tailWord_3597343).sum := by decide
  have hdescent : baseEnd_3597343 < baseStart_3597343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597394 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3597394 : Nat := 118140960795 + 3597394 * 2 ^ 59
def prefixEnd_3597394 : Nat := 4983230072969 + 3 ^ 40 * 3597394 * 2
def baseEnd_3597394 : Nat := 410487161244534091806865

theorem tailTrace_3597394 : CollatzResearch.WordTrace tailWord_3597394 prefixEnd_3597394 410487161244534091806865 := by
  unfold tailWord_3597394
  simp only [CollatzResearch.WordTrace]
  refine ⟨32801934582315849706635809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87471825552842265884362157 32801934582315849706635809)
  ·
    refine ⟨24601450936736887279976857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32801934582315849706635809 24601450936736887279976857)
    ·
      refine ⟨18451088202552665459982643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24601450936736887279976857 18451088202552665459982643)
      ·
        refine ⟨27676632303828998189973965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451088202552665459982643 27676632303828998189973965)
        ·
          refine ⟨10378737113935874321240237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27676632303828998189973965 10378737113935874321240237)
          ·
            refine ⟨3892026417725952870465089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10378737113935874321240237 3892026417725952870465089)
            ·
              refine ⟨2919019813294464652848817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892026417725952870465089 2919019813294464652848817)
              ·
                refine ⟨2189264859970848489636613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919019813294464652848817 2189264859970848489636613)
                ·
                  refine ⟨410487161244534091806865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189264859970848489636613 410487161244534091806865)
                  ·
                    rfl

theorem cell22_3597394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3597394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597394 prefixEnd_3597394 := by exact prefixLift 3597394
  have htrace : WordTrace (prefixWord ++ tailWord_3597394) baseStart_3597394 baseEnd_3597394 := by
    simpa [prefixWord, tailWord_3597394, baseEnd_3597394] using wordTrace_append hprefix tailTrace_3597394
  have hstable : (prefixWord ++ tailWord_3597394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597394).length < 2 ^ (prefixWord ++ tailWord_3597394).sum := by decide
  have hdescent : baseEnd_3597394 < baseStart_3597394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597420 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_3597420 : Nat := 118140960795 + 3597420 * 2 ^ 59
def prefixEnd_3597420 : Nat := 4983230072969 + 3 ^ 40 * 3597420 * 2
def baseEnd_3597420 : Nat := 1231470384064946874270515

theorem tailTrace_3597420 : CollatzResearch.WordTrace tailWord_3597420 prefixEnd_3597420 1231470384064946874270515 := by
  unfold tailWord_3597420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65604343313584602633494857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87472457751446136844659809 65604343313584602633494857)
  ·
    refine ⟨49203257485188451975121143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65604343313584602633494857 49203257485188451975121143)
    ·
      refine ⟨73804886227782677962681715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49203257485188451975121143 73804886227782677962681715)
      ·
        refine ⟨110707329341674016944022573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73804886227782677962681715 110707329341674016944022573)
        ·
          refine ⟨41515248503127756354008465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110707329341674016944022573 41515248503127756354008465)
          ·
            refine ⟨31136436377345817265506349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41515248503127756354008465 31136436377345817265506349)
            ·
              refine ⟨11676163641504681474564881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31136436377345817265506349 11676163641504681474564881)
              ·
                refine ⟨8757122731128511105923661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11676163641504681474564881 8757122731128511105923661)
                ·
                  refine ⟨3283921024173191664721373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8757122731128511105923661 3283921024173191664721373)
                  ·
                    refine ⟨1231470384064946874270515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283921024173191664721373 1231470384064946874270515)
                    ·
                      rfl

theorem cell22_3597420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_3597420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597420 prefixEnd_3597420 := by exact prefixLift 3597420
  have htrace : WordTrace (prefixWord ++ tailWord_3597420) baseStart_3597420 baseEnd_3597420 := by
    simpa [prefixWord, tailWord_3597420, baseEnd_3597420] using wordTrace_append hprefix tailTrace_3597420
  have hstable : (prefixWord ++ tailWord_3597420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597420).length < 2 ^ (prefixWord ++ tailWord_3597420).sum := by decide
  have hdescent : baseEnd_3597420 < baseStart_3597420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597454 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3597454 : Nat := 118140960795 + 3597454 * 2 ^ 59
def prefixEnd_3597454 : Nat := 4983230072969 + 3 ^ 40 * 3597454 * 2
def baseEnd_3597454 : Nat := 1231482022959782118920411

theorem tailTrace_3597454 : CollatzResearch.WordTrace tailWord_3597454 prefixEnd_3597454 1231482022959782118920411 := by
  unfold tailWord_3597454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401240838630753634215927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87473284472697352715818277 16401240838630753634215927)
  ·
    refine ⟨24601861257946130451323891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16401240838630753634215927 24601861257946130451323891)
    ·
      refine ⟨36902791886919195676985837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24601861257946130451323891 36902791886919195676985837)
      ·
        refine ⟨13838546957594698378869689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36902791886919195676985837 13838546957594698378869689)
        ·
          refine ⟨10378910218196023784152267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13838546957594698378869689 10378910218196023784152267)
          ·
            refine ⟨15568365327294035676228401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378910218196023784152267 15568365327294035676228401)
            ·
              refine ⟨11676273995470526757171301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15568365327294035676228401 11676273995470526757171301)
              ·
                refine ⟨2189301374150723766969619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11676273995470526757171301 2189301374150723766969619)
                ·
                  refine ⟨3283952061226085650454429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189301374150723766969619 3283952061226085650454429)
                  ·
                    refine ⟨1231482022959782118920411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283952061226085650454429 1231482022959782118920411)
                    ·
                      rfl

theorem cell22_3597454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3597454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597454 prefixEnd_3597454 := by exact prefixLift 3597454
  have htrace : WordTrace (prefixWord ++ tailWord_3597454) baseStart_3597454 baseEnd_3597454 := by
    simpa [prefixWord, tailWord_3597454, baseEnd_3597454] using wordTrace_append hprefix tailTrace_3597454
  have hstable : (prefixWord ++ tailWord_3597454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597454).length < 2 ^ (prefixWord ++ tailWord_3597454).sum := by decide
  have hdescent : baseEnd_3597454 < baseStart_3597454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597585 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 5]
def baseStart_3597585 : Nat := 118140960795 + 3597585 * 2 ^ 59
def prefixEnd_3597585 : Nat := 4983230072969 + 3 ^ 40 * 3597585 * 2
def baseEnd_3597585 : Nat := 410508955645647147965003

theorem tailTrace_3597585 : CollatzResearch.WordTrace tailWord_3597585 prefixEnd_3597585 410508955645647147965003 := by
  unfold tailWord_3597585
  simp only [CollatzResearch.WordTrace]
  refine ⟨131214704671571438446746209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87476469781047625631164139 131214704671571438446746209)
  ·
    refine ⟨98411028503678578835059657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131214704671571438446746209 98411028503678578835059657)
    ·
      refine ⟨73808271377758934126294743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98411028503678578835059657 73808271377758934126294743)
      ·
        refine ⟨110712407066638401189442115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73808271377758934126294743 110712407066638401189442115)
        ·
          refine ⟨166068610599957601784163173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110712407066638401189442115 166068610599957601784163173)
          ·
            refine ⟨31137864487492050334530595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166068610599957601784163173 31137864487492050334530595)
            ·
              refine ⟨46706796731238075501795893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31137864487492050334530595 46706796731238075501795893)
              ·
                refine ⟨4378762193553569578293365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46706796731238075501795893 4378762193553569578293365)
                ·
                  refine ⟨410508955645647147965003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4378762193553569578293365 410508955645647147965003)
                  ·
                    rfl

theorem cell22_3597585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_3597585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597585 prefixEnd_3597585 := by exact prefixLift 3597585
  have htrace : WordTrace (prefixWord ++ tailWord_3597585) baseStart_3597585 baseEnd_3597585 := by
    simpa [prefixWord, tailWord_3597585, baseEnd_3597585] using wordTrace_append hprefix tailTrace_3597585
  have hstable : (prefixWord ++ tailWord_3597585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597585).length < 2 ^ (prefixWord ++ tailWord_3597585).sum := by decide
  have hdescent : baseEnd_3597585 < baseStart_3597585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597636 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3597636 : Nat := 118140960795 + 3597636 * 2 ^ 59
def prefixEnd_3597636 : Nat := 4983230072969 + 3 ^ 40 * 3597636 * 2
def baseEnd_3597636 : Nat := 410514775093064770289951

theorem tailTrace_3597636 : CollatzResearch.WordTrace tailWord_3597636 prefixEnd_3597636 410514775093064770289951 := by
  unfold tailWord_3597636
  simp only [CollatzResearch.WordTrace]
  refine ⟨65608282397193337078426381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87477709862924449437901841 65608282397193337078426381)
  ·
    refine ⟨24603105898947501404409893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65608282397193337078426381 24603105898947501404409893)
    ·
      refine ⟨4613082356052656513326855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24603105898947501404409893 4613082356052656513326855)
      ·
        refine ⟨6919623534078984769990283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613082356052656513326855 6919623534078984769990283)
        ·
          refine ⟨10379435301118477154985425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919623534078984769990283 10379435301118477154985425)
          ·
            refine ⟨7784576475838857866239069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10379435301118477154985425 7784576475838857866239069)
            ·
              refine ⟨2919216178439571699839651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7784576475838857866239069 2919216178439571699839651)
              ·
                refine ⟨4378824267659357549759477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919216178439571699839651 4378824267659357549759477)
                ·
                  refine ⟨410514775093064770289951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4378824267659357549759477 410514775093064770289951)
                  ·
                    rfl

theorem cell22_3597636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3597636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597636 prefixEnd_3597636 := by exact prefixLift 3597636
  have htrace : WordTrace (prefixWord ++ tailWord_3597636) baseStart_3597636 baseEnd_3597636 := by
    simpa [prefixWord, tailWord_3597636, baseEnd_3597636] using wordTrace_append hprefix tailTrace_3597636
  have hstable : (prefixWord ++ tailWord_3597636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597636).length < 2 ^ (prefixWord ++ tailWord_3597636).sum := by decide
  have hdescent : baseEnd_3597636 < baseStart_3597636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597664 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_3597664 : Nat := 118140960795 + 3597664 * 2 ^ 59
def prefixEnd_3597664 : Nat := 4983230072969 + 3 ^ 40 * 3597664 * 2
def baseEnd_3597664 : Nat := 410517970083803857056589

theorem tailTrace_3597664 : CollatzResearch.WordTrace tailWord_3597664 prefixEnd_3597664 410517970083803857056589 := by
  unfold tailWord_3597664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65608793019142617469436023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87478390692190156625914697 65608793019142617469436023)
  ·
    refine ⟨98413189528713926204154035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65608793019142617469436023 98413189528713926204154035)
    ·
      refine ⟨147619784293070889306231053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98413189528713926204154035 147619784293070889306231053)
      ·
        refine ⟨55357419109901583489836645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147619784293070889306231053 55357419109901583489836645)
        ·
          refine ⟨10379516083106546904344371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55357419109901583489836645 10379516083106546904344371)
          ·
            refine ⟨15569274124659820356516557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379516083106546904344371 15569274124659820356516557)
            ·
              refine ⟨5838477796747432633693709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15569274124659820356516557 5838477796747432633693709)
              ·
                refine ⟨2189429173780287237635141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5838477796747432633693709 2189429173780287237635141)
                ·
                  refine ⟨410517970083803857056589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189429173780287237635141 410517970083803857056589)
                  ·
                    rfl

theorem cell22_3597664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_3597664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597664 prefixEnd_3597664 := by exact prefixLift 3597664
  have htrace : WordTrace (prefixWord ++ tailWord_3597664) baseStart_3597664 baseEnd_3597664 := by
    simpa [prefixWord, tailWord_3597664, baseEnd_3597664] using wordTrace_append hprefix tailTrace_3597664
  have hstable : (prefixWord ++ tailWord_3597664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597664).length < 2 ^ (prefixWord ++ tailWord_3597664).sum := by decide
  have hdescent : baseEnd_3597664 < baseStart_3597664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597677 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3597677 : Nat := 118140960795 + 3597677 * 2 ^ 59
def prefixEnd_3597677 : Nat := 4983230072969 + 3 ^ 40 * 3597677 * 2
def baseEnd_3597677 : Nat := 1231558360417083870594727

theorem tailTrace_3597677 : CollatzResearch.WordTrace tailWord_3597677 prefixEnd_3597677 1231558360417083870594727 := by
  unfold tailWord_3597677
  simp only [CollatzResearch.WordTrace]
  refine ⟨131218060187238138159095285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87478706791492092106063523 131218060187238138159095285)
  ·
    refine ⟨12301693142553575452415183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131218060187238138159095285 12301693142553575452415183)
    ·
      refine ⟨18452539713830363178622775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12301693142553575452415183 18452539713830363178622775)
      ·
        refine ⟨27678809570745544767934163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18452539713830363178622775 27678809570745544767934163)
        ·
          refine ⟨41518214356118317151901245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678809570745544767934163 41518214356118317151901245)
          ·
            refine ⟨15569330383544368931962967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41518214356118317151901245 15569330383544368931962967)
            ·
              refine ⟨23353995575316553397944451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15569330383544368931962967 23353995575316553397944451)
              ·
                refine ⟨35030993362974830096916677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23353995575316553397944451 35030993362974830096916677)
                ·
                  refine ⟨6568311255557780643171877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35030993362974830096916677 6568311255557780643171877)
                  ·
                    refine ⟨1231558360417083870594727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568311255557780643171877 1231558360417083870594727)
                    ·
                      rfl

theorem cell22_3597677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3597677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597677 prefixEnd_3597677 := by exact prefixLift 3597677
  have htrace : WordTrace (prefixWord ++ tailWord_3597677) baseStart_3597677 baseEnd_3597677 := by
    simpa [prefixWord, tailWord_3597677, baseEnd_3597677] using wordTrace_append hprefix tailTrace_3597677
  have hstable : (prefixWord ++ tailWord_3597677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597677).length < 2 ^ (prefixWord ++ tailWord_3597677).sum := by decide
  have hdescent : baseEnd_3597677 < baseStart_3597677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597707 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 5, 3]
def baseStart_3597707 : Nat := 118140960795 + 3597707 * 2 ^ 59
def prefixEnd_3597707 : Nat := 4983230072969 + 3 ^ 40 * 3597707 * 2
def baseEnd_3597707 : Nat := 1231568630030173792344635

theorem tailTrace_3597707 : CollatzResearch.WordTrace tailWord_3597707 prefixEnd_3597707 1231568630030173792344635 := by
  unfold tailWord_3597707
  simp only [CollatzResearch.WordTrace]
  refine ⟨131219154377129453282687375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87479436251419635521791583 131219154377129453282687375)
  ·
    refine ⟨196828731565694179924031063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131219154377129453282687375 196828731565694179924031063)
    ·
      refine ⟨295243097348541269886046595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196828731565694179924031063 295243097348541269886046595)
      ·
        refine ⟨442864646022811904829069893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295243097348541269886046595 442864646022811904829069893)
        ·
          refine ⟨83037121129277232155450605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442864646022811904829069893 83037121129277232155450605)
          ·
            refine ⟨31138920423478962058293977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83037121129277232155450605 31138920423478962058293977)
            ·
              refine ⟨23354190317609221543720483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31138920423478962058293977 23354190317609221543720483)
              ·
                refine ⟨35031285476413832315580725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23354190317609221543720483 35031285476413832315580725)
                ·
                  refine ⟨3284183013413796779585693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35031285476413832315580725 3284183013413796779585693)
                  ·
                    refine ⟨1231568630030173792344635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3284183013413796779585693 1231568630030173792344635)
                    ·
                      rfl

theorem cell22_3597707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].length) (baseStart_3597707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597707 prefixEnd_3597707 := by exact prefixLift 3597707
  have htrace : WordTrace (prefixWord ++ tailWord_3597707) baseStart_3597707 baseEnd_3597707 := by
    simpa [prefixWord, tailWord_3597707, baseEnd_3597707] using wordTrace_append hprefix tailTrace_3597707
  have hstable : (prefixWord ++ tailWord_3597707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597707).length < 2 ^ (prefixWord ++ tailWord_3597707).sum := by decide
  have hdescent : baseEnd_3597707 < baseStart_3597707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597762 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3597762 : Nat := 118140960795 + 3597762 * 2 ^ 59
def prefixEnd_3597762 : Nat := 4983230072969 + 3 ^ 40 * 3597762 * 2
def baseEnd_3597762 : Nat := 1231587457654171982219467

theorem tailTrace_3597762 : CollatzResearch.WordTrace tailWord_3597762 prefixEnd_3597762 1231587457654171982219467 := by
  unfold tailWord_3597762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805290097982549418984885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87480773594620131783959693 32805290097982549418984885)
  ·
    refine ⟨3075495946685864008029833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32805290097982549418984885 3075495946685864008029833)
    ·
      refine ⟨2306621960014398006022375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3075495946685864008029833 2306621960014398006022375)
      ·
        refine ⟨3459932940021597009033563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306621960014398006022375 3459932940021597009033563)
        ·
          refine ⟨5189899410032395513550345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459932940021597009033563 5189899410032395513550345)
          ·
            refine ⟨3892424557524296635162759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189899410032395513550345 3892424557524296635162759)
            ·
              refine ⟨5838636836286444952744139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892424557524296635162759 5838636836286444952744139)
              ·
                refine ⟨8757955254429667429116209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838636836286444952744139 8757955254429667429116209)
                ·
                  refine ⟨6568466440822250571837157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8757955254429667429116209 6568466440822250571837157)
                  ·
                    refine ⟨1231587457654171982219467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568466440822250571837157 1231587457654171982219467)
                    ·
                      rfl

theorem cell22_3597762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3597762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597762 prefixEnd_3597762 := by exact prefixLift 3597762
  have htrace : WordTrace (prefixWord ++ tailWord_3597762) baseStart_3597762 baseEnd_3597762 := by
    simpa [prefixWord, tailWord_3597762, baseEnd_3597762] using wordTrace_append hprefix tailTrace_3597762
  have hstable : (prefixWord ++ tailWord_3597762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597762).length < 2 ^ (prefixWord ++ tailWord_3597762).sum := by decide
  have hdescent : baseEnd_3597762 < baseStart_3597762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597767 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3597767 : Nat := 118140960795 + 3597767 * 2 ^ 59
def prefixEnd_3597767 : Nat := 4983230072969 + 3 ^ 40 * 3597767 * 2
def baseEnd_3597767 : Nat := 1231589169256353635844451

theorem tailTrace_3597767 : CollatzResearch.WordTrace tailWord_3597767 prefixEnd_3597767 1231589169256353635844451 := by
  unfold tailWord_3597767
  simp only [CollatzResearch.WordTrace]
  refine ⟨131221342756912083529871555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87480895171274722353247703 131221342756912083529871555)
  ·
    refine ⟨196832014135368125294807333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131221342756912083529871555 196832014135368125294807333)
    ·
      refine ⟨36906002650381523492776375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196832014135368125294807333 36906002650381523492776375)
      ·
        refine ⟨55359003975572285239164563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36906002650381523492776375 55359003975572285239164563)
        ·
          refine ⟨83038505963358427858746845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55359003975572285239164563 83038505963358427858746845)
          ·
            refine ⟨31139439736259410447030067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83038505963358427858746845 31139439736259410447030067)
            ·
              refine ⟨46709159604389115670545101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31139439736259410447030067 46709159604389115670545101)
              ·
                refine ⟨17515934851645918376454413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46709159604389115670545101 17515934851645918376454413)
                ·
                  refine ⟨6568475569367219391170405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17515934851645918376454413 6568475569367219391170405)
                  ·
                    refine ⟨1231589169256353635844451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568475569367219391170405 1231589169256353635844451)
                    ·
                      rfl

theorem cell22_3597767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3597767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597767 prefixEnd_3597767 := by exact prefixLift 3597767
  have htrace : WordTrace (prefixWord ++ tailWord_3597767) baseStart_3597767 baseEnd_3597767 := by
    simpa [prefixWord, tailWord_3597767, baseEnd_3597767] using wordTrace_append hprefix tailTrace_3597767
  have hstable : (prefixWord ++ tailWord_3597767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597767).length < 2 ^ (prefixWord ++ tailWord_3597767).sum := by decide
  have hdescent : baseEnd_3597767 < baseStart_3597767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597799 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 6]
def baseStart_3597799 : Nat := 118140960795 + 3597799 * 2 ^ 59
def prefixEnd_3597799 : Nat := 4983230072969 + 3 ^ 40 * 3597799 * 2
def baseEnd_3597799 : Nat := 410533374503438739681451

theorem tailTrace_3597799 : CollatzResearch.WordTrace tailWord_3597799 prefixEnd_3597799 410533374503438739681451 := by
  unfold tailWord_3597799
  simp only [CollatzResearch.WordTrace]
  refine ⟨131222509892796152995036451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87481673261864101996690967 131222509892796152995036451)
  ·
    refine ⟨196833764839194229492554677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131222509892796152995036451 196833764839194229492554677)
    ·
      refine ⟨18453165453674459014927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196833764839194229492554677 18453165453674459014927001)
      ·
        refine ⟨13839874090255844261195251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18453165453674459014927001 13839874090255844261195251)
        ·
          refine ⟨20759811135383766391792877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13839874090255844261195251 20759811135383766391792877)
          ·
            refine ⟨7784929175768912396922329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20759811135383766391792877 7784929175768912396922329)
            ·
              refine ⟨5838696881826684297691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7784929175768912396922329 5838696881826684297691747)
              ·
                refine ⟨8758045322740026446537621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838696881826684297691747 8758045322740026446537621)
                ·
                  refine ⟨410533374503438739681451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8758045322740026446537621 410533374503438739681451)
                  ·
                    rfl

theorem cell22_3597799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_3597799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597799 prefixEnd_3597799 := by exact prefixLift 3597799
  have htrace : WordTrace (prefixWord ++ tailWord_3597799) baseStart_3597799 baseEnd_3597799 := by
    simpa [prefixWord, tailWord_3597799, baseEnd_3597799] using wordTrace_append hprefix tailTrace_3597799
  have hstable : (prefixWord ++ tailWord_3597799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597799).length < 2 ^ (prefixWord ++ tailWord_3597799).sum := by decide
  have hdescent : baseEnd_3597799 < baseStart_3597799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597906 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3597906 : Nat := 118140960795 + 3597906 * 2 ^ 59
def prefixEnd_3597906 : Nat := 4983230072969 + 3 ^ 40 * 3597906 * 2
def baseEnd_3597906 : Nat := 410545583932334535539675

theorem tailTrace_3597906 : CollatzResearch.WordTrace tailWord_3597906 prefixEnd_3597906 410545583932334535539675 := by
  unfold tailWord_3597906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806603125852127567295393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87484275002272340179454381 32806603125852127567295393)
  ·
    refine ⟨24604952344389095675471545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32806603125852127567295393 24604952344389095675471545)
    ·
      refine ⟨18453714258291821756603659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24604952344389095675471545 18453714258291821756603659)
      ·
        refine ⟨27680571387437732634905489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18453714258291821756603659 27680571387437732634905489)
        ·
          refine ⟨20760428540578299476179117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680571387437732634905489 20760428540578299476179117)
          ·
            refine ⟨7785160702716862303567169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20760428540578299476179117 7785160702716862303567169)
            ·
              refine ⟨5838870527037646727675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785160702716862303567169 5838870527037646727675377)
              ·
                refine ⟨4379152895278235045756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838870527037646727675377 4379152895278235045756533)
                ·
                  refine ⟨410545583932334535539675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4379152895278235045756533 410545583932334535539675)
                  ·
                    rfl

theorem cell22_3597906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3597906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597906 prefixEnd_3597906 := by exact prefixLift 3597906
  have htrace : WordTrace (prefixWord ++ tailWord_3597906) baseStart_3597906 baseEnd_3597906 := by
    simpa [prefixWord, tailWord_3597906, baseEnd_3597906] using wordTrace_append hprefix tailTrace_3597906
  have hstable : (prefixWord ++ tailWord_3597906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597906).length < 2 ^ (prefixWord ++ tailWord_3597906).sum := by decide
  have hdescent : baseEnd_3597906 < baseStart_3597906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597953 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3597953 : Nat := 118140960795 + 3597953 * 2 ^ 59
def prefixEnd_3597953 : Nat := 4983230072969 + 3 ^ 40 * 3597953 * 2
def baseEnd_3597953 : Nat := 1231652840857511150693881

theorem tailTrace_3597953 : CollatzResearch.WordTrace tailWord_3597953 prefixEnd_3597953 1231652840857511150693881 := by
  unfold tailWord_3597953
  simp only [CollatzResearch.WordTrace]
  refine ⟨131228126734238237296142513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87485417822825491530761675 131228126734238237296142513)
  ·
    refine ⟨98421095050678677972106885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131228126734238237296142513 98421095050678677972106885)
    ·
      refine ⟨18453955322002252119770041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98421095050678677972106885 18453955322002252119770041)
      ·
        refine ⟨13840466491501689089827531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18453955322002252119770041 13840466491501689089827531)
        ·
          refine ⟨20760699737252533634741297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13840466491501689089827531 20760699737252533634741297)
          ·
            refine ⟨15570524802939400226055973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20760699737252533634741297 15570524802939400226055973)
            ·
              refine ⟨2919473400551137542385495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15570524802939400226055973 2919473400551137542385495)
              ·
                refine ⟨4379210100826706313578243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919473400551137542385495 4379210100826706313578243)
                ·
                  refine ⟨6568815151240059470367365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379210100826706313578243 6568815151240059470367365)
                  ·
                    refine ⟨1231652840857511150693881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568815151240059470367365 1231652840857511150693881)
                    ·
                      rfl

theorem cell22_3597953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3597953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597953 prefixEnd_3597953 := by exact prefixLift 3597953
  have htrace : WordTrace (prefixWord ++ tailWord_3597953) baseStart_3597953 baseEnd_3597953 := by
    simpa [prefixWord, tailWord_3597953, baseEnd_3597953] using wordTrace_append hprefix tailTrace_3597953
  have hstable : (prefixWord ++ tailWord_3597953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597953).length < 2 ^ (prefixWord ++ tailWord_3597953).sum := by decide
  have hdescent : baseEnd_3597953 < baseStart_3597953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3597964 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3597964 : Nat := 118140960795 + 3597964 * 2 ^ 59
def prefixEnd_3597964 : Nat := 4983230072969 + 3 ^ 40 * 3597964 * 2
def baseEnd_3597964 : Nat := 1231656606382310788668847

theorem tailTrace_3597964 : CollatzResearch.WordTrace tailWord_3597964 prefixEnd_3597964 1231656606382310788668847 := by
  unfold tailWord_3597964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65614263968599193087396473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87485685291465590783195297 65614263968599193087396473)
  ·
    refine ⟨49210697976449394815547355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65614263968599193087396473 49210697976449394815547355)
    ·
      refine ⟨73816046964674092223321033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49210697976449394815547355 73816046964674092223321033)
      ·
        refine ⟨55362035223505569167490775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73816046964674092223321033 55362035223505569167490775)
        ·
          refine ⟨83043052835258353751236163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55362035223505569167490775 83043052835258353751236163)
          ·
            refine ⟨124564579252887530626854245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83043052835258353751236163 124564579252887530626854245)
            ·
              refine ⟨23355858609916411992535171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124564579252887530626854245 23355858609916411992535171)
              ·
                refine ⟨35033787914874617988802757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23355858609916411992535171 35033787914874617988802757)
                ·
                  refine ⟨6568835234038990872900517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35033787914874617988802757 6568835234038990872900517)
                  ·
                    refine ⟨1231656606382310788668847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568835234038990872900517 1231656606382310788668847)
                    ·
                      rfl

theorem cell22_3597964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3597964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3597964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3597964 prefixEnd_3597964 := by exact prefixLift 3597964
  have htrace : WordTrace (prefixWord ++ tailWord_3597964) baseStart_3597964 baseEnd_3597964 := by
    simpa [prefixWord, tailWord_3597964, baseEnd_3597964] using wordTrace_append hprefix tailTrace_3597964
  have hstable : (prefixWord ++ tailWord_3597964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3597964).length < 2 ^ (prefixWord ++ tailWord_3597964).sum := by decide
  have hdescent : baseEnd_3597964 < baseStart_3597964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3597964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598024 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_3598024 : Nat := 118140960795 + 3598024 * 2 ^ 59
def prefixEnd_3598024 : Nat := 4983230072969 + 3 ^ 40 * 3598024 * 2
def baseEnd_3598024 : Nat := 410559048536163544056221

theorem tailTrace_3598024 : CollatzResearch.WordTrace tailWord_3598024 prefixEnd_3598024 410559048536163544056221 := by
  unfold tailWord_3598024
  simp only [CollatzResearch.WordTrace]
  refine ⟨65615358158490508210988563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87487144211320677614651417 65615358158490508210988563)
  ·
    refine ⟨98423037237735762316482845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65615358158490508210988563 98423037237735762316482845)
    ·
      refine ⟨36908638964150910868681067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98423037237735762316482845 36908638964150910868681067)
      ·
        refine ⟨55362958446226366303021601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36908638964150910868681067 55362958446226366303021601)
        ·
          refine ⟨41522218834669774727266201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55362958446226366303021601 41522218834669774727266201)
          ·
            refine ⟨31141664126002331045449651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41522218834669774727266201 31141664126002331045449651)
            ·
              refine ⟨46712496189003496568174477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31141664126002331045449651 46712496189003496568174477)
              ·
                refine ⟨17517186070876311213065429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46712496189003496568174477 17517186070876311213065429)
                ·
                  refine ⟨410559048536163544056221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17517186070876311213065429 410559048536163544056221)
                  ·
                    rfl

theorem cell22_3598024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_3598024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598024 prefixEnd_3598024 := by exact prefixLift 3598024
  have htrace : WordTrace (prefixWord ++ tailWord_3598024) baseStart_3598024 baseEnd_3598024 := by
    simpa [prefixWord, tailWord_3598024, baseEnd_3598024] using wordTrace_append hprefix tailTrace_3598024
  have hstable : (prefixWord ++ tailWord_3598024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598024).length < 2 ^ (prefixWord ++ tailWord_3598024).sum := by decide
  have hdescent : baseEnd_3598024 < baseStart_3598024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598039 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3598039 : Nat := 118140960795 + 3598039 * 2 ^ 59
def prefixEnd_3598039 : Nat := 4983230072969 + 3 ^ 40 * 3598039 * 2
def baseEnd_3598039 : Nat := 1231682280415035593043617

theorem tailTrace_3598039 : CollatzResearch.WordTrace tailWord_3598039 prefixEnd_3598039 1231682280415035593043617 := by
  unfold tailWord_3598039
  simp only [CollatzResearch.WordTrace]
  refine ⟨131231263411926673983773171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87487508941284449322515447 131231263411926673983773171)
  ·
    refine ⟨196846895117890010975659757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131231263411926673983773171 196846895117890010975659757)
    ·
      refine ⟨73817585669208754115872409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196846895117890010975659757 73817585669208754115872409)
      ·
        refine ⟨55363189251906565586904307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73817585669208754115872409 55363189251906565586904307)
        ·
          refine ⟨83044783877859848380356461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55363189251906565586904307 83044783877859848380356461)
          ·
            refine ⟨31141793954197443142633673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83044783877859848380356461 31141793954197443142633673)
            ·
              refine ⟨23356345465648082356975255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31141793954197443142633673 23356345465648082356975255)
              ·
                refine ⟨35034518198472123535462883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23356345465648082356975255 35034518198472123535462883)
                ·
                  refine ⟨52551777297708185303194325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35034518198472123535462883 52551777297708185303194325)
                  ·
                    refine ⟨1231682280415035593043617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52551777297708185303194325 1231682280415035593043617)
                    ·
                      rfl

theorem cell22_3598039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3598039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598039 prefixEnd_3598039 := by exact prefixLift 3598039
  have htrace : WordTrace (prefixWord ++ tailWord_3598039) baseStart_3598039 baseEnd_3598039 := by
    simpa [prefixWord, tailWord_3598039, baseEnd_3598039] using wordTrace_append hprefix tailTrace_3598039
  have hstable : (prefixWord ++ tailWord_3598039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598039).length < 2 ^ (prefixWord ++ tailWord_3598039).sum := by decide
  have hdescent : baseEnd_3598039 < baseStart_3598039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598041 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 5]
def baseStart_3598041 : Nat := 118140960795 + 3598041 * 2 ^ 59
def prefixEnd_3598041 : Nat := 4983230072969 + 3 ^ 40 * 3598041 * 2
def baseEnd_3598041 : Nat := 410560988351969418164537

theorem tailTrace_3598041 : CollatzResearch.WordTrace tailWord_3598041 prefixEnd_3598041 410560988351969418164537 := by
  unfold tailWord_3598041
  simp only [CollatzResearch.WordTrace]
  refine ⟨131231336357919428325345977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87487557571946285550230651 131231336357919428325345977)
  ·
    refine ⟨98423502268439571244009483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131231336357919428325345977 98423502268439571244009483)
    ·
      refine ⟨147635253402659356866014225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98423502268439571244009483 147635253402659356866014225)
      ·
        refine ⟨110726440051994517649510669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147635253402659356866014225 110726440051994517649510669)
        ·
          refine ⟨41522415019497944118566501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110726440051994517649510669 41522415019497944118566501)
          ·
            refine ⟨7785452816155864522231219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41522415019497944118566501 7785452816155864522231219)
            ·
              refine ⟨11678179224233796783346829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785452816155864522231219 11678179224233796783346829)
              ·
                refine ⟨4379317209087673793755061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11678179224233796783346829 4379317209087673793755061)
                ·
                  refine ⟨410560988351969418164537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4379317209087673793755061 410560988351969418164537)
                  ·
                    rfl

theorem cell22_3598041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_3598041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598041 prefixEnd_3598041 := by exact prefixLift 3598041
  have htrace : WordTrace (prefixWord ++ tailWord_3598041) baseStart_3598041 baseEnd_3598041 := by
    simpa [prefixWord, tailWord_3598041, baseEnd_3598041] using wordTrace_append hprefix tailTrace_3598041
  have hstable : (prefixWord ++ tailWord_3598041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598041).length < 2 ^ (prefixWord ++ tailWord_3598041).sum := by decide
  have hdescent : baseEnd_3598041 < baseStart_3598041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598071 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3598071 : Nat := 118140960795 + 3598071 * 2 ^ 59
def prefixEnd_3598071 : Nat := 4983230072969 + 3 ^ 40 * 3598071 * 2
def baseEnd_3598071 : Nat := 1231693234668998176243519

theorem tailTrace_3598071 : CollatzResearch.WordTrace tailWord_3598071 prefixEnd_3598071 1231693234668998176243519 := by
  unfold tailWord_3598071
  simp only [CollatzResearch.WordTrace]
  refine ⟨131232430547810743448938067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87488287031873828965958711 131232430547810743448938067)
  ·
    refine ⟨196848645821716115173407101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131232430547810743448938067 196848645821716115173407101)
    ·
      refine ⟨73818242183143543190027663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196848645821716115173407101 73818242183143543190027663)
      ·
        refine ⟨110727363274715314785041495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73818242183143543190027663 110727363274715314785041495)
        ·
          refine ⟨166091044912072972177562243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110727363274715314785041495 166091044912072972177562243)
          ·
            refine ⟨249136567368109458266343365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166091044912072972177562243 249136567368109458266343365)
            ·
              refine ⟨46713106381520523424939381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249136567368109458266343365 46713106381520523424939381)
              ·
                refine ⟨4379353723267549071088067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46713106381520523424939381 4379353723267549071088067)
                ·
                  refine ⟨6569030584901323606632101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379353723267549071088067 6569030584901323606632101)
                  ·
                    refine ⟨1231693234668998176243519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569030584901323606632101 1231693234668998176243519)
                    ·
                      rfl

theorem cell22_3598071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3598071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598071 prefixEnd_3598071 := by exact prefixLift 3598071
  have htrace : WordTrace (prefixWord ++ tailWord_3598071) baseStart_3598071 baseEnd_3598071 := by
    simpa [prefixWord, tailWord_3598071, baseEnd_3598071] using wordTrace_append hprefix tailTrace_3598071
  have hstable : (prefixWord ++ tailWord_3598071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598071).length < 2 ^ (prefixWord ++ tailWord_3598071).sum := by decide
  have hdescent : baseEnd_3598071 < baseStart_3598071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598101 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3598101 : Nat := 118140960795 + 3598101 * 2 ^ 59
def prefixEnd_3598101 : Nat := 4983230072969 + 3 ^ 40 * 3598101 * 2
def baseEnd_3598101 : Nat := 1231703504282088097993427

theorem tailTrace_3598101 : CollatzResearch.WordTrace tailWord_3598101 prefixEnd_3598101 1231703504282088097993427 := by
  unfold tailWord_3598101
  simp only [CollatzResearch.WordTrace]
  refine ⟨131233524737702058572530157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87489016491801372381686771 131233524737702058572530157)
  ·
    refine ⟨49212571776638271964698809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131233524737702058572530157 49212571776638271964698809)
    ·
      refine ⟨36909428832478703973524107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49212571776638271964698809 36909428832478703973524107)
      ·
        refine ⟨55364143248718055960286161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36909428832478703973524107 55364143248718055960286161)
        ·
          refine ⟨41523107436538541970214621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55364143248718055960286161 41523107436538541970214621)
          ·
            refine ⟨15571165288701953238830483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41523107436538541970214621 15571165288701953238830483)
            ·
              refine ⟨23356747933052929858245725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571165288701953238830483 23356747933052929858245725)
              ·
                refine ⟨8758780474894848696842147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23356747933052929858245725 8758780474894848696842147)
                ·
                  refine ⟨13138170712342273045263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8758780474894848696842147 13138170712342273045263221)
                  ·
                    refine ⟨1231703504282088097993427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138170712342273045263221 1231703504282088097993427)
                    ·
                      rfl

theorem cell22_3598101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3598101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598101 prefixEnd_3598101 := by exact prefixLift 3598101
  have htrace : WordTrace (prefixWord ++ tailWord_3598101) baseStart_3598101 baseEnd_3598101 := by
    simpa [prefixWord, tailWord_3598101, baseEnd_3598101] using wordTrace_append hprefix tailTrace_3598101
  have hstable : (prefixWord ++ tailWord_3598101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598101).length < 2 ^ (prefixWord ++ tailWord_3598101).sum := by decide
  have hdescent : baseEnd_3598101 < baseStart_3598101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598120 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_3598120 : Nat := 118140960795 + 3598120 * 2 ^ 59
def prefixEnd_3598120 : Nat := 4983230072969 + 3 ^ 40 * 3598120 * 2
def baseEnd_3598120 : Nat := 410570002790126127256123

theorem tailTrace_3598120 : CollatzResearch.WordTrace tailWord_3598120 prefixEnd_3598120 410570002790126127256123 := by
  unfold tailWord_3598120
  simp only [CollatzResearch.WordTrace]
  refine ⟨65617108862316612408735907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87489478483088816544981209 65617108862316612408735907)
  ·
    refine ⟨98425663293474918613103861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65617108862316612408735907 98425663293474918613103861)
    ·
      refine ⟨9227405933763273619978487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98425663293474918613103861 9227405933763273619978487)
      ·
        refine ⟨13841108900644910429967731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227405933763273619978487 13841108900644910429967731)
        ·
          refine ⟨20761663350967365644951597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841108900644910429967731 20761663350967365644951597)
          ·
            refine ⟨7785623756612762116856849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20761663350967365644951597 7785623756612762116856849)
            ·
              refine ⟨5839217817459571587642637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785623756612762116856849 5839217817459571587642637)
              ·
                refine ⟨2189706681547339345365989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5839217817459571587642637 2189706681547339345365989)
                ·
                  refine ⟨410570002790126127256123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189706681547339345365989 410570002790126127256123)
                  ·
                    rfl

theorem cell22_3598120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_3598120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598120 prefixEnd_3598120 := by exact prefixLift 3598120
  have htrace : WordTrace (prefixWord ++ tailWord_3598120) baseStart_3598120 baseEnd_3598120 := by
    simpa [prefixWord, tailWord_3598120, baseEnd_3598120] using wordTrace_append hprefix tailTrace_3598120
  have hstable : (prefixWord ++ tailWord_3598120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598120).length < 2 ^ (prefixWord ++ tailWord_3598120).sum := by decide
  have hdescent : baseEnd_3598120 < baseStart_3598120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598131 : List Nat := [1, 1, 1, 2, 7, 1, 9]
def baseStart_3598131 : Nat := 118140960795 + 3598131 * 2 ^ 59
def prefixEnd_3598131 : Nat := 4983230072969 + 3 ^ 40 * 3598131 * 2
def baseEnd_3598131 : Nat := 45619028662784371101605

theorem tailTrace_3598131 : CollatzResearch.WordTrace tailWord_3598131 prefixEnd_3598131 45619028662784371101605 := by
  unfold tailWord_3598131
  simp only [CollatzResearch.WordTrace]
  refine ⟨131234618927593373696122247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87489745951728915797414831 131234618927593373696122247)
  ·
    refine ⟨196851928391390060544183371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131234618927593373696122247 196851928391390060544183371)
    ·
      refine ⟨295277892587085090816275057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196851928391390060544183371 295277892587085090816275057)
      ·
        refine ⟨221458419440313818112206293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295277892587085090816275057 221458419440313818112206293)
        ·
          refine ⟨5190431705632355112004835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 221458419440313818112206293 5190431705632355112004835)
          ·
            refine ⟨7785647558448532668007253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190431705632355112004835 7785647558448532668007253)
            ·
              refine ⟨45619028662784371101605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7785647558448532668007253 45619028662784371101605)
              ·
                rfl

theorem cell22_3598131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 9].length) (baseStart_3598131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598131 prefixEnd_3598131 := by exact prefixLift 3598131
  have htrace : WordTrace (prefixWord ++ tailWord_3598131) baseStart_3598131 baseEnd_3598131 := by
    simpa [prefixWord, tailWord_3598131, baseEnd_3598131] using wordTrace_append hprefix tailTrace_3598131
  have hstable : (prefixWord ++ tailWord_3598131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598131).length < 2 ^ (prefixWord ++ tailWord_3598131).sum := by decide
  have hdescent : baseEnd_3598131 < baseStart_3598131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598150 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3598150 : Nat := 118140960795 + 3598150 * 2 ^ 59
def prefixEnd_3598150 : Nat := 4983230072969 + 3 ^ 40 * 3598150 * 2
def baseEnd_3598150 : Nat := 1231720277983468303518277

theorem tailTrace_3598150 : CollatzResearch.WordTrace tailWord_3598150 prefixEnd_3598150 1231720277983468303518277 := by
  unfold tailWord_3598150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101103497328891873158247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87490207943016359960709269 4101103497328891873158247)
  ·
    refine ⟨6151655245993337809737371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101103497328891873158247 6151655245993337809737371)
    ·
      refine ⟨9227482868990006714606057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151655245993337809737371 9227482868990006714606057)
      ·
        refine ⟨6920612151742505035954543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227482868990006714606057 6920612151742505035954543)
        ·
          refine ⟨10380918227613757553931815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920612151742505035954543 10380918227613757553931815)
          ·
            refine ⟨15571377341420636330897723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380918227613757553931815 15571377341420636330897723)
            ·
              refine ⟨23357066012130954496346585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571377341420636330897723 23357066012130954496346585)
              ·
                refine ⟨17517799509098215872259939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23357066012130954496346585 17517799509098215872259939)
                ·
                  refine ⟨26276699263647323808389909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17517799509098215872259939 26276699263647323808389909)
                  ·
                    refine ⟨1231720277983468303518277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26276699263647323808389909 1231720277983468303518277)
                    ·
                      rfl

theorem cell22_3598150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3598150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598150 prefixEnd_3598150 := by exact prefixLift 3598150
  have htrace : WordTrace (prefixWord ++ tailWord_3598150) baseStart_3598150 baseEnd_3598150 := by
    simpa [prefixWord, tailWord_3598150, baseEnd_3598150] using wordTrace_append hprefix tailTrace_3598150
  have hstable : (prefixWord ++ tailWord_3598150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598150).length < 2 ^ (prefixWord ++ tailWord_3598150).sum := by decide
  have hdescent : baseEnd_3598150 < baseStart_3598150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598176 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_3598176 : Nat := 118140960795 + 3598176 * 2 ^ 59
def prefixEnd_3598176 : Nat := 4983230072969 + 3 ^ 40 * 3598176 * 2
def baseEnd_3598176 : Nat := 410576392771604300789399

theorem tailTrace_3598176 : CollatzResearch.WordTrace tailWord_3598176 prefixEnd_3598176 410576392771604300789399 := by
  unfold tailWord_3598176
  simp only [CollatzResearch.WordTrace]
  refine ⟨65618130106215173190755191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87490840141620230921006921 65618130106215173190755191)
  ·
    refine ⟨98427195159322759786132787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65618130106215173190755191 98427195159322759786132787)
    ·
      refine ⟨147640792738984139679199181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98427195159322759786132787 147640792738984139679199181)
      ·
        refine ⟨55365297277119052379699693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147640792738984139679199181 55365297277119052379699693)
        ·
          refine ⟨20761986478919644642387385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55365297277119052379699693 20761986478919644642387385)
          ·
            refine ⟨15571489859189733481790539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20761986478919644642387385 15571489859189733481790539)
            ·
              refine ⟨23357234788784600222685809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571489859189733481790539 23357234788784600222685809)
              ·
                refine ⟨17517926091588450167014357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23357234788784600222685809 17517926091588450167014357)
                ·
                  refine ⟨410576392771604300789399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17517926091588450167014357 410576392771604300789399)
                  ·
                    rfl

theorem cell22_3598176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_3598176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598176 prefixEnd_3598176 := by exact prefixLift 3598176
  have htrace : WordTrace (prefixWord ++ tailWord_3598176) baseStart_3598176 baseEnd_3598176 := by
    simpa [prefixWord, tailWord_3598176, baseEnd_3598176] using wordTrace_append hprefix tailTrace_3598176
  have hstable : (prefixWord ++ tailWord_3598176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598176).length < 2 ^ (prefixWord ++ tailWord_3598176).sum := by decide
  have hdescent : baseEnd_3598176 < baseStart_3598176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598248 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3598248 : Nat := 118140960795 + 3598248 * 2 ^ 59
def prefixEnd_3598248 : Nat := 4983230072969 + 3 ^ 40 * 3598248 * 2
def baseEnd_3598248 : Nat := 1231753825386228714567977

theorem tailTrace_3598248 : CollatzResearch.WordTrace tailWord_3598248 prefixEnd_3598248 1231753825386228714567977 := by
  unfold tailWord_3598248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65619443134084751339065699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87492590845446335118754265 65619443134084751339065699)
  ·
    refine ⟨98429164701127127008598549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65619443134084751339065699 98429164701127127008598549)
    ·
      refine ⟨4613867095365334078528057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98429164701127127008598549 4613867095365334078528057)
      ·
        refine ⟨3460400321524000558896043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4613867095365334078528057 3460400321524000558896043)
        ·
          refine ⟨5190600482286000838344065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460400321524000558896043 5190600482286000838344065)
          ·
            refine ⟨3892950361714500628758049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190600482286000838344065 3892950361714500628758049)
            ·
              refine ⟨2919712771285875471568537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892950361714500628758049 2919712771285875471568537)
              ·
                refine ⟨2189784578464406603676403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919712771285875471568537 2189784578464406603676403)
                ·
                  refine ⟨3284676867696609905514605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189784578464406603676403 3284676867696609905514605)
                  ·
                    refine ⟨1231753825386228714567977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3284676867696609905514605 1231753825386228714567977)
                    ·
                      rfl

theorem cell22_3598248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3598248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598248 prefixEnd_3598248 := by exact prefixLift 3598248
  have htrace : WordTrace (prefixWord ++ tailWord_3598248) baseStart_3598248 baseEnd_3598248 := by
    simpa [prefixWord, tailWord_3598248, baseEnd_3598248] using wordTrace_append hprefix tailTrace_3598248
  have hstable : (prefixWord ++ tailWord_3598248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598248).length < 2 ^ (prefixWord ++ tailWord_3598248).sum := by decide
  have hdescent : baseEnd_3598248 < baseStart_3598248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598266 : List Nat := [3, 1, 1, 1, 2, 1, 2, 11]
def baseStart_3598266 : Nat := 118140960795 + 3598266 * 2 ^ 59
def prefixEnd_3598266 : Nat := 4983230072969 + 3 ^ 40 * 3598266 * 2
def baseEnd_3598266 : Nat := 136862220794898074179769

theorem tailTrace_3598266 : CollatzResearch.WordTrace tailWord_3598266 prefixEnd_3598266 136862220794898074179769 := by
  unfold tailWord_3598266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809885695526072938071663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87493028521402861168191101 32809885695526072938071663)
  ·
    refine ⟨49214828543289109407107495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809885695526072938071663 49214828543289109407107495)
    ·
      refine ⟨73822242814933664110661243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214828543289109407107495 73822242814933664110661243)
      ·
        refine ⟨110733364222400496165991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73822242814933664110661243 110733364222400496165991865)
        ·
          refine ⟨83050023166800372124493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110733364222400496165991865 83050023166800372124493899)
          ·
            refine ⟨124575034750200558186740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83050023166800372124493899 124575034750200558186740849)
            ·
              refine ⟨93431276062650418640055637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124575034750200558186740849 93431276062650418640055637)
              ·
                refine ⟨136862220794898074179769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93431276062650418640055637 136862220794898074179769)
                ·
                  rfl

theorem cell22_3598266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_3598266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598266 prefixEnd_3598266 := by exact prefixLift 3598266
  have htrace : WordTrace (prefixWord ++ tailWord_3598266) baseStart_3598266 baseEnd_3598266 := by
    simpa [prefixWord, tailWord_3598266, baseEnd_3598266] using wordTrace_append hprefix tailTrace_3598266
  have hstable : (prefixWord ++ tailWord_3598266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598266).length < 2 ^ (prefixWord ++ tailWord_3598266).sum := by decide
  have hdescent : baseEnd_3598266 < baseStart_3598266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598270 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3598270 : Nat := 118140960795 + 3598270 * 2 ^ 59
def prefixEnd_3598270 : Nat := 4983230072969 + 3 ^ 40 * 3598270 * 2
def baseEnd_3598270 : Nat := 1231761356435827990517909

theorem tailTrace_3598270 : CollatzResearch.WordTrace tailWord_3598270 prefixEnd_3598270 1231761356435827990517909 := by
  unfold tailWord_3598270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404961084261225054429033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87493125782726533623621509 16404961084261225054429033)
  ·
    refine ⟨12303720813195918790821775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16404961084261225054429033 12303720813195918790821775)
    ·
      refine ⟨18455581219793878186232663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303720813195918790821775 18455581219793878186232663)
      ·
        refine ⟨27683371829690817279348995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455581219793878186232663 27683371829690817279348995)
        ·
          refine ⟨41525057744536225919023493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27683371829690817279348995 41525057744536225919023493)
          ·
            refine ⟨7785948327100542359816905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41525057744536225919023493 7785948327100542359816905)
            ·
              refine ⟨5839461245325406769862679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785948327100542359816905 5839461245325406769862679)
              ·
                refine ⟨8759191867988110154794019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839461245325406769862679 8759191867988110154794019)
                ·
                  refine ⟨13138787801982165232191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759191867988110154794019 13138787801982165232191029)
                  ·
                    refine ⟨1231761356435827990517909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138787801982165232191029 1231761356435827990517909)
                    ·
                      rfl

theorem cell22_3598270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3598270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598270 prefixEnd_3598270 := by exact prefixLift 3598270
  have htrace : WordTrace (prefixWord ++ tailWord_3598270) baseStart_3598270 baseEnd_3598270 := by
    simpa [prefixWord, tailWord_3598270, baseEnd_3598270] using wordTrace_append hprefix tailTrace_3598270
  have hstable : (prefixWord ++ tailWord_3598270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598270).length < 2 ^ (prefixWord ++ tailWord_3598270).sum := by decide
  have hdescent : baseEnd_3598270 < baseStart_3598270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598281 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_3598281 : Nat := 118140960795 + 3598281 * 2 ^ 59
def prefixEnd_3598281 : Nat := 4983230072969 + 3 ^ 40 * 3598281 * 2
def baseEnd_3598281 : Nat := 1231765121960627628492875

theorem tailTrace_3598281 : CollatzResearch.WordTrace tailWord_3598281 prefixEnd_3598281 1231765121960627628492875 := by
  unfold tailWord_3598281
  simp only [CollatzResearch.WordTrace]
  refine ⟨131240089877049949314082697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87493393251366632876055131 131240089877049949314082697)
  ·
    refine ⟨98430067407787461985562023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131240089877049949314082697 98430067407787461985562023)
    ·
      refine ⟨147645101111681192978343035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98430067407787461985562023 147645101111681192978343035)
      ·
        refine ⟨221467651667521789467514553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147645101111681192978343035 221467651667521789467514553)
        ·
          refine ⟨166100738750641342100635915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221467651667521789467514553 166100738750641342100635915)
          ·
            refine ⟨249151108125962013150953873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166100738750641342100635915 249151108125962013150953873)
            ·
              refine ⟨186863331094471509863215405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249151108125962013150953873 186863331094471509863215405)
              ·
                refine ⟨70073749160426816198705777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186863331094471509863215405 70073749160426816198705777)
                ·
                  refine ⟨52555311870320112149029333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70073749160426816198705777 52555311870320112149029333)
                  ·
                    refine ⟨1231765121960627628492875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52555311870320112149029333 1231765121960627628492875)
                    ·
                      rfl

theorem cell22_3598281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_3598281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598281 prefixEnd_3598281 := by exact prefixLift 3598281
  have htrace : WordTrace (prefixWord ++ tailWord_3598281) baseStart_3598281 baseEnd_3598281 := by
    simpa [prefixWord, tailWord_3598281, baseEnd_3598281] using wordTrace_append hprefix tailTrace_3598281
  have hstable : (prefixWord ++ tailWord_3598281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598281).length < 2 ^ (prefixWord ++ tailWord_3598281).sum := by decide
  have hdescent : baseEnd_3598281 < baseStart_3598281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598283 : List Nat := [1, 1, 1, 1, 3, 4, 5, 6]
def baseStart_3598283 : Nat := 118140960795 + 3598283 * 2 ^ 59
def prefixEnd_3598283 : Nat := 4983230072969 + 3 ^ 40 * 3598283 * 2
def baseEnd_3598283 : Nat := 136862867400166698882541

theorem tailTrace_3598283 : CollatzResearch.WordTrace tailWord_3598283 prefixEnd_3598283 136862867400166698882541 := by
  unfold tailWord_3598283
  simp only [CollatzResearch.WordTrace]
  refine ⟨131240162823042703655655503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87493441882028469103770335 131240162823042703655655503)
  ·
    refine ⟨196860244234564055483483255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131240162823042703655655503 196860244234564055483483255)
    ·
      refine ⟨295290366351846083225224883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196860244234564055483483255 295290366351846083225224883)
      ·
        refine ⟨442935549527769124837837325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295290366351846083225224883 442935549527769124837837325)
        ·
          refine ⟨166100831072913421814188997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442935549527769124837837325 166100831072913421814188997)
          ·
            refine ⟨31143905826171266590160437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166100831072913421814188997 31143905826171266590160437)
            ·
              refine ⟨2919741171203556242827541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31143905826171266590160437 2919741171203556242827541)
              ·
                refine ⟨136862867400166698882541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2919741171203556242827541 136862867400166698882541)
                ·
                  rfl

theorem cell22_3598283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 6].length) (baseStart_3598283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598283 prefixEnd_3598283 := by exact prefixLift 3598283
  have htrace : WordTrace (prefixWord ++ tailWord_3598283) baseStart_3598283 baseEnd_3598283 := by
    simpa [prefixWord, tailWord_3598283, baseEnd_3598283] using wordTrace_append hprefix tailTrace_3598283
  have hstable : (prefixWord ++ tailWord_3598283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598283).length < 2 ^ (prefixWord ++ tailWord_3598283).sum := by decide
  have hdescent : baseEnd_3598283 < baseStart_3598283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598328 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_3598328 : Nat := 118140960795 + 3598328 * 2 ^ 59
def prefixEnd_3598328 : Nat := 4983230072969 + 3 ^ 40 * 3598328 * 2
def baseEnd_3598328 : Nat := 410593737007045057522577

theorem tailTrace_3598328 : CollatzResearch.WordTrace tailWord_3598328 prefixEnd_3598328 410593737007045057522577 := by
  unfold tailWord_3598328
  simp only [CollatzResearch.WordTrace]
  refine ⟨65620902053939838170521819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87494536071919784227362425 65620902053939838170521819)
  ·
    refine ⟨98431353080909757255782729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65620902053939838170521819 98431353080909757255782729)
    ·
      refine ⟨73823514810682317941837047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98431353080909757255782729 73823514810682317941837047)
      ·
        refine ⟨110735272216023476912755571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73823514810682317941837047 110735272216023476912755571)
        ·
          refine ⟨166102908324035215369133357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110735272216023476912755571 166102908324035215369133357)
          ·
            refine ⟨62288590621513205763425009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166102908324035215369133357 62288590621513205763425009)
            ·
              refine ⟨46716442966134904322568757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62288590621513205763425009 46716442966134904322568757)
              ·
                refine ⟨4379666528075147280240821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46716442966134904322568757 4379666528075147280240821)
                ·
                  refine ⟨410593737007045057522577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4379666528075147280240821 410593737007045057522577)
                  ·
                    rfl

theorem cell22_3598328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_3598328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598328 prefixEnd_3598328 := by exact prefixLift 3598328
  have htrace : WordTrace (prefixWord ++ tailWord_3598328) baseStart_3598328 baseEnd_3598328 := by
    simpa [prefixWord, tailWord_3598328, baseEnd_3598328] using wordTrace_append hprefix tailTrace_3598328
  have hstable : (prefixWord ++ tailWord_3598328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598328).length < 2 ^ (prefixWord ++ tailWord_3598328).sum := by decide
  have hdescent : baseEnd_3598328 < baseStart_3598328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598390 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3598390 : Nat := 118140960795 + 3598390 * 2 ^ 59
def prefixEnd_3598390 : Nat := 4983230072969 + 3 ^ 40 * 3598390 * 2
def baseEnd_3598390 : Nat := 410600811629395892505847

theorem tailTrace_3598390 : CollatzResearch.WordTrace tailWord_3598390 prefixEnd_3598390 410600811629395892505847 := by
  unfold tailWord_3598390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202754089603441308112539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87496043622436707286533749 8202754089603441308112539)
  ·
    refine ⟨12304131134405161962168809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202754089603441308112539 12304131134405161962168809)
    ·
      refine ⟨9228098350803871471626607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12304131134405161962168809 9228098350803871471626607)
      ·
        refine ⟨13842147526205807207439911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9228098350803871471626607 13842147526205807207439911)
        ·
          refine ⟨20763221289308710811159867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13842147526205807207439911 20763221289308710811159867)
          ·
            refine ⟨31144831933963066216739801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20763221289308710811159867 31144831933963066216739801)
            ·
              refine ⟨23358623950472299662554851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31144831933963066216739801 23358623950472299662554851)
              ·
                refine ⟨35037935925708449493832277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23358623950472299662554851 35037935925708449493832277)
                ·
                  refine ⟨410600811629395892505847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35037935925708449493832277 410600811629395892505847)
                  ·
                    rfl

theorem cell22_3598390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3598390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598390 prefixEnd_3598390 := by exact prefixLift 3598390
  have htrace : WordTrace (prefixWord ++ tailWord_3598390) baseStart_3598390 baseEnd_3598390 := by
    simpa [prefixWord, tailWord_3598390, baseEnd_3598390] using wordTrace_append hprefix tailTrace_3598390
  have hstable : (prefixWord ++ tailWord_3598390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598390).length < 2 ^ (prefixWord ++ tailWord_3598390).sum := by decide
  have hdescent : baseEnd_3598390 < baseStart_3598390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598418 : List Nat := [3, 2, 2, 1, 14]
def baseStart_3598418 : Nat := 118140960795 + 3598418 * 2 ^ 59
def prefixEnd_3598418 : Nat := 4983230072969 + 3 ^ 40 * 3598418 * 2
def baseEnd_3598418 : Nat := 5069185266915246657685

theorem tailTrace_3598418 : CollatzResearch.WordTrace tailWord_3598418 prefixEnd_3598418 5069185266915246657685 := by
  unfold tailWord_3598418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32811271669388405427954977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87496724451702414474546605 32811271669388405427954977)
  ·
    refine ⟨24608453752041304070966233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32811271669388405427954977 24608453752041304070966233)
    ·
      refine ⟨18456340314030978053224675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24608453752041304070966233 18456340314030978053224675)
      ·
        refine ⟨27684510471046467079837013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18456340314030978053224675 27684510471046467079837013)
        ·
          refine ⟨5069185266915246657685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 27684510471046467079837013 5069185266915246657685)
          ·
            rfl

theorem cell22_3598418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 14].length) (baseStart_3598418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598418 prefixEnd_3598418 := by exact prefixLift 3598418
  have htrace : WordTrace (prefixWord ++ tailWord_3598418) baseStart_3598418 baseEnd_3598418 := by
    simpa [prefixWord, tailWord_3598418, baseEnd_3598418] using wordTrace_append hprefix tailTrace_3598418
  have hstable : (prefixWord ++ tailWord_3598418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598418).length < 2 ^ (prefixWord ++ tailWord_3598418).sum := by decide
  have hdescent : baseEnd_3598418 < baseStart_3598418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598424 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_3598424 : Nat := 118140960795 + 3598424 * 2 ^ 59
def prefixEnd_3598424 : Nat := 4983230072969 + 3 ^ 40 * 3598424 * 2
def baseEnd_3598424 : Nat := 410604691261007640722479

theorem tailTrace_3598424 : CollatzResearch.WordTrace tailWord_3598424 prefixEnd_3598424 410604691261007640722479 := by
  unfold tailWord_3598424
  simp only [CollatzResearch.WordTrace]
  refine ⟨65622652757765942368269163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87496870343687923157692217 65622652757765942368269163)
  ·
    refine ⟨98433979136648913552403745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65622652757765942368269163 98433979136648913552403745)
    ·
      refine ⟨73825484352486685164302809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98433979136648913552403745 73825484352486685164302809)
      ·
        refine ⟨55369113264365013873227107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73825484352486685164302809 55369113264365013873227107)
        ·
          refine ⟨83053669896547520809840661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55369113264365013873227107 83053669896547520809840661)
          ·
            refine ⟨3893140776400665037961281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83053669896547520809840661 3893140776400665037961281)
            ·
              refine ⟨2919855582300498778470961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893140776400665037961281 2919855582300498778470961)
              ·
                refine ⟨2189891686725374083853221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919855582300498778470961 2189891686725374083853221)
                ·
                  refine ⟨410604691261007640722479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189891686725374083853221 410604691261007640722479)
                  ·
                    rfl

theorem cell22_3598424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_3598424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598424 prefixEnd_3598424 := by exact prefixLift 3598424
  have htrace : WordTrace (prefixWord ++ tailWord_3598424) baseStart_3598424 baseEnd_3598424 := by
    simpa [prefixWord, tailWord_3598424, baseEnd_3598424] using wordTrace_append hprefix tailTrace_3598424
  have hstable : (prefixWord ++ tailWord_3598424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598424).length < 2 ^ (prefixWord ++ tailWord_3598424).sum := by decide
  have hdescent : baseEnd_3598424 < baseStart_3598424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3598433 : Nat := 118140960795 + 3598433 * 2 ^ 59
def prefixEnd_3598433 : Nat := 4983230072969 + 3 ^ 40 * 3598433 * 2
def baseEnd_3598433 : Nat := 1231817154666949898692409

theorem tailTrace_3598433 : CollatzResearch.WordTrace tailWord_3598433 prefixEnd_3598433 1231817154666949898692409 := by
  unfold tailWord_3598433
  simp only [CollatzResearch.WordTrace]
  refine ⟨131245633772499279273615953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87497089181666186182410635 131245633772499279273615953)
  ·
    refine ⟨98434225329374459455211965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131245633772499279273615953 98434225329374459455211965)
    ·
      refine ⟨36912834498515422295704487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98434225329374459455211965 36912834498515422295704487)
      ·
        refine ⟨55369251747773133443556731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36912834498515422295704487 55369251747773133443556731)
        ·
          refine ⟨83053877621659700165335097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55369251747773133443556731 83053877621659700165335097)
          ·
            refine ⟨62290408216244775124001323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83053877621659700165335097 62290408216244775124001323)
            ·
              refine ⟨93435612324367162686001985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62290408216244775124001323 93435612324367162686001985)
              ·
                refine ⟨70076709243275372014501489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93435612324367162686001985 70076709243275372014501489)
                ·
                  refine ⟨52557531932456529010876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70076709243275372014501489 52557531932456529010876117)
                  ·
                    refine ⟨1231817154666949898692409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52557531932456529010876117 1231817154666949898692409)
                    ·
                      rfl

theorem cell22_3598433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3598433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598433 prefixEnd_3598433 := by exact prefixLift 3598433
  have htrace : WordTrace (prefixWord ++ tailWord_3598433) baseStart_3598433 baseEnd_3598433 := by
    simpa [prefixWord, tailWord_3598433, baseEnd_3598433] using wordTrace_append hprefix tailTrace_3598433
  have hstable : (prefixWord ++ tailWord_3598433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598433).length < 2 ^ (prefixWord ++ tailWord_3598433).sum := by decide
  have hdescent : baseEnd_3598433 < baseStart_3598433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598454 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3598454 : Nat := 118140960795 + 3598454 * 2 ^ 59
def prefixEnd_3598454 : Nat := 4983230072969 + 3 ^ 40 * 3598454 * 2
def baseEnd_3598454 : Nat := 1231824343396112843917345

theorem tailTrace_3598454 : CollatzResearch.WordTrace tailWord_3598454 prefixEnd_3598454 1231824343396112843917345 := by
  unfold tailWord_3598454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202899981588949991258151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87497599803615466573420277 8202899981588949991258151)
  ·
    refine ⟨12304349972383424986887227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202899981588949991258151 12304349972383424986887227)
    ·
      refine ⟨18456524958575137480330841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12304349972383424986887227 18456524958575137480330841)
      ·
        refine ⟨13842393718931353110248131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18456524958575137480330841 13842393718931353110248131)
        ·
          refine ⟨20763590578397029665372197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13842393718931353110248131 20763590578397029665372197)
          ·
            refine ⟨3893173233449443062257287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20763590578397029665372197 3893173233449443062257287)
            ·
              refine ⟨5839759850174164593385931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893173233449443062257287 5839759850174164593385931)
              ·
                refine ⟨8759639775261246890078897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839759850174164593385931 8759639775261246890078897)
                ·
                  refine ⟨6569729831445935167559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8759639775261246890078897 6569729831445935167559173)
                  ·
                    refine ⟨1231824343396112843917345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569729831445935167559173 1231824343396112843917345)
                    ·
                      rfl

theorem cell22_3598454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3598454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598454 prefixEnd_3598454 := by exact prefixLift 3598454
  have htrace : WordTrace (prefixWord ++ tailWord_3598454) baseStart_3598454 baseEnd_3598454 := by
    simpa [prefixWord, tailWord_3598454, baseEnd_3598454] using wordTrace_append hprefix tailTrace_3598454
  have hstable : (prefixWord ++ tailWord_3598454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598454).length < 2 ^ (prefixWord ++ tailWord_3598454).sum := by decide
  have hdescent : baseEnd_3598454 < baseStart_3598454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598542 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_3598542 : Nat := 118140960795 + 3598542 * 2 ^ 59
def prefixEnd_3598542 : Nat := 4983230072969 + 3 ^ 40 * 3598542 * 2
def baseEnd_3598542 : Nat := 410618155864836649239025

theorem tailTrace_3598542 : CollatzResearch.WordTrace tailWord_3598542 prefixEnd_3598542 410618155864836649239025 := by
  unfold tailWord_3598542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16406201166138048861166735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87499739552736260592889253 16406201166138048861166735)
  ·
    refine ⟨24609301749207073291750103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16406201166138048861166735 24609301749207073291750103)
    ·
      refine ⟨36913952623810609937625155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24609301749207073291750103 36913952623810609937625155)
      ·
        refine ⟨55370928935715914906437733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36913952623810609937625155 55370928935715914906437733)
        ·
          refine ⟨10382049175446734044957075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55370928935715914906437733 10382049175446734044957075)
          ·
            refine ⟨15573073763170101067435613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382049175446734044957075 15573073763170101067435613)
            ·
              refine ⟨5839902661188787900288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15573073763170101067435613 5839902661188787900288355)
              ·
                refine ⟨8759853991783181850432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839902661188787900288355 8759853991783181850432533)
                ·
                  refine ⟨410618155864836649239025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8759853991783181850432533 410618155864836649239025)
                  ·
                    rfl

theorem cell22_3598542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_3598542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598542 prefixEnd_3598542 := by exact prefixLift 3598542
  have htrace : WordTrace (prefixWord ++ tailWord_3598542) baseStart_3598542 baseEnd_3598542 := by
    simpa [prefixWord, tailWord_3598542, baseEnd_3598542] using wordTrace_append hprefix tailTrace_3598542
  have hstable : (prefixWord ++ tailWord_3598542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598542).length < 2 ^ (prefixWord ++ tailWord_3598542).sum := by decide
  have hdescent : baseEnd_3598542 < baseStart_3598542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598570 : List Nat := [3, 1, 3, 1, 1, 2, 1, 10]
def baseStart_3598570 : Nat := 118140960795 + 3598570 * 2 ^ 59
def prefixEnd_3598570 : Nat := 4983230072969 + 3 ^ 40 * 3598570 * 2
def baseEnd_3598570 : Nat := 136873783618525245335221

theorem tailTrace_3598570 : CollatzResearch.WordTrace tailWord_3598570 prefixEnd_3598570 136873783618525245335221 := by
  unfold tailWord_3598570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812657643250737917838291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87500420382001967780902109 32812657643250737917838291)
  ·
    refine ⟨49218986464876106876757437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32812657643250737917838291 49218986464876106876757437)
    ·
      refine ⟨18457119924328540078784039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49218986464876106876757437 18457119924328540078784039)
      ·
        refine ⟨27685679886492810118176059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18457119924328540078784039 27685679886492810118176059)
        ·
          refine ⟨41528519829739215177264089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27685679886492810118176059 41528519829739215177264089)
          ·
            refine ⟨31146389872304411382948067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41528519829739215177264089 31146389872304411382948067)
            ·
              refine ⟨46719584808456617074422101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31146389872304411382948067 46719584808456617074422101)
              ·
                refine ⟨136873783618525245335221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46719584808456617074422101 136873783618525245335221)
                ·
                  rfl

theorem cell22_3598570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_3598570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598570 prefixEnd_3598570 := by exact prefixLift 3598570
  have htrace : WordTrace (prefixWord ++ tailWord_3598570) baseStart_3598570 baseEnd_3598570 := by
    simpa [prefixWord, tailWord_3598570, baseEnd_3598570] using wordTrace_append hprefix tailTrace_3598570
  have hstable : (prefixWord ++ tailWord_3598570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598570).length < 2 ^ (prefixWord ++ tailWord_3598570).sum := by decide
  have hdescent : baseEnd_3598570 < baseStart_3598570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598572 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3598572 : Nat := 118140960795 + 3598572 * 2 ^ 59
def prefixEnd_3598572 : Nat := 4983230072969 + 3 ^ 40 * 3598572 * 2
def baseEnd_3598572 : Nat := 1231864737207599869466983

theorem tailTrace_3598572 : CollatzResearch.WordTrace tailWord_3598572 prefixEnd_3598572 1231864737207599869466983 := by
  unfold tailWord_3598572
  simp only [CollatzResearch.WordTrace]
  refine ⟨65625351759497853006462985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87500469012663804008617313 65625351759497853006462985)
  ·
    refine ⟨49219013819623389754847239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65625351759497853006462985 49219013819623389754847239)
    ·
      refine ⟨73828520729435084632270859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49219013819623389754847239 73828520729435084632270859)
      ·
        refine ⟨110742781094152626948406289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73828520729435084632270859 110742781094152626948406289)
        ·
          refine ⟨83057085820614470211304717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110742781094152626948406289 83057085820614470211304717)
          ·
            refine ⟨31146407182730426329239269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83057085820614470211304717 31146407182730426329239269)
            ·
              refine ⟨5839951346761954936732363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31146407182730426329239269 5839951346761954936732363)
              ·
                refine ⟨8759927020142932405098545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839951346761954936732363 8759927020142932405098545)
                ·
                  refine ⟨6569945265107199303823909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8759927020142932405098545 6569945265107199303823909)
                  ·
                    refine ⟨1231864737207599869466983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569945265107199303823909 1231864737207599869466983)
                    ·
                      rfl

theorem cell22_3598572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3598572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598572 prefixEnd_3598572 := by exact prefixLift 3598572
  have htrace : WordTrace (prefixWord ++ tailWord_3598572) baseStart_3598572 baseEnd_3598572 := by
    simpa [prefixWord, tailWord_3598572, baseEnd_3598572] using wordTrace_append hprefix tailTrace_3598572
  have hstable : (prefixWord ++ tailWord_3598572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598572).length < 2 ^ (prefixWord ++ tailWord_3598572).sum := by decide
  have hdescent : baseEnd_3598572 < baseStart_3598572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598649 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 5]
def baseStart_3598649 : Nat := 118140960795 + 3598649 * 2 ^ 59
def prefixEnd_3598649 : Nat := 4983230072969 + 3 ^ 40 * 3598649 * 2
def baseEnd_3598649 : Nat := 410630365293732445097249

theorem tailTrace_3598649 : CollatzResearch.WordTrace tailWord_3598649 prefixEnd_3598649 410630365293732445097249 := by
  unfold tailWord_3598649
  simp only [CollatzResearch.WordTrace]
  refine ⟨131253511939716748163479001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87502341293144498775652667 131253511939716748163479001)
  ·
    refine ⟨98440133954787561122609251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131253511939716748163479001 98440133954787561122609251)
    ·
      refine ⟨147660200932181341683913877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98440133954787561122609251 147660200932181341683913877)
      ·
        refine ⟨6921571918696000391433463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147660200932181341683913877 6921571918696000391433463)
        ·
          refine ⟨10382357878044000587150195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6921571918696000391433463 10382357878044000587150195)
          ·
            refine ⟨15573536817066000880725293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382357878044000587150195 15573536817066000880725293)
            ·
              refine ⟨5840076306399750330271985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15573536817066000880725293 5840076306399750330271985)
              ·
                refine ⟨4380057229799812747703989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840076306399750330271985 4380057229799812747703989)
                ·
                  refine ⟨410630365293732445097249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380057229799812747703989 410630365293732445097249)
                  ·
                    rfl

theorem cell22_3598649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_3598649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598649 prefixEnd_3598649 := by exact prefixLift 3598649
  have htrace : WordTrace (prefixWord ++ tailWord_3598649) baseStart_3598649 baseEnd_3598649 := by
    simpa [prefixWord, tailWord_3598649, baseEnd_3598649] using wordTrace_append hprefix tailTrace_3598649
  have hstable : (prefixWord ++ tailWord_3598649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598649).length < 2 ^ (prefixWord ++ tailWord_3598649).sum := by decide
  have hdescent : baseEnd_3598649 < baseStart_3598649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598679 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3598679 : Nat := 118140960795 + 3598679 * 2 ^ 59
def prefixEnd_3598679 : Nat := 4983230072969 + 3 ^ 40 * 3598679 * 2
def baseEnd_3598679 : Nat := 1231901365494287257041655

theorem tailTrace_3598679 : CollatzResearch.WordTrace tailWord_3598679 prefixEnd_3598679 1231901365494287257041655 := by
  unfold tailWord_3598679
  simp only [CollatzResearch.WordTrace]
  refine ⟨131254606129608063287071091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87503070753072042191380727 131254606129608063287071091)
  ·
    refine ⟨196881909194412094930606637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131254606129608063287071091 196881909194412094930606637)
    ·
      refine ⟨73830715947904535598977489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196881909194412094930606637 73830715947904535598977489)
      ·
        refine ⟨55373036960928401699233117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73830715947904535598977489 55373036960928401699233117)
        ·
          refine ⟨20764888860348150637212419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55373036960928401699233117 20764888860348150637212419)
          ·
            refine ⟨31147333290522225955818629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20764888860348150637212419 31147333290522225955818629)
            ·
              refine ⟨5840124991972917366715993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31147333290522225955818629 5840124991972917366715993)
              ·
                refine ⟨4380093743979688025036995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840124991972917366715993 4380093743979688025036995)
                ·
                  refine ⟨6570140615969532037555493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380093743979688025036995 6570140615969532037555493)
                  ·
                    refine ⟨1231901365494287257041655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570140615969532037555493 1231901365494287257041655)
                    ·
                      rfl

theorem cell22_3598679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3598679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598679 prefixEnd_3598679 := by exact prefixLift 3598679
  have htrace : WordTrace (prefixWord ++ tailWord_3598679) baseStart_3598679 baseEnd_3598679 := by
    simpa [prefixWord, tailWord_3598679, baseEnd_3598679] using wordTrace_append hprefix tailTrace_3598679
  have hstable : (prefixWord ++ tailWord_3598679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598679).length < 2 ^ (prefixWord ++ tailWord_3598679).sum := by decide
  have hdescent : baseEnd_3598679 < baseStart_3598679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598692 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3598692 : Nat := 118140960795 + 3598692 * 2 ^ 59
def prefixEnd_3598692 : Nat := 4983230072969 + 3 ^ 40 * 3598692 * 2
def baseEnd_3598692 : Nat := 1231905815659959556466615

theorem tailTrace_3598692 : CollatzResearch.WordTrace tailWord_3598692 prefixEnd_3598692 1231905815659959556466615 := by
  unfold tailWord_3598692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65627540139280483253647165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87503386852373977671529553 65627540139280483253647165)
  ·
    refine ⟨24610327552230181220117687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65627540139280483253647165 24610327552230181220117687)
    ·
      refine ⟨36915491328345271830176531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24610327552230181220117687 36915491328345271830176531)
      ·
        refine ⟨55373236992517907745264797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36915491328345271830176531 55373236992517907745264797)
        ·
          refine ⟨20764963872194215404474299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55373236992517907745264797 20764963872194215404474299)
          ·
            refine ⟨31147445808291323106711449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20764963872194215404474299 31147445808291323106711449)
            ·
              refine ⟨23360584356218492330033587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31147445808291323106711449 23360584356218492330033587)
              ·
                refine ⟨35040876534327738495050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23360584356218492330033587 35040876534327738495050381)
                ·
                  refine ⟨13140328700372901935643893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35040876534327738495050381 13140328700372901935643893)
                  ·
                    refine ⟨1231905815659959556466615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13140328700372901935643893 1231905815659959556466615)
                    ·
                      rfl

theorem cell22_3598692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3598692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598692 prefixEnd_3598692 := by exact prefixLift 3598692
  have htrace : WordTrace (prefixWord ++ tailWord_3598692) baseStart_3598692 baseEnd_3598692 := by
    simpa [prefixWord, tailWord_3598692, baseEnd_3598692] using wordTrace_append hprefix tailTrace_3598692
  have hstable : (prefixWord ++ tailWord_3598692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598692).length < 2 ^ (prefixWord ++ tailWord_3598692).sum := by decide
  have hdescent : baseEnd_3598692 < baseStart_3598692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598707 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_3598707 : Nat := 118140960795 + 3598707 * 2 ^ 59
def prefixEnd_3598707 : Nat := 4983230072969 + 3 ^ 40 * 3598707 * 2
def baseEnd_3598707 : Nat := 1231910950466504517341569

theorem tailTrace_3598707 : CollatzResearch.WordTrace tailWord_3598707 prefixEnd_3598707 1231910950466504517341569 := by
  unfold tailWord_3598707
  simp only [CollatzResearch.WordTrace]
  refine ⟨131255627373506624069090375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87503751582337749379393583 131255627373506624069090375)
  ·
    refine ⟨196883441060259936103635563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131255627373506624069090375 196883441060259936103635563)
    ·
      refine ⟨295325161590389904155453345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196883441060259936103635563 295325161590389904155453345)
      ·
        refine ⟨221493871192792428116590009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295325161590389904155453345 221493871192792428116590009)
        ·
          refine ⟨166120403394594321087442507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221493871192792428116590009 166120403394594321087442507)
          ·
            refine ⟨249180605091891481631163761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166120403394594321087442507 249180605091891481631163761)
            ·
              refine ⟨186885453818918611223372821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249180605091891481631163761 186885453818918611223372821)
              ·
                refine ⟨8760255647761809901095601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186885453818918611223372821 8760255647761809901095601)
                ·
                  refine ⟨6570191735821357425821701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760255647761809901095601 6570191735821357425821701)
                  ·
                    refine ⟨1231910950466504517341569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570191735821357425821701 1231910950466504517341569)
                    ·
                      rfl

theorem cell22_3598707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_3598707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598707 prefixEnd_3598707 := by exact prefixLift 3598707
  have htrace : WordTrace (prefixWord ++ tailWord_3598707) baseStart_3598707 baseEnd_3598707 := by
    simpa [prefixWord, tailWord_3598707, baseEnd_3598707] using wordTrace_append hprefix tailTrace_3598707
  have hstable : (prefixWord ++ tailWord_3598707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598707).length < 2 ^ (prefixWord ++ tailWord_3598707).sum := by decide
  have hdescent : baseEnd_3598707 < baseStart_3598707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598730 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3598730 : Nat := 118140960795 + 3598730 * 2 ^ 59
def prefixEnd_3598730 : Nat := 4983230072969 + 3 ^ 40 * 3598730 * 2
def baseEnd_3598730 : Nat := 1231918823836540124016499

theorem tailTrace_3598730 : CollatzResearch.WordTrace tailWord_3598730 prefixEnd_3598730 1231918823836540124016499 := by
  unfold tailWord_3598730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814116563105824749294411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87504310834948865998118429 32814116563105824749294411)
  ·
    refine ⟨49221174844658737123941617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32814116563105824749294411 49221174844658737123941617)
    ·
      refine ⟨36915881133494052842956213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49221174844658737123941617 36915881133494052842956213)
      ·
        refine ⟨3460863856265067454027145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36915881133494052842956213 3460863856265067454027145)
        ·
          refine ⟨2595647892198800590520359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460863856265067454027145 2595647892198800590520359)
          ·
            refine ⟨3893471838298200885780539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595647892198800590520359 3893471838298200885780539)
            ·
              refine ⟨5840207757447301328670809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893471838298200885780539 5840207757447301328670809)
              ·
                refine ⟨4380155818085475996503107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840207757447301328670809 4380155818085475996503107)
                ·
                  refine ⟨6570233727128213994754661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380155818085475996503107 6570233727128213994754661)
                  ·
                    refine ⟨1231918823836540124016499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570233727128213994754661 1231918823836540124016499)
                    ·
                      rfl

theorem cell22_3598730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3598730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598730 prefixEnd_3598730 := by exact prefixLift 3598730
  have htrace : WordTrace (prefixWord ++ tailWord_3598730) baseStart_3598730 baseEnd_3598730 := by
    simpa [prefixWord, tailWord_3598730, baseEnd_3598730] using wordTrace_append hprefix tailTrace_3598730
  have hstable : (prefixWord ++ tailWord_3598730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598730).length < 2 ^ (prefixWord ++ tailWord_3598730).sum := by decide
  have hdescent : baseEnd_3598730 < baseStart_3598730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598788 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3598788 : Nat := 118140960795 + 3598788 * 2 ^ 59
def prefixEnd_3598788 : Nat := 4983230072969 + 3 ^ 40 * 3598788 * 2
def baseEnd_3598788 : Nat := 1231938678421847306066321

theorem tailTrace_3598788 : CollatzResearch.WordTrace tailWord_3598788 prefixEnd_3598788 1231938678421847306066321 := by
  unfold tailWord_3598788
  simp only [CollatzResearch.WordTrace]
  refine ⟨65629290843106587451394509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87505721124142116601859345 65629290843106587451394509)
  ·
    refine ⟨24610984066164970294272941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65629290843106587451394509 24610984066164970294272941)
    ·
      refine ⟨9229119024811863860352353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24610984066164970294272941 9229119024811863860352353)
      ·
        refine ⟨6921839268608897895264265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9229119024811863860352353 6921839268608897895264265)
        ·
          refine ⟨5191379451456673421448199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6921839268608897895264265 5191379451456673421448199)
          ·
            refine ⟨7787069177185010132172299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191379451456673421448199 7787069177185010132172299)
            ·
              refine ⟨11680603765777515198258449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787069177185010132172299 11680603765777515198258449)
              ·
                refine ⟨8760452824333136398693837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680603765777515198258449 8760452824333136398693837)
                ·
                  refine ⟨3285169809124926149510189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8760452824333136398693837 3285169809124926149510189)
                  ·
                    refine ⟨1231938678421847306066321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285169809124926149510189 1231938678421847306066321)
                    ·
                      rfl

theorem cell22_3598788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3598788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598788 prefixEnd_3598788 := by exact prefixLift 3598788
  have htrace : WordTrace (prefixWord ++ tailWord_3598788) baseStart_3598788 baseEnd_3598788 := by
    simpa [prefixWord, tailWord_3598788, baseEnd_3598788] using wordTrace_append hprefix tailTrace_3598788
  have hstable : (prefixWord ++ tailWord_3598788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598788).length < 2 ^ (prefixWord ++ tailWord_3598788).sum := by decide
  have hdescent : baseEnd_3598788 < baseStart_3598788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598818 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3598818 : Nat := 118140960795 + 3598818 * 2 ^ 59
def prefixEnd_3598818 : Nat := 4983230072969 + 3 ^ 40 * 3598818 * 2
def baseEnd_3598818 : Nat := 410649649344979075938743

theorem tailTrace_3598818 : CollatzResearch.WordTrace tailWord_3598818 prefixEnd_3598818 410649649344979075938743 := by
  unfold tailWord_3598818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814918969026122506595277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87506450584069660017587405 32814918969026122506595277)
  ·
    refine ⟨12305594613384795939973229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32814918969026122506595277 12305594613384795939973229)
    ·
      refine ⟨4614597980019298477489961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12305594613384795939973229 4614597980019298477489961)
      ·
        refine ⟨3460948485014473858117471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4614597980019298477489961 3460948485014473858117471)
        ·
          refine ⟨5191422727521710787176207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460948485014473858117471 5191422727521710787176207)
          ·
            refine ⟨7787134091282566180764311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191422727521710787176207 7787134091282566180764311)
            ·
              refine ⟨11680701136923849271146467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787134091282566180764311 11680701136923849271146467)
              ·
                refine ⟨17521051705385773906719701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680701136923849271146467 17521051705385773906719701)
                ·
                  refine ⟨410649649344979075938743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17521051705385773906719701 410649649344979075938743)
                  ·
                    rfl

theorem cell22_3598818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3598818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598818 prefixEnd_3598818 := by exact prefixLift 3598818
  have htrace : WordTrace (prefixWord ++ tailWord_3598818) baseStart_3598818 baseEnd_3598818 := by
    simpa [prefixWord, tailWord_3598818, baseEnd_3598818] using wordTrace_append hprefix tailTrace_3598818
  have hstable : (prefixWord ++ tailWord_3598818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598818).length < 2 ^ (prefixWord ++ tailWord_3598818).sum := by decide
  have hdescent : baseEnd_3598818 < baseStart_3598818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598859 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_3598859 : Nat := 118140960795 + 3598859 * 2 ^ 59
def prefixEnd_3598859 : Nat := 4983230072969 + 3 ^ 40 * 3598859 * 2
def baseEnd_3598859 : Nat := 1231962983172826787541103

theorem tailTrace_3598859 : CollatzResearch.WordTrace tailWord_3598859 prefixEnd_3598859 1231962983172826787541103 := by
  unfold tailWord_3598859
  simp only [CollatzResearch.WordTrace]
  refine ⟨131261171268955954028623631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87507447512637302685749087 131261171268955954028623631)
  ·
    refine ⟨196891756903433931042935447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131261171268955954028623631 196891756903433931042935447)
    ·
      refine ⟨295337635355150896564403171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196891756903433931042935447 295337635355150896564403171)
      ·
        refine ⟨443006453032726344846604757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295337635355150896564403171 443006453032726344846604757)
        ·
          refine ⟨10382963742954523707342299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 443006453032726344846604757 10382963742954523707342299)
          ·
            refine ⟨15574445614431785561013449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382963742954523707342299 15574445614431785561013449)
            ·
              refine ⟨11680834210823839170760087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15574445614431785561013449 11680834210823839170760087)
              ·
                refine ⟨17521251316235758756140131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680834210823839170760087 17521251316235758756140131)
                ·
                  refine ⟨26281876974353638134210197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17521251316235758756140131 26281876974353638134210197)
                  ·
                    refine ⟨1231962983172826787541103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26281876974353638134210197 1231962983172826787541103)
                    ·
                      rfl

theorem cell22_3598859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_3598859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598859 prefixEnd_3598859 := by exact prefixLift 3598859
  have htrace : WordTrace (prefixWord ++ tailWord_3598859) baseStart_3598859 baseEnd_3598859 := by
    simpa [prefixWord, tailWord_3598859, baseEnd_3598859] using wordTrace_append hprefix tailTrace_3598859
  have hstable : (prefixWord ++ tailWord_3598859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598859).length < 2 ^ (prefixWord ++ tailWord_3598859).sum := by decide
  have hdescent : baseEnd_3598859 < baseStart_3598859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598876 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3598876 : Nat := 118140960795 + 3598876 * 2 ^ 59
def prefixEnd_3598876 : Nat := 4983230072969 + 3 ^ 40 * 3598876 * 2
def baseEnd_3598876 : Nat := 1231968802620244409866051

theorem tailTrace_3598876 : CollatzResearch.WordTrace tailWord_3598876 prefixEnd_3598876 1231968802620244409866051 := by
  unfold tailWord_3598876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65630895654947182965996241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87507860873262910621328321 65630895654947182965996241)
  ·
    refine ⟨49223171741210387224497181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65630895654947182965996241 49223171741210387224497181)
    ·
      refine ⟨18458689402953895209186443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49223171741210387224497181 18458689402953895209186443)
      ·
        refine ⟨27688034104430842813779665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18458689402953895209186443 27688034104430842813779665)
        ·
          refine ⟨20766025578323132110334749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27688034104430842813779665 20766025578323132110334749)
          ·
            refine ⟨7787259591871174541375531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20766025578323132110334749 7787259591871174541375531)
            ·
              refine ⟨11680889387806761812063297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787259591871174541375531 11680889387806761812063297)
              ·
                refine ⟨8760667040855071359047473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680889387806761812063297 8760667040855071359047473)
                ·
                  refine ⟨6570500280641303519285605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760667040855071359047473 6570500280641303519285605)
                  ·
                    refine ⟨1231968802620244409866051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570500280641303519285605 1231968802620244409866051)
                    ·
                      rfl

theorem cell22_3598876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3598876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598876 prefixEnd_3598876 := by exact prefixLift 3598876
  have htrace : WordTrace (prefixWord ++ tailWord_3598876) baseStart_3598876 baseEnd_3598876 := by
    simpa [prefixWord, tailWord_3598876, baseEnd_3598876] using wordTrace_append hprefix tailTrace_3598876
  have hstable : (prefixWord ++ tailWord_3598876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598876).length < 2 ^ (prefixWord ++ tailWord_3598876).sum := by decide
  have hdescent : baseEnd_3598876 < baseStart_3598876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598880 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_3598880 : Nat := 118140960795 + 3598880 * 2 ^ 59
def prefixEnd_3598880 : Nat := 4983230072969 + 3 ^ 40 * 3598880 * 2
def baseEnd_3598880 : Nat := 410656723967329910922013

theorem tailTrace_3598880 : CollatzResearch.WordTrace tailWord_3598880 prefixEnd_3598880 410656723967329910922013 := by
  unfold tailWord_3598880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65630968600939937307569047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87507958134586583076758729 65630968600939937307569047)
  ·
    refine ⟨98446452901409905961353571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65630968600939937307569047 98446452901409905961353571)
    ·
      refine ⟨147669679352114858942030357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98446452901409905961353571 147669679352114858942030357)
      ·
        refine ⟨6922016219630384012907673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147669679352114858942030357 6922016219630384012907673)
        ·
          refine ⟨5191512164722788009680755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6922016219630384012907673 5191512164722788009680755)
          ·
            refine ⟨7787268247084182014521133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191512164722788009680755 7787268247084182014521133)
            ·
              refine ⟨2920225592656568255445425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7787268247084182014521133 2920225592656568255445425)
              ·
                refine ⟨2190169194492426191584069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920225592656568255445425 2190169194492426191584069)
                ·
                  refine ⟨410656723967329910922013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190169194492426191584069 410656723967329910922013)
                  ·
                    rfl

theorem cell22_3598880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_3598880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598880 prefixEnd_3598880 := by exact prefixLift 3598880
  have htrace : WordTrace (prefixWord ++ tailWord_3598880) baseStart_3598880 baseEnd_3598880 := by
    simpa [prefixWord, tailWord_3598880, baseEnd_3598880] using wordTrace_append hprefix tailTrace_3598880
  have hstable : (prefixWord ++ tailWord_3598880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598880).length < 2 ^ (prefixWord ++ tailWord_3598880).sum := by decide
  have hdescent : baseEnd_3598880 < baseStart_3598880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598910 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3598910 : Nat := 118140960795 + 3598910 * 2 ^ 59
def prefixEnd_3598910 : Nat := 4983230072969 + 3 ^ 40 * 3598910 * 2
def baseEnd_3598910 : Nat := 1231980441515079654515947

theorem tailTrace_3598910 : CollatzResearch.WordTrace tailWord_3598910 prefixEnd_3598910 1231980441515079654515947 := by
  unfold tailWord_3598910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407878923971398717341273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87508687594514126492486789 16407878923971398717341273)
  ·
    refine ⟨12305909192978549038005955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16407878923971398717341273 12305909192978549038005955)
    ·
      refine ⟨18458863789467823557008933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12305909192978549038005955 18458863789467823557008933)
      ·
        refine ⟨3461036960525216916939175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18458863789467823557008933 3461036960525216916939175)
        ·
          refine ⟨5191555440787825375408763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461036960525216916939175 5191555440787825375408763)
          ·
            refine ⟨7787333161181738063113145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191555440787825375408763 7787333161181738063113145)
            ·
              refine ⟨5840499870886303547334859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7787333161181738063113145 5840499870886303547334859)
              ·
                refine ⟨8760749806329455321002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840499870886303547334859 8760749806329455321002289)
                ·
                  refine ⟨6570562354747091490751717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760749806329455321002289 6570562354747091490751717)
                  ·
                    refine ⟨1231980441515079654515947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570562354747091490751717 1231980441515079654515947)
                    ·
                      rfl

theorem cell22_3598910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3598910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598910 prefixEnd_3598910 := by exact prefixLift 3598910
  have htrace : WordTrace (prefixWord ++ tailWord_3598910) baseStart_3598910 baseEnd_3598910 := by
    simpa [prefixWord, tailWord_3598910, baseEnd_3598910] using wordTrace_append hprefix tailTrace_3598910
  have hstable : (prefixWord ++ tailWord_3598910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598910).length < 2 ^ (prefixWord ++ tailWord_3598910).sum := by decide
  have hdescent : baseEnd_3598910 < baseStart_3598910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3598942 : List Nat := [4, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3598942 : Nat := 118140960795 + 3598942 * 2 ^ 59
def prefixEnd_3598942 : Nat := 4983230072969 + 3 ^ 40 * 3598942 * 2
def baseEnd_3598942 : Nat := 136887932863226915301761

theorem tailTrace_3598942 : CollatzResearch.WordTrace tailWord_3598942 prefixEnd_3598942 136887932863226915301761 := by
  unfold tailWord_3598942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408024815956907400486885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87509465685103506135930053 16408024815956907400486885)
  ·
    refine ⟨3076504652991920137591291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16408024815956907400486885 3076504652991920137591291)
    ·
      refine ⟨4614756979487880206386937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076504652991920137591291 4614756979487880206386937)
      ·
        refine ⟨3461067734615910154790203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4614756979487880206386937 3461067734615910154790203)
        ·
          refine ⟨5191601601923865232185305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461067734615910154790203 5191601601923865232185305)
          ·
            refine ⟨3893701201442898924138979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5191601601923865232185305 3893701201442898924138979)
            ·
              refine ⟨5840551802164348386208469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893701201442898924138979 5840551802164348386208469)
              ·
                refine ⟨136887932863226915301761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5840551802164348386208469 136887932863226915301761)
                ·
                  rfl

theorem cell22_3598942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3598942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3598942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3598942 prefixEnd_3598942 := by exact prefixLift 3598942
  have htrace : WordTrace (prefixWord ++ tailWord_3598942) baseStart_3598942 baseEnd_3598942 := by
    simpa [prefixWord, tailWord_3598942, baseEnd_3598942] using wordTrace_append hprefix tailTrace_3598942
  have hstable : (prefixWord ++ tailWord_3598942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3598942).length < 2 ^ (prefixWord ++ tailWord_3598942).sum := by decide
  have hdescent : baseEnd_3598942 < baseStart_3598942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3598942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599024 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_3599024 : Nat := 118140960795 + 3599024 * 2 ^ 59
def prefixEnd_3599024 : Nat := 4983230072969 + 3 ^ 40 * 3599024 * 2
def baseEnd_3599024 : Nat := 1232019466044821357165597

theorem tailTrace_3599024 : CollatzResearch.WordTrace tailWord_3599024 prefixEnd_3599024 1232019466044821357165597 := by
  unfold tailWord_3599024
  simp only [CollatzResearch.WordTrace]
  refine ⟨65633594656679093604190063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87511459542238791472253417 65633594656679093604190063)
  ·
    refine ⟨98450391985018640406285095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65633594656679093604190063 98450391985018640406285095)
    ·
      refine ⟨147675587977527960609427643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98450391985018640406285095 147675587977527960609427643)
      ·
        refine ⟨221513381966291940914141465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147675587977527960609427643 221513381966291940914141465)
        ·
          refine ⟨166135036474718955685606099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221513381966291940914141465 166135036474718955685606099)
          ·
            refine ⟨249202554712078433528409149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166135036474718955685606099 249202554712078433528409149)
            ·
              refine ⟨93450958017029412573153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249202554712078433528409149 93450958017029412573153431)
              ·
                refine ⟨140176437025544118859730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93450958017029412573153431 140176437025544118859730147)
                ·
                  refine ⟨210264655538316178289595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140176437025544118859730147 210264655538316178289595221)
                  ·
                    refine ⟨1232019466044821357165597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210264655538316178289595221 1232019466044821357165597)
                    ·
                      rfl

theorem cell22_3599024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_3599024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599024 prefixEnd_3599024 := by exact prefixLift 3599024
  have htrace : WordTrace (prefixWord ++ tailWord_3599024) baseStart_3599024 baseEnd_3599024 := by
    simpa [prefixWord, tailWord_3599024, baseEnd_3599024] using wordTrace_append hprefix tailTrace_3599024
  have hstable : (prefixWord ++ tailWord_3599024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599024).length < 2 ^ (prefixWord ++ tailWord_3599024).sum := by decide
  have hdescent : baseEnd_3599024 < baseStart_3599024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599116 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3599116 : Nat := 118140960795 + 3599116 * 2 ^ 59
def prefixEnd_3599116 : Nat := 4983230072969 + 3 ^ 40 * 3599116 * 2
def baseEnd_3599116 : Nat := 410683653174987927955105

theorem tailTrace_3599116 : CollatzResearch.WordTrace tailWord_3599116 prefixEnd_3599116 410683653174987927955105 := by
  unfold tailWord_3599116
  simp only [CollatzResearch.WordTrace]
  refine ⟨65635272414512443460364601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87513696552683257947152801 65635272414512443460364601)
  ·
    refine ⟨49226454310884332595273451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65635272414512443460364601 49226454310884332595273451)
    ·
      refine ⟨73839681466326498892910177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49226454310884332595273451 73839681466326498892910177)
      ·
        refine ⟨55379761099744874169682633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73839681466326498892910177 55379761099744874169682633)
        ·
          refine ⟨41534820824808655627261975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55379761099744874169682633 41534820824808655627261975)
          ·
            refine ⟨62302231237212983440892963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41534820824808655627261975 62302231237212983440892963)
            ·
              refine ⟨93453346855819475161339445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62302231237212983440892963 93453346855819475161339445)
              ·
                refine ⟨8761251267733075796375573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93453346855819475161339445 8761251267733075796375573)
                ·
                  refine ⟨410683653174987927955105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8761251267733075796375573 410683653174987927955105)
                  ·
                    rfl

theorem cell22_3599116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3599116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599116 prefixEnd_3599116 := by exact prefixLift 3599116
  have htrace : WordTrace (prefixWord ++ tailWord_3599116) baseStart_3599116 baseEnd_3599116 := by
    simpa [prefixWord, tailWord_3599116, baseEnd_3599116] using wordTrace_append hprefix tailTrace_3599116
  have hstable : (prefixWord ++ tailWord_3599116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599116).length < 2 ^ (prefixWord ++ tailWord_3599116).sum := by decide
  have hdescent : baseEnd_3599116 < baseStart_3599116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599148 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_3599148 : Nat := 118140960795 + 3599148 * 2 ^ 59
def prefixEnd_3599148 : Nat := 4983230072969 + 3 ^ 40 * 3599148 * 2
def baseEnd_3599148 : Nat := 1232061913778926367065217

theorem tailTrace_3599148 : CollatzResearch.WordTrace tailWord_3599148 prefixEnd_3599148 1232061913778926367065217 := by
  unfold tailWord_3599148
  simp only [CollatzResearch.WordTrace]
  refine ⟨65635855982454478192947049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87514474643272637590596065 65635855982454478192947049)
  ·
    refine ⟨49226891986840858644710287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65635855982454478192947049 49226891986840858644710287)
    ·
      refine ⟨73840337980261287967065431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49226891986840858644710287 73840337980261287967065431)
      ·
        refine ⟨110760506970391931950598147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73840337980261287967065431 110760506970391931950598147)
        ·
          refine ⟨166140760455587897925897221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110760506970391931950598147 166140760455587897925897221)
          ·
            refine ⟨31151392585422730861105729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166140760455587897925897221 31151392585422730861105729)
            ·
              refine ⟨23363544439067048145829297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31151392585422730861105729 23363544439067048145829297)
              ·
                refine ⟨17522658329300286109371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23363544439067048145829297 17522658329300286109371973)
                ·
                  refine ⟨3285498436743803645507245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17522658329300286109371973 3285498436743803645507245)
                  ·
                    refine ⟨1232061913778926367065217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285498436743803645507245 1232061913778926367065217)
                    ·
                      rfl

theorem cell22_3599148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_3599148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599148 prefixEnd_3599148 := by exact prefixLift 3599148
  have htrace : WordTrace (prefixWord ++ tailWord_3599148) baseStart_3599148 baseEnd_3599148 := by
    simpa [prefixWord, tailWord_3599148, baseEnd_3599148] using wordTrace_append hprefix tailTrace_3599148
  have hstable : (prefixWord ++ tailWord_3599148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599148).length < 2 ^ (prefixWord ++ tailWord_3599148).sum := by decide
  have hdescent : baseEnd_3599148 < baseStart_3599148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599240 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_3599240 : Nat := 118140960795 + 3599240 * 2 ^ 59
def prefixEnd_3599240 : Nat := 4983230072969 + 3 ^ 40 * 3599240 * 2
def baseEnd_3599240 : Nat := 410697802419689597921645

theorem tailTrace_3599240 : CollatzResearch.WordTrace tailWord_3599240 prefixEnd_3599240 410697802419689597921645 := by
  unfold tailWord_3599240
  simp only [CollatzResearch.WordTrace]
  refine ⟨65637533740287828049121587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87516711653717104065495449 65637533740287828049121587)
  ·
    refine ⟨98456300610431742073682381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65637533740287828049121587 98456300610431742073682381)
    ·
      refine ⟨36921112728911903277630893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98456300610431742073682381 36921112728911903277630893)
      ·
        refine ⟨13845417273341963729111585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36921112728911903277630893 13845417273341963729111585)
        ·
          refine ⟨10384062955006472796833689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13845417273341963729111585 10384062955006472796833689)
          ·
            refine ⟨7788047216254854597625267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384062955006472796833689 7788047216254854597625267)
            ·
              refine ⟨11682070824382281896437901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788047216254854597625267 11682070824382281896437901)
              ·
                refine ⟨4380776559143355711164213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11682070824382281896437901 4380776559143355711164213)
                ·
                  refine ⟨410697802419689597921645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380776559143355711164213 410697802419689597921645)
                  ·
                    rfl

theorem cell22_3599240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_3599240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599240 prefixEnd_3599240 := by exact prefixLift 3599240
  have htrace : WordTrace (prefixWord ++ tailWord_3599240) baseStart_3599240 baseEnd_3599240 := by
    simpa [prefixWord, tailWord_3599240, baseEnd_3599240] using wordTrace_append hprefix tailTrace_3599240
  have hstable : (prefixWord ++ tailWord_3599240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599240).length < 2 ^ (prefixWord ++ tailWord_3599240).sum := by decide
  have hdescent : baseEnd_3599240 < baseStart_3599240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599450 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_3599450 : Nat := 118140960795 + 3599450 * 2 ^ 59
def prefixEnd_3599450 : Nat := 4983230072969 + 3 ^ 40 * 3599450 * 2
def baseEnd_3599450 : Nat := 1232165294550698246014291

theorem tailTrace_3599450 : CollatzResearch.WordTrace tailWord_3599450 prefixEnd_3599450 1232165294550698246014291 := by
  unfold tailWord_3599450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820681702453715490846951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87521817873209907975591869 32820681702453715490846951)
  ·
    refine ⟨49231022553680573236270427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32820681702453715490846951 49231022553680573236270427)
    ·
      refine ⟨73846533830520859854405641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49231022553680573236270427 73846533830520859854405641)
      ·
        refine ⟨55384900372890644890804231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73846533830520859854405641 55384900372890644890804231)
        ·
          refine ⟨83077350559335967336206347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55384900372890644890804231 83077350559335967336206347)
          ·
            refine ⟨124616025839003951004309521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83077350559335967336206347 124616025839003951004309521)
            ·
              refine ⟨93462019379252963253232141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124616025839003951004309521 93462019379252963253232141)
              ·
                refine ⟨35048257267219861219962053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93462019379252963253232141 35048257267219861219962053)
                ·
                  refine ⟨6571548237603723978742885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35048257267219861219962053 6571548237603723978742885)
                  ·
                    refine ⟨1232165294550698246014291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571548237603723978742885 1232165294550698246014291)
                    ·
                      rfl

theorem cell22_3599450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_3599450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599450 prefixEnd_3599450 := by exact prefixLift 3599450
  have htrace : WordTrace (prefixWord ++ tailWord_3599450) baseStart_3599450 baseEnd_3599450 := by
    simpa [prefixWord, tailWord_3599450, baseEnd_3599450] using wordTrace_append hprefix tailTrace_3599450
  have hstable : (prefixWord ++ tailWord_3599450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599450).length < 2 ^ (prefixWord ++ tailWord_3599450).sum := by decide
  have hdescent : baseEnd_3599450 < baseStart_3599450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599465 : List Nat := [1, 2, 1, 1, 1, 6, 3, 7]
def baseStart_3599465 : Nat := 118140960795 + 3599465 * 2 ^ 59
def prefixEnd_3599465 : Nat := 4983230072969 + 3 ^ 40 * 3599465 * 2
def baseEnd_3599465 : Nat := 136907825484138134098805

theorem tailTrace_3599465 : CollatzResearch.WordTrace tailWord_3599465 prefixEnd_3599465 136907825484138134098805 := by
  unfold tailWord_3599465
  simp only [CollatzResearch.WordTrace]
  refine ⟨131283273904760519525183849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87522182603173679683455899 131283273904760519525183849)
  ·
    refine ⟨98462455428570389643887887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131283273904760519525183849 98462455428570389643887887)
    ·
      refine ⟨147693683142855584465831831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98462455428570389643887887 147693683142855584465831831)
      ·
        refine ⟨221540524714283376698747747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147693683142855584465831831 221540524714283376698747747)
        ·
          refine ⟨332310787071425065048121621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221540524714283376698747747 332310787071425065048121621)
          ·
            refine ⟨15577068143973049924130701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332310787071425065048121621 15577068143973049924130701)
            ·
              refine ⟨5841400553989893721549013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15577068143973049924130701 5841400553989893721549013)
              ·
                refine ⟨136907825484138134098805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5841400553989893721549013 136907825484138134098805)
                ·
                  rfl

theorem cell22_3599465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 7].length) (baseStart_3599465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599465 prefixEnd_3599465 := by exact prefixLift 3599465
  have htrace : WordTrace (prefixWord ++ tailWord_3599465) baseStart_3599465 baseEnd_3599465 := by
    simpa [prefixWord, tailWord_3599465, baseEnd_3599465] using wordTrace_append hprefix tailTrace_3599465
  have hstable : (prefixWord ++ tailWord_3599465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599465).length < 2 ^ (prefixWord ++ tailWord_3599465).sum := by decide
  have hdescent : baseEnd_3599465 < baseStart_3599465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599469 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3599469 : Nat := 118140960795 + 3599469 * 2 ^ 59
def prefixEnd_3599469 : Nat := 4983230072969 + 3 ^ 40 * 3599469 * 2
def baseEnd_3599469 : Nat := 1232171798638988529789233

theorem tailTrace_3599469 : CollatzResearch.WordTrace tailWord_3599469 prefixEnd_3599469 1232171798638988529789233 := by
  unfold tailWord_3599469
  simp only [CollatzResearch.WordTrace]
  refine ⟨131283419796746028208329461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87522279864497352138886307 131283419796746028208329461)
  ·
    refine ⟨12307820605944940144530887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131283419796746028208329461 12307820605944940144530887)
    ·
      refine ⟨18461730908917410216796331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307820605944940144530887 18461730908917410216796331)
      ·
        refine ⟨27692596363376115325194497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18461730908917410216796331 27692596363376115325194497)
        ·
          refine ⟨20769447272532086493895873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27692596363376115325194497 20769447272532086493895873)
          ·
            refine ⟨15577085454399064870421905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20769447272532086493895873 15577085454399064870421905)
            ·
              refine ⟨11682814090799298652816429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15577085454399064870421905 11682814090799298652816429)
              ·
                refine ⟨4381055284049736994806161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11682814090799298652816429 4381055284049736994806161)
                ·
                  refine ⟨3285791463037302746104621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381055284049736994806161 3285791463037302746104621)
                  ·
                    refine ⟨1232171798638988529789233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285791463037302746104621 1232171798638988529789233)
                    ·
                      rfl

theorem cell22_3599469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3599469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599469 prefixEnd_3599469 := by exact prefixLift 3599469
  have htrace : WordTrace (prefixWord ++ tailWord_3599469) baseStart_3599469 baseEnd_3599469 := by
    simpa [prefixWord, tailWord_3599469, baseEnd_3599469] using wordTrace_append hprefix tailTrace_3599469
  have hstable : (prefixWord ++ tailWord_3599469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599469).length < 2 ^ (prefixWord ++ tailWord_3599469).sum := by decide
  have hdescent : baseEnd_3599469 < baseStart_3599469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599514 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_3599514 : Nat := 118140960795 + 3599514 * 2 ^ 59
def prefixEnd_3599514 : Nat := 4983230072969 + 3 ^ 40 * 3599514 * 2
def baseEnd_3599514 : Nat := 1232187203058623412414095

theorem tailTrace_3599514 : CollatzResearch.WordTrace tailWord_3599514 prefixEnd_3599514 1232187203058623412414095 := by
  unfold tailWord_3599514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32821265270395750223429399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87523374054388667262478397 32821265270395750223429399)
  ·
    refine ⟨49231897905593625335144099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32821265270395750223429399 49231897905593625335144099)
    ·
      refine ⟨73847846858390438002716149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49231897905593625335144099 73847846858390438002716149)
      ·
        refine ⟨6923235642974103562754639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73847846858390438002716149 6923235642974103562754639)
        ·
          refine ⟨10384853464461155344131959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923235642974103562754639 10384853464461155344131959)
          ·
            refine ⟨15577280196691733016197939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384853464461155344131959 15577280196691733016197939)
            ·
              refine ⟨23365920295037599524296909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15577280196691733016197939 23365920295037599524296909)
              ·
                refine ⟨8762220110639099821611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23365920295037599524296909 8762220110639099821611341)
                ·
                  refine ⟨3285832541489662433104253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8762220110639099821611341 3285832541489662433104253)
                  ·
                    refine ⟨1232187203058623412414095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285832541489662433104253 1232187203058623412414095)
                    ·
                      rfl

theorem cell22_3599514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_3599514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599514 prefixEnd_3599514 := by exact prefixLift 3599514
  have htrace : WordTrace (prefixWord ++ tailWord_3599514) baseStart_3599514 baseEnd_3599514 := by
    simpa [prefixWord, tailWord_3599514, baseEnd_3599514] using wordTrace_append hprefix tailTrace_3599514
  have hstable : (prefixWord ++ tailWord_3599514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599514).length < 2 ^ (prefixWord ++ tailWord_3599514).sum := by decide
  have hdescent : baseEnd_3599514 < baseStart_3599514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599548 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3599548 : Nat := 118140960795 + 3599548 * 2 ^ 59
def prefixEnd_3599548 : Nat := 4983230072969 + 3 ^ 40 * 3599548 * 2
def baseEnd_3599548 : Nat := 1232198841953458657063991

theorem tailTrace_3599548 : CollatzResearch.WordTrace tailWord_3599548 prefixEnd_3599548 1232198841953458657063991 := by
  unfold tailWord_3599548
  simp only [CollatzResearch.WordTrace]
  refine ⟨65643150581729912350227649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87524200775639883133636865 65643150581729912350227649)
  ·
    refine ⟨49232362936297434262670737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65643150581729912350227649 49232362936297434262670737)
    ·
      refine ⟨36924272202223075697003053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49232362936297434262670737 36924272202223075697003053)
      ·
        refine ⟨13846602075833653386376145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36924272202223075697003053 13846602075833653386376145)
        ·
          refine ⟨10384951556875240039782109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13846602075833653386376145 10384951556875240039782109)
          ·
            refine ⟨3894356833828215014918291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10384951556875240039782109 3894356833828215014918291)
            ·
              refine ⟨5841535250742322522377437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894356833828215014918291 5841535250742322522377437)
              ·
                refine ⟨2190575719028370945891539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5841535250742322522377437 2190575719028370945891539)
                ·
                  refine ⟨3285863578542556418837309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190575719028370945891539 3285863578542556418837309)
                  ·
                    refine ⟨1232198841953458657063991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285863578542556418837309 1232198841953458657063991)
                    ·
                      rfl

theorem cell22_3599548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3599548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599548 prefixEnd_3599548 := by exact prefixLift 3599548
  have htrace : WordTrace (prefixWord ++ tailWord_3599548) baseStart_3599548 baseEnd_3599548 := by
    simpa [prefixWord, tailWord_3599548, baseEnd_3599548] using wordTrace_append hprefix tailTrace_3599548
  have hstable : (prefixWord ++ tailWord_3599548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599548).length < 2 ^ (prefixWord ++ tailWord_3599548).sum := by decide
  have hdescent : baseEnd_3599548 < baseStart_3599548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599565 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3599565 : Nat := 118140960795 + 3599565 * 2 ^ 59
def prefixEnd_3599565 : Nat := 4983230072969 + 3 ^ 40 * 3599565 * 2
def baseEnd_3599565 : Nat := 1232204661400876279388939

theorem tailTrace_3599565 : CollatzResearch.WordTrace tailWord_3599565 prefixEnd_3599565 1232204661400876279388939 := by
  unfold tailWord_3599565
  simp only [CollatzResearch.WordTrace]
  refine ⟨131286921204398236603824149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87524614136265491069216099 131286921204398236603824149)
  ·
    refine ⟨6154074431456167340804257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131286921204398236603824149 6154074431456167340804257)
    ·
      refine ⟨4615555823592125505603193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154074431456167340804257 4615555823592125505603193)
      ·
        refine ⟨3461666867694094129202395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615555823592125505603193 3461666867694094129202395)
        ·
          refine ⟨5192500301541141193803593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461666867694094129202395 5192500301541141193803593)
          ·
            refine ⟨3894375226155855895352695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5192500301541141193803593 3894375226155855895352695)
            ·
              refine ⟨5841562839233783843029043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894375226155855895352695 5841562839233783843029043)
              ·
                refine ⟨8762344258850675764543565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841562839233783843029043 8762344258850675764543565)
                ·
                  refine ⟨3285879097069003411703837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8762344258850675764543565 3285879097069003411703837)
                  ·
                    refine ⟨1232204661400876279388939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285879097069003411703837 1232204661400876279388939)
                    ·
                      rfl

theorem cell22_3599565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3599565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599565 prefixEnd_3599565 := by exact prefixLift 3599565
  have htrace : WordTrace (prefixWord ++ tailWord_3599565) baseStart_3599565 baseEnd_3599565 := by
    simpa [prefixWord, tailWord_3599565, baseEnd_3599565] using wordTrace_append hprefix tailTrace_3599565
  have hstable : (prefixWord ++ tailWord_3599565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599565).length < 2 ^ (prefixWord ++ tailWord_3599565).sum := by decide
  have hdescent : baseEnd_3599565 < baseStart_3599565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599679 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 5]
def baseStart_3599679 : Nat := 118140960795 + 3599679 * 2 ^ 59
def prefixEnd_3599679 : Nat := 4983230072969 + 3 ^ 40 * 3599679 * 2
def baseEnd_3599679 : Nat := 410747895310205994012863

theorem tailTrace_3599679 : CollatzResearch.WordTrace tailWord_3599679 prefixEnd_3599679 410747895310205994012863 := by
  unfold tailWord_3599679
  simp only [CollatzResearch.WordTrace]
  refine ⟨131291079125985234073474091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87527386083990156048982727 131291079125985234073474091)
  ·
    refine ⟨196936618688977851110211137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131291079125985234073474091 196936618688977851110211137)
    ·
      refine ⟨147702464016733388332658353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196936618688977851110211137 147702464016733388332658353)
      ·
        refine ⟨110776848012550041249493765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147702464016733388332658353 110776848012550041249493765)
        ·
          refine ⟨20770659002353132734280081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110776848012550041249493765 20770659002353132734280081)
          ·
            refine ⟨15577994251764849550710061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20770659002353132734280081 15577994251764849550710061)
            ·
              refine ⟨5841747844411818581516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15577994251764849550710061 5841747844411818581516273)
              ·
                refine ⟨4381310883308863936137205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841747844411818581516273 4381310883308863936137205)
                ·
                  refine ⟨410747895310205994012863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381310883308863936137205 410747895310205994012863)
                  ·
                    rfl

theorem cell22_3599679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].length) (baseStart_3599679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599679 prefixEnd_3599679 := by exact prefixLift 3599679
  have htrace : WordTrace (prefixWord ++ tailWord_3599679) baseStart_3599679 baseEnd_3599679 := by
    simpa [prefixWord, tailWord_3599679, baseEnd_3599679] using wordTrace_append hprefix tailTrace_3599679
  have hstable : (prefixWord ++ tailWord_3599679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599679).length < 2 ^ (prefixWord ++ tailWord_3599679).sum := by decide
  have hdescent : baseEnd_3599679 < baseStart_3599679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599702 : List Nat := [5, 2, 3, 1, 1, 2, 2, 6]
def baseStart_3599702 : Nat := 118140960795 + 3599702 * 2 ^ 59
def prefixEnd_3599702 : Nat := 4983230072969 + 3 ^ 40 * 3599702 * 2
def baseEnd_3599702 : Nat := 136916839922294843190391

theorem tailTrace_3599702 : CollatzResearch.WordTrace tailWord_3599702 prefixEnd_3599702 136916839922294843190391 := by
  unfold tailWord_3599702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205744875306369312597585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87527945336601272667707573 8205744875306369312597585)
  ·
    refine ⟨6154308656479776984448189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8205744875306369312597585 6154308656479776984448189)
    ·
      refine ⟨2307865746179916369168071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6154308656479776984448189 2307865746179916369168071)
      ·
        refine ⟨3461798619269874553752107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307865746179916369168071 3461798619269874553752107)
        ·
          refine ⟨5192697928904811830628161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461798619269874553752107 5192697928904811830628161)
          ·
            refine ⟨3894523446678608872971121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5192697928904811830628161 3894523446678608872971121)
            ·
              refine ⟨2920892585008956654728341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894523446678608872971121 2920892585008956654728341)
              ·
                refine ⟨136916839922294843190391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920892585008956654728341 136916839922294843190391)
                ·
                  rfl

theorem cell22_3599702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_3599702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599702 prefixEnd_3599702 := by exact prefixLift 3599702
  have htrace : WordTrace (prefixWord ++ tailWord_3599702) baseStart_3599702 baseEnd_3599702 := by
    simpa [prefixWord, tailWord_3599702, baseEnd_3599702] using wordTrace_append hprefix tailTrace_3599702
  have hstable : (prefixWord ++ tailWord_3599702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599702).length < 2 ^ (prefixWord ++ tailWord_3599702).sum := by decide
  have hdescent : baseEnd_3599702 < baseStart_3599702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599739 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 4, 3]
def baseStart_3599739 : Nat := 118140960795 + 3599739 * 2 ^ 59
def prefixEnd_3599739 : Nat := 4983230072969 + 3 ^ 40 * 3599739 * 2
def baseEnd_3599739 : Nat := 1232264225156797825538405

theorem tailTrace_3599739 : CollatzResearch.WordTrace tailWord_3599739 prefixEnd_3599739 1232264225156797825538405 := by
  unfold tailWord_3599739
  simp only [CollatzResearch.WordTrace]
  refine ⟨131293267505767864320658271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87528845003845242880438847 131293267505767864320658271)
  ·
    refine ⟨196939901258651796480987407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131293267505767864320658271 196939901258651796480987407)
    ·
      refine ⟨295409851887977694721481111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196939901258651796480987407 295409851887977694721481111)
      ·
        refine ⟨443114777831966542082221667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295409851887977694721481111 443114777831966542082221667)
        ·
          refine ⟨664672166747949813123332501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443114777831966542082221667 664672166747949813123332501)
          ·
            refine ⟨31156507816310147490156211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 664672166747949813123332501 31156507816310147490156211)
            ·
              refine ⟨46734761724465221235234317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31156507816310147490156211 46734761724465221235234317)
              ·
                refine ⟨17525535646674457963212869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46734761724465221235234317 17525535646674457963212869)
                ·
                  refine ⟨3286037933751460868102413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17525535646674457963212869 3286037933751460868102413)
                  ·
                    refine ⟨1232264225156797825538405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286037933751460868102413 1232264225156797825538405)
                    ·
                      rfl

theorem cell22_3599739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].length) (baseStart_3599739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599739 prefixEnd_3599739 := by exact prefixLift 3599739
  have htrace : WordTrace (prefixWord ++ tailWord_3599739) baseStart_3599739 baseEnd_3599739 := by
    simpa [prefixWord, tailWord_3599739, baseEnd_3599739] using wordTrace_append hprefix tailTrace_3599739
  have hstable : (prefixWord ++ tailWord_3599739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599739).length < 2 ^ (prefixWord ++ tailWord_3599739).sum := by decide
  have hdescent : baseEnd_3599739 < baseStart_3599739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599756 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_3599756 : Nat := 118140960795 + 3599756 * 2 ^ 59
def prefixEnd_3599756 : Nat := 4983230072969 + 3 ^ 40 * 3599756 * 2
def baseEnd_3599756 : Nat := 1232270044604215447863353

theorem tailTrace_3599756 : CollatzResearch.WordTrace tailWord_3599756 prefixEnd_3599756 1232270044604215447863353 := by
  unfold tailWord_3599756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65646943773353138112013561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87529258364470850816018081 65646943773353138112013561)
  ·
    refine ⟨49235207830014853584010171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65646943773353138112013561 49235207830014853584010171)
    ·
      refine ⟨73852811745022280376015257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49235207830014853584010171 73852811745022280376015257)
      ·
        refine ⟨55389608808766710282011443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73852811745022280376015257 55389608808766710282011443)
        ·
          refine ⟨83084413213150065423017165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55389608808766710282011443 83084413213150065423017165)
          ·
            refine ⟨31156654954931274533631437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83084413213150065423017165 31156654954931274533631437)
            ·
              refine ⟨11683745608099227950111789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31156654954931274533631437 11683745608099227950111789)
              ·
                refine ⟨4381404603037210481291921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11683745608099227950111789 4381404603037210481291921)
                ·
                  refine ⟨3286053452277907860968941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381404603037210481291921 3286053452277907860968941)
                  ·
                    refine ⟨1232270044604215447863353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286053452277907860968941 1232270044604215447863353)
                    ·
                      rfl

theorem cell22_3599756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_3599756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599756 prefixEnd_3599756 := by exact prefixLift 3599756
  have htrace : WordTrace (prefixWord ++ tailWord_3599756) baseStart_3599756 baseEnd_3599756 := by
    simpa [prefixWord, tailWord_3599756, baseEnd_3599756] using wordTrace_append hprefix tailTrace_3599756
  have hstable : (prefixWord ++ tailWord_3599756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599756).length < 2 ^ (prefixWord ++ tailWord_3599756).sum := by decide
  have hdescent : baseEnd_3599756 < baseStart_3599756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599829 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3599829 : Nat := 118140960795 + 3599829 * 2 ^ 59
def prefixEnd_3599829 : Nat := 4983230072969 + 3 ^ 40 * 3599829 * 2
def baseEnd_3599829 : Nat := 1232295033996067590788129

theorem tailTrace_3599829 : CollatzResearch.WordTrace tailWord_3599829 prefixEnd_3599829 1232295033996067590788129 := by
  unfold tailWord_3599829
  simp only [CollatzResearch.WordTrace]
  refine ⟨131296550075441809691434541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87531033383627873127623027 131296550075441809691434541)
  ·
    refine ⟨49236206278290678634287953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131296550075441809691434541 49236206278290678634287953)
    ·
      refine ⟨36927154708718008975715965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49236206278290678634287953 36927154708718008975715965)
      ·
        refine ⟨13847683015769253365893487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36927154708718008975715965 13847683015769253365893487)
        ·
          refine ⟨20771524523653880048840231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13847683015769253365893487 20771524523653880048840231)
          ·
            refine ⟨31157286785480820073260347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20771524523653880048840231 31157286785480820073260347)
            ·
              refine ⟨46735930178221230109890521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31157286785480820073260347 46735930178221230109890521)
              ·
                refine ⟨35051947633665922582417891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46735930178221230109890521 35051947633665922582417891)
                ·
                  refine ⟨52577921450498883873626837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35051947633665922582417891 52577921450498883873626837)
                  ·
                    refine ⟨1232295033996067590788129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52577921450498883873626837 1232295033996067590788129)
                    ·
                      rfl

theorem cell22_3599829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3599829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599829 prefixEnd_3599829 := by exact prefixLift 3599829
  have htrace : WordTrace (prefixWord ++ tailWord_3599829) baseStart_3599829 baseEnd_3599829 := by
    simpa [prefixWord, tailWord_3599829, baseEnd_3599829] using wordTrace_append hprefix tailTrace_3599829
  have hstable : (prefixWord ++ tailWord_3599829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599829).length < 2 ^ (prefixWord ++ tailWord_3599829).sum := by decide
  have hdescent : baseEnd_3599829 < baseStart_3599829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599889 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3599889 : Nat := 118140960795 + 3599889 * 2 ^ 59
def prefixEnd_3599889 : Nat := 4983230072969 + 3 ^ 40 * 3599889 * 2
def baseEnd_3599889 : Nat := 1232315573222247434287945

theorem tailTrace_3599889 : CollatzResearch.WordTrace tailWord_3599889 prefixEnd_3599889 1232315573222247434287945 := by
  unfold tailWord_3599889
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298738455224439938618721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87532492303482959959079147 131298738455224439938618721)
  ·
    refine ⟨98474053841418329953964041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131298738455224439938618721 98474053841418329953964041)
    ·
      refine ⟨73855540381063747465473031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98474053841418329953964041 73855540381063747465473031)
      ·
        refine ⟨110783310571595621198209547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73855540381063747465473031 110783310571595621198209547)
        ·
          refine ⟨166174965857393431797314321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110783310571595621198209547 166174965857393431797314321)
          ·
            refine ⟨124631224393045073847985741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166174965857393431797314321 124631224393045073847985741)
            ·
              refine ⟨46736709147391902692994653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124631224393045073847985741 46736709147391902692994653)
              ·
                refine ⟨17526265930271963509872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46736709147391902692994653 17526265930271963509872995)
                ·
                  refine ⟨26289398895407945264809493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17526265930271963509872995 26289398895407945264809493)
                  ·
                    refine ⟨1232315573222247434287945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26289398895407945264809493 1232315573222247434287945)
                    ·
                      rfl

theorem cell22_3599889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3599889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599889 prefixEnd_3599889 := by exact prefixLift 3599889
  have htrace : WordTrace (prefixWord ++ tailWord_3599889) baseStart_3599889 baseEnd_3599889 := by
    simpa [prefixWord, tailWord_3599889, baseEnd_3599889] using wordTrace_append hprefix tailTrace_3599889
  have hstable : (prefixWord ++ tailWord_3599889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599889).length < 2 ^ (prefixWord ++ tailWord_3599889).sum := by decide
  have hdescent : baseEnd_3599889 < baseStart_3599889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599891 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 4, 3]
def baseStart_3599891 : Nat := 118140960795 + 3599891 * 2 ^ 59
def prefixEnd_3599891 : Nat := 4983230072969 + 3 ^ 40 * 3599891 * 2
def baseEnd_3599891 : Nat := 1232316257863120095737939

theorem tailTrace_3599891 : CollatzResearch.WordTrace tailWord_3599891 prefixEnd_3599891 1232316257863120095737939 := by
  unfold tailWord_3599891
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298811401217194280191527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87532540934144796186794351 131298811401217194280191527)
  ·
    refine ⟨196948217101825791420287291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131298811401217194280191527 196948217101825791420287291)
    ·
      refine ⟨295422325652738687130430937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196948217101825791420287291 295422325652738687130430937)
      ·
        refine ⟨221566744239554015347823203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295422325652738687130430937 221566744239554015347823203)
        ·
          refine ⟨332350116359331023021734805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221566744239554015347823203 332350116359331023021734805)
          ·
            refine ⟨15578911704343641704143819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332350116359331023021734805 15578911704343641704143819)
            ·
              refine ⟨23368367556515462556215729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578911704343641704143819 23368367556515462556215729)
              ·
                refine ⟨17526275667386596917161797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23368367556515462556215729 17526275667386596917161797)
                ·
                  refine ⟨3286176687634986921967837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17526275667386596917161797 3286176687634986921967837)
                  ·
                    refine ⟨1232316257863120095737939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286176687634986921967837 1232316257863120095737939)
                    ·
                      rfl

theorem cell22_3599891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].length) (baseStart_3599891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599891 prefixEnd_3599891 := by exact prefixLift 3599891
  have htrace : WordTrace (prefixWord ++ tailWord_3599891) baseStart_3599891 baseEnd_3599891 := by
    simpa [prefixWord, tailWord_3599891, baseEnd_3599891] using wordTrace_append hprefix tailTrace_3599891
  have hstable : (prefixWord ++ tailWord_3599891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599891).length < 2 ^ (prefixWord ++ tailWord_3599891).sum := by decide
  have hdescent : baseEnd_3599891 < baseStart_3599891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599893 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 4]
def baseStart_3599893 : Nat := 118140960795 + 3599893 * 2 ^ 59
def prefixEnd_3599893 : Nat := 4983230072969 + 3 ^ 40 * 3599893 * 2
def baseEnd_3599893 : Nat := 410772314167997585729311

theorem tailTrace_3599893 : CollatzResearch.WordTrace tailWord_3599893 prefixEnd_3599893 410772314167997585729311 := by
  unfold tailWord_3599893
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298884347209948621764333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87532589564806632414509555 131298884347209948621764333)
  ·
    refine ⟨49237081630203730733161625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131298884347209948621764333 49237081630203730733161625)
    ·
      refine ⟨36927811222652798049871219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49237081630203730733161625 36927811222652798049871219)
      ·
        refine ⟨55391716833979197074806829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36927811222652798049871219 55391716833979197074806829)
        ·
          refine ⟨20771893812742198903052561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55391716833979197074806829 20771893812742198903052561)
          ·
            refine ⟨15578920359556649177289421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20771893812742198903052561 15578920359556649177289421)
            ·
              refine ⟨5842095134833743441483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15578920359556649177289421 5842095134833743441483533)
              ·
                refine ⟨2190785675562653790556325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842095134833743441483533 2190785675562653790556325)
                ·
                  refine ⟨410772314167997585729311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190785675562653790556325 410772314167997585729311)
                  ·
                    rfl

theorem cell22_3599893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_3599893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599893 prefixEnd_3599893 := by exact prefixLift 3599893
  have htrace : WordTrace (prefixWord ++ tailWord_3599893) baseStart_3599893 baseEnd_3599893 := by
    simpa [prefixWord, tailWord_3599893, baseEnd_3599893] using wordTrace_append hprefix tailTrace_3599893
  have hstable : (prefixWord ++ tailWord_3599893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599893).length < 2 ^ (prefixWord ++ tailWord_3599893).sum := by decide
  have hdescent : baseEnd_3599893 < baseStart_3599893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599906 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3599906 : Nat := 118140960795 + 3599906 * 2 ^ 59
def prefixEnd_3599906 : Nat := 4983230072969 + 3 ^ 40 * 3599906 * 2
def baseEnd_3599906 : Nat := 1232321392669665056612893

theorem tailTrace_3599906 : CollatzResearch.WordTrace tailWord_3599906 prefixEnd_3599906 1232321392669665056612893 := by
  unfold tailWord_3599906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824839624040712960496893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87532905664108567894658381 32824839624040712960496893)
  ·
    refine ⟨12309314859015267360186335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32824839624040712960496893 12309314859015267360186335)
    ·
      refine ⟨18463972288522901040279503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309314859015267360186335 18463972288522901040279503)
      ·
        refine ⟨27695958432784351560419255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463972288522901040279503 27695958432784351560419255)
        ·
          refine ⟨41543937649176527340628883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27695958432784351560419255 41543937649176527340628883)
          ·
            refine ⟨62315906473764791010943325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41543937649176527340628883 62315906473764791010943325)
            ·
              refine ⟨23368464927661796629103747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62315906473764791010943325 23368464927661796629103747)
              ·
                refine ⟨35052697391492694943655621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23368464927661796629103747 35052697391492694943655621)
                ·
                  refine ⟨6572380760904880301935429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35052697391492694943655621 6572380760904880301935429)
                  ·
                    refine ⟨1232321392669665056612893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6572380760904880301935429 1232321392669665056612893)
                    ·
                      rfl

theorem cell22_3599906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3599906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599906 prefixEnd_3599906 := by exact prefixLift 3599906
  have htrace : WordTrace (prefixWord ++ tailWord_3599906) baseStart_3599906 baseEnd_3599906 := by
    simpa [prefixWord, tailWord_3599906, baseEnd_3599906] using wordTrace_append hprefix tailTrace_3599906
  have hstable : (prefixWord ++ tailWord_3599906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599906).length < 2 ^ (prefixWord ++ tailWord_3599906).sum := by decide
  have hdescent : baseEnd_3599906 < baseStart_3599906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599925 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3599925 : Nat := 118140960795 + 3599925 * 2 ^ 59
def prefixEnd_3599925 : Nat := 4983230072969 + 3 ^ 40 * 3599925 * 2
def baseEnd_3599925 : Nat := 1232327896757955340387835

theorem tailTrace_3599925 : CollatzResearch.WordTrace tailWord_3599925 prefixEnd_3599925 1232327896757955340387835 := by
  unfold tailWord_3599925
  simp only [CollatzResearch.WordTrace]
  refine ⟨131300051483094018086929229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87533367655396012057952819 131300051483094018086929229)
  ·
    refine ⟨49237519306160256782598461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131300051483094018086929229 49237519306160256782598461)
    ·
      refine ⟨18464069739810096293474423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49237519306160256782598461 18464069739810096293474423)
      ·
        refine ⟨27696104609715144440211635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464069739810096293474423 27696104609715144440211635)
        ·
          refine ⟨41544156914572716660317453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27696104609715144440211635 41544156914572716660317453)
          ·
            refine ⟨15579058842964768747619045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41544156914572716660317453 15579058842964768747619045)
            ·
              refine ⟨2921073533055894140178571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15579058842964768747619045 2921073533055894140178571)
              ·
                refine ⟨4381610299583841210267857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921073533055894140178571 4381610299583841210267857)
                ·
                  refine ⟨3286207724687880907700893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381610299583841210267857 3286207724687880907700893)
                  ·
                    refine ⟨1232327896757955340387835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286207724687880907700893 1232327896757955340387835)
                    ·
                      rfl

theorem cell22_3599925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3599925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599925 prefixEnd_3599925 := by exact prefixLift 3599925
  have htrace : WordTrace (prefixWord ++ tailWord_3599925) baseStart_3599925 baseEnd_3599925 := by
    simpa [prefixWord, tailWord_3599925, baseEnd_3599925] using wordTrace_append hprefix tailTrace_3599925
  have hstable : (prefixWord ++ tailWord_3599925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599925).length < 2 ^ (prefixWord ++ tailWord_3599925).sum := by decide
  have hdescent : baseEnd_3599925 < baseStart_3599925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3599936 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_3599936 : Nat := 118140960795 + 3599936 * 2 ^ 59
def prefixEnd_3599936 : Nat := 4983230072969 + 3 ^ 40 * 3599936 * 2
def baseEnd_3599936 : Nat := 1232331662282754978362801

theorem tailTrace_3599936 : CollatzResearch.WordTrace tailWord_3599936 prefixEnd_3599936 1232331662282754978362801 := by
  unfold tailWord_3599936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65650226343027083482789831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87533635124036111310386441 65650226343027083482789831)
  ·
    refine ⟨98475339514540625224184747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65650226343027083482789831 98475339514540625224184747)
    ·
      refine ⟨147713009271810937836277121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98475339514540625224184747 147713009271810937836277121)
      ·
        refine ⟨110784756953858203377207841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147713009271810937836277121 110784756953858203377207841)
        ·
          refine ⟨83088567715393652532905881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110784756953858203377207841 83088567715393652532905881)
          ·
            refine ⟨62316425786545239399679411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83088567715393652532905881 62316425786545239399679411)
            ·
              refine ⟨93474638679817859099519117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62316425786545239399679411 93474638679817859099519117)
              ·
                refine ⟨35052989504931697162319669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93474638679817859099519117 35052989504931697162319669)
                ·
                  refine ⟨3286217766087346608967469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35052989504931697162319669 3286217766087346608967469)
                  ·
                    refine ⟨1232331662282754978362801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286217766087346608967469 1232331662282754978362801)
                    ·
                      rfl

theorem cell22_3599936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_3599936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3599936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3599936 prefixEnd_3599936 := by exact prefixLift 3599936
  have htrace : WordTrace (prefixWord ++ tailWord_3599936) baseStart_3599936 baseEnd_3599936 := by
    simpa [prefixWord, tailWord_3599936, baseEnd_3599936] using wordTrace_append hprefix tailTrace_3599936
  have hstable : (prefixWord ++ tailWord_3599936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3599936).length < 2 ^ (prefixWord ++ tailWord_3599936).sum := by decide
  have hdescent : baseEnd_3599936 < baseStart_3599936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3599936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600062 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_3600062 : Nat := 118140960795 + 3600062 * 2 ^ 59
def prefixEnd_3600062 : Nat := 4983230072969 + 3 ^ 40 * 3600062 * 2
def baseEnd_3600062 : Nat := 410791598219244216570805

theorem tailTrace_3600062 : CollatzResearch.WordTrace tailWord_3600062 prefixEnd_3600062 410791598219244216570805 := by
  unfold tailWord_3600062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413131035449711310583305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87536698855731793656444293 16413131035449711310583305)
  ·
    refine ⟨12309848276587283482937479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16413131035449711310583305 12309848276587283482937479)
    ·
      refine ⟨18464772414880925224406219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309848276587283482937479 18464772414880925224406219)
      ·
        refine ⟨27697158622321387836609329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464772414880925224406219 27697158622321387836609329)
        ·
          refine ⟨20772868966741040877456997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27697158622321387836609329 20772868966741040877456997)
          ·
            refine ⟨3894912931263945164523187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20772868966741040877456997 3894912931263945164523187)
            ·
              refine ⟨5842369396895917746784781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894912931263945164523187 5842369396895917746784781)
              ·
                refine ⟨2190888523835969155044293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842369396895917746784781 2190888523835969155044293)
                ·
                  refine ⟨410791598219244216570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190888523835969155044293 410791598219244216570805)
                  ·
                    rfl

theorem cell22_3600062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_3600062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600062 prefixEnd_3600062 := by exact prefixLift 3600062
  have htrace : WordTrace (prefixWord ++ tailWord_3600062) baseStart_3600062 baseEnd_3600062 := by
    simpa [prefixWord, tailWord_3600062, baseEnd_3600062] using wordTrace_append hprefix tailTrace_3600062
  have hstable : (prefixWord ++ tailWord_3600062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600062).length < 2 ^ (prefixWord ++ tailWord_3600062).sum := by decide
  have hdescent : baseEnd_3600062 < baseStart_3600062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600077 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3600077 : Nat := 118140960795 + 3600077 * 2 ^ 59
def prefixEnd_3600077 : Nat := 4983230072969 + 3 ^ 40 * 3600077 * 2
def baseEnd_3600077 : Nat := 1232379929464277610587369

theorem tailTrace_3600077 : CollatzResearch.WordTrace tailWord_3600077 prefixEnd_3600077 1232379929464277610587369 := by
  unfold tailWord_3600077
  simp only [CollatzResearch.WordTrace]
  refine ⟨131305595378543348046462485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87537063585695565364308323 131305595378543348046462485)
  ·
    refine ⟨6154949783369219439677929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131305595378543348046462485 6154949783369219439677929)
    ·
      refine ⟨4616212337526914579758447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154949783369219439677929 4616212337526914579758447)
      ·
        refine ⟨6924318506290371869637671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616212337526914579758447 6924318506290371869637671)
        ·
          refine ⟨10386477759435557804456507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6924318506290371869637671 10386477759435557804456507)
          ·
            refine ⟨15579716639153336706684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10386477759435557804456507 15579716639153336706684761)
            ·
              refine ⟨11684787479365002530013571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579716639153336706684761 11684787479365002530013571)
              ·
                refine ⟨17527181219047503795020357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684787479365002530013571 17527181219047503795020357)
                ·
                  refine ⟨3286346478571406961566317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17527181219047503795020357 3286346478571406961566317)
                  ·
                    refine ⟨1232379929464277610587369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286346478571406961566317 1232379929464277610587369)
                    ·
                      rfl

theorem cell22_3600077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3600077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600077 prefixEnd_3600077 := by exact prefixLift 3600077
  have htrace : WordTrace (prefixWord ++ tailWord_3600077) baseStart_3600077 baseEnd_3600077 := by
    simpa [prefixWord, tailWord_3600077, baseEnd_3600077] using wordTrace_append hprefix tailTrace_3600077
  have hstable : (prefixWord ++ tailWord_3600077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600077).length < 2 ^ (prefixWord ++ tailWord_3600077).sum := by decide
  have hdescent : baseEnd_3600077 < baseStart_3600077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600141 : List Nat := [1, 7, 2, 1, 1, 2, 1, 7]
def baseStart_3600141 : Nat := 118140960795 + 3600141 * 2 ^ 59
def prefixEnd_3600141 : Nat := 4983230072969 + 3 ^ 40 * 3600141 * 2
def baseEnd_3600141 : Nat := 136933537552466975220797

theorem tailTrace_3600141 : CollatzResearch.WordTrace tailWord_3600141 prefixEnd_3600141 136933537552466975220797 := by
  unfold tailWord_3600141
  simp only [CollatzResearch.WordTrace]
  refine ⟨131307929650311486976792277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87538619766874324651194851 131307929650311486976792277)
  ·
    refine ⟨3077529601179175476018569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 131307929650311486976792277 3077529601179175476018569)
    ·
      refine ⟨2308147200884381607013927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3077529601179175476018569 2308147200884381607013927)
      ·
        refine ⟨3462220801326572410520891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308147200884381607013927 3462220801326572410520891)
        ·
          refine ⟨5193331201989858615781337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462220801326572410520891 5193331201989858615781337)
          ·
            refine ⟨3894998401492393961836003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193331201989858615781337 3894998401492393961836003)
            ·
              refine ⟨5842497602238590942754005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894998401492393961836003 5842497602238590942754005)
              ·
                refine ⟨136933537552466975220797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5842497602238590942754005 136933537552466975220797)
                ·
                  rfl

theorem cell22_3600141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 7].length) (baseStart_3600141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600141 prefixEnd_3600141 := by exact prefixLift 3600141
  have htrace : WordTrace (prefixWord ++ tailWord_3600141) baseStart_3600141 baseEnd_3600141 := by
    simpa [prefixWord, tailWord_3600141, baseEnd_3600141] using wordTrace_append hprefix tailTrace_3600141
  have hstable : (prefixWord ++ tailWord_3600141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600141).length < 2 ^ (prefixWord ++ tailWord_3600141).sum := by decide
  have hdescent : baseEnd_3600141 < baseStart_3600141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600195 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 4, 3]
def baseStart_3600195 : Nat := 118140960795 + 3600195 * 2 ^ 59
def prefixEnd_3600195 : Nat := 4983230072969 + 3 ^ 40 * 3600195 * 2
def baseEnd_3600195 : Nat := 1232420323275764636137007

theorem tailTrace_3600195 : CollatzResearch.WordTrace tailWord_3600195 prefixEnd_3600195 1232420323275764636137007 := by
  unfold tailWord_3600195
  simp only [CollatzResearch.WordTrace]
  refine ⟨131309899192115854199258039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87539932794743902799505359 131309899192115854199258039)
  ·
    refine ⟨196964848788173781298887059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131309899192115854199258039 196964848788173781298887059)
    ·
      refine ⟨295447273182260671948330589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196964848788173781298887059 295447273182260671948330589)
      ·
        refine ⟨110792727443347751980623971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295447273182260671948330589 110792727443347751980623971)
        ·
          refine ⟨166189091165021627970935957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110792727443347751980623971 166189091165021627970935957)
          ·
            refine ⟨7790113648360388811137623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166189091165021627970935957 7790113648360388811137623)
            ·
              refine ⟨11685170472540583216706435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790113648360388811137623 11685170472540583216706435)
              ·
                refine ⟨17527755708810874825059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11685170472540583216706435 17527755708810874825059653)
                ·
                  refine ⟨3286454195402039029698685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17527755708810874825059653 3286454195402039029698685)
                  ·
                    refine ⟨1232420323275764636137007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286454195402039029698685 1232420323275764636137007)
                    ·
                      rfl

theorem cell22_3600195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].length) (baseStart_3600195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600195 prefixEnd_3600195 := by exact prefixLift 3600195
  have htrace : WordTrace (prefixWord ++ tailWord_3600195) baseStart_3600195 baseEnd_3600195 := by
    simpa [prefixWord, tailWord_3600195, baseEnd_3600195] using wordTrace_append hprefix tailTrace_3600195
  have hstable : (prefixWord ++ tailWord_3600195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600195).length < 2 ^ (prefixWord ++ tailWord_3600195).sum := by decide
  have hdescent : baseEnd_3600195 < baseStart_3600195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600212 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3600212 : Nat := 118140960795 + 3600212 * 2 ^ 59
def prefixEnd_3600212 : Nat := 4983230072969 + 3 ^ 40 * 3600212 * 2
def baseEnd_3600212 : Nat := 1232426142723182258461955

theorem tailTrace_3600212 : CollatzResearch.WordTrace tailWord_3600212 prefixEnd_3600212 1232426142723182258461955 := by
  unfold tailWord_3600212
  simp only [CollatzResearch.WordTrace]
  refine ⟨65655259616527133051313445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87540346155369510735084593 65655259616527133051313445)
  ·
    refine ⟨12310361178098837447121271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65655259616527133051313445 12310361178098837447121271)
    ·
      refine ⟨18465541767148256170681907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12310361178098837447121271 18465541767148256170681907)
      ·
        refine ⟨27698312650722384256022861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18465541767148256170681907 27698312650722384256022861)
        ·
          refine ⟨10386867244020894096008573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27698312650722384256022861 10386867244020894096008573)
          ·
            refine ⟨3895075216507835286003215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10386867244020894096008573 3895075216507835286003215)
            ·
              refine ⟨5842612824761752929004823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895075216507835286003215 5842612824761752929004823)
              ·
                refine ⟨8763919237142629393507235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5842612824761752929004823 8763919237142629393507235)
                ·
                  refine ⟨13145878855713944090260853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8763919237142629393507235 13145878855713944090260853)
                  ·
                    refine ⟨1232426142723182258461955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13145878855713944090260853 1232426142723182258461955)
                    ·
                      rfl

theorem cell22_3600212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3600212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600212 prefixEnd_3600212 := by exact prefixLift 3600212
  have htrace : WordTrace (prefixWord ++ tailWord_3600212) baseStart_3600212 baseEnd_3600212 := by
    simpa [prefixWord, tailWord_3600212, baseEnd_3600212] using wordTrace_append hprefix tailTrace_3600212
  have hstable : (prefixWord ++ tailWord_3600212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600212).length < 2 ^ (prefixWord ++ tailWord_3600212).sum := by decide
  have hdescent : baseEnd_3600212 < baseStart_3600212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600268 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3600268 : Nat := 118140960795 + 3600268 * 2 ^ 59
def prefixEnd_3600268 : Nat := 4983230072969 + 3 ^ 40 * 3600268 * 2
def baseEnd_3600268 : Nat := 1232445312667616779061783

theorem tailTrace_3600268 : CollatzResearch.WordTrace tailWord_3600268 prefixEnd_3600268 1232445312667616779061783 := by
  unfold tailWord_3600268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65656280860425693833332729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87541707813900925111110305 65656280860425693833332729)
  ·
    refine ⟨49242210645319270374999547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65656280860425693833332729 49242210645319270374999547)
    ·
      refine ⟨73863315967978905562499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49242210645319270374999547 73863315967978905562499321)
      ·
        refine ⟨55397486975984179171874491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73863315967978905562499321 55397486975984179171874491)
        ·
          refine ⟨83096230463976268757811737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55397486975984179171874491 83096230463976268757811737)
          ·
            refine ⟨62322172847982201568358803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83096230463976268757811737 62322172847982201568358803)
            ·
              refine ⟨93483259271973302352538205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62322172847982201568358803 93483259271973302352538205)
              ·
                refine ⟨35056222226989988382201827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93483259271973302352538205 35056222226989988382201827)
                ·
                  refine ⟨52584333340484982573302741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35056222226989988382201827 52584333340484982573302741)
                  ·
                    refine ⟨1232445312667616779061783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52584333340484982573302741 1232445312667616779061783)
                    ·
                      rfl

theorem cell22_3600268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3600268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600268 prefixEnd_3600268 := by exact prefixLift 3600268
  have htrace : WordTrace (prefixWord ++ tailWord_3600268) baseStart_3600268 baseEnd_3600268 := by
    simpa [prefixWord, tailWord_3600268, baseEnd_3600268] using wordTrace_append hprefix tailTrace_3600268
  have hstable : (prefixWord ++ tailWord_3600268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600268).length < 2 ^ (prefixWord ++ tailWord_3600268).sum := by decide
  have hdescent : baseEnd_3600268 < baseStart_3600268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600308 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3600308 : Nat := 118140960795 + 3600308 * 2 ^ 59
def prefixEnd_3600308 : Nat := 4983230072969 + 3 ^ 40 * 3600308 * 2
def baseEnd_3600308 : Nat := 1232459005485070008061661

theorem tailTrace_3600308 : CollatzResearch.WordTrace tailWord_3600308 prefixEnd_3600308 1232459005485070008061661 := by
  unfold tailWord_3600308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657010320353237249060789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87542680427137649665414385 65657010320353237249060789)
  ·
    refine ⟨6155344717533115992099449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65657010320353237249060789 6155344717533115992099449)
    ·
      refine ⟨4616508538149836994074587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6155344717533115992099449 4616508538149836994074587)
      ·
        refine ⟨6924762807224755491111881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616508538149836994074587 6924762807224755491111881)
        ·
          refine ⟨5193572105418566618333911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924762807224755491111881 5193572105418566618333911)
          ·
            refine ⟨7790358158127849927500867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193572105418566618333911 7790358158127849927500867)
            ·
              refine ⟨11685537237191774891251301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790358158127849927500867 11685537237191774891251301)
              ·
                refine ⟨2191038231973457792109619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11685537237191774891251301 2191038231973457792109619)
                ·
                  refine ⟨3286557347960186688164429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191038231973457792109619 3286557347960186688164429)
                  ·
                    refine ⟨1232459005485070008061661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286557347960186688164429 1232459005485070008061661)
                    ·
                      rfl

theorem cell22_3600308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3600308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600308 prefixEnd_3600308 := by exact prefixLift 3600308
  have htrace : WordTrace (prefixWord ++ tailWord_3600308) baseStart_3600308 baseEnd_3600308 := by
    simpa [prefixWord, tailWord_3600308, baseEnd_3600308] using wordTrace_append hprefix tailTrace_3600308
  have hstable : (prefixWord ++ tailWord_3600308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600308).length < 2 ^ (prefixWord ++ tailWord_3600308).sum := by decide
  have hdescent : baseEnd_3600308 < baseStart_3600308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600330 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3600330 : Nat := 118140960795 + 3600330 * 2 ^ 59
def prefixEnd_3600330 : Nat := 4983230072969 + 3 ^ 40 * 3600330 * 2
def baseEnd_3600330 : Nat := 1232466536534669284011593

theorem tailTrace_3600330 : CollatzResearch.WordTrace tailWord_3600330 prefixEnd_3600330 1232466536534669284011593 := by
  unfold tailWord_3600330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32828705761656693063855611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87543215364417848170281629 32828705761656693063855611)
  ·
    refine ⟨49243058642485039595783417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32828705761656693063855611 49243058642485039595783417)
    ·
      refine ⟨36932293981863779696837563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49243058642485039595783417 36932293981863779696837563)
      ·
        refine ⟨55398440972795669545256345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36932293981863779696837563 55398440972795669545256345)
        ·
          refine ⟨41548830729596752158942259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55398440972795669545256345 41548830729596752158942259)
          ·
            refine ⟨62323246094395128238413389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41548830729596752158942259 62323246094395128238413389)
            ·
              refine ⟨23371217285398173089405021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62323246094395128238413389 23371217285398173089405021)
              ·
                refine ⟨8764206482024314908526883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23371217285398173089405021 8764206482024314908526883)
                ·
                  refine ⟨13146309723036472362790325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764206482024314908526883 13146309723036472362790325)
                  ·
                    refine ⟨1232466536534669284011593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13146309723036472362790325 1232466536534669284011593)
                    ·
                      rfl

theorem cell22_3600330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3600330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600330 prefixEnd_3600330 := by exact prefixLift 3600330
  have htrace : WordTrace (prefixWord ++ tailWord_3600330) baseStart_3600330 baseEnd_3600330 := by
    simpa [prefixWord, tailWord_3600330, baseEnd_3600330] using wordTrace_append hprefix tailTrace_3600330
  have hstable : (prefixWord ++ tailWord_3600330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600330).length < 2 ^ (prefixWord ++ tailWord_3600330).sum := by decide
  have hdescent : baseEnd_3600330 < baseStart_3600330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600392 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_3600392 : Nat := 118140960795 + 3600392 * 2 ^ 59
def prefixEnd_3600392 : Nat := 4983230072969 + 3 ^ 40 * 3600392 * 2
def baseEnd_3600392 : Nat := 1232487760401721788961403

theorem tailTrace_3600392 : CollatzResearch.WordTrace tailWord_3600392 prefixEnd_3600392 1232487760401721788961403 := by
  unfold tailWord_3600392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65658542186201078422089715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87544722914934771229452953 65658542186201078422089715)
  ·
    refine ⟨98487813279301617633134573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65658542186201078422089715 98487813279301617633134573)
    ·
      refine ⟨36932929979738106612425465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98487813279301617633134573 36932929979738106612425465)
      ·
        refine ⟨27699697484803579959319099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36932929979738106612425465 27699697484803579959319099)
        ·
          refine ⟨41549546227205369938978649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27699697484803579959319099 41549546227205369938978649)
          ·
            refine ⟨31162159670404027454233987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41549546227205369938978649 31162159670404027454233987)
            ·
              refine ⟨46743239505606041181350981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31162159670404027454233987 46743239505606041181350981)
              ·
                refine ⟨8764357407301132721503309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46743239505606041181350981 8764357407301132721503309)
                ·
                  refine ⟨3286634027737924770563741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8764357407301132721503309 3286634027737924770563741)
                  ·
                    refine ⟨1232487760401721788961403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286634027737924770563741 1232487760401721788961403)
                    ·
                      rfl

theorem cell22_3600392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_3600392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600392 prefixEnd_3600392 := by exact prefixLift 3600392
  have htrace : WordTrace (prefixWord ++ tailWord_3600392) baseStart_3600392 baseEnd_3600392 := by
    simpa [prefixWord, tailWord_3600392, baseEnd_3600392] using wordTrace_append hprefix tailTrace_3600392
  have hstable : (prefixWord ++ tailWord_3600392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600392).length < 2 ^ (prefixWord ++ tailWord_3600392).sum := by decide
  have hdescent : baseEnd_3600392 < baseStart_3600392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600394 : List Nat := [3, 1, 2, 2, 4, 2, 2, 6]
def baseStart_3600394 : Nat := 118140960795 + 3600394 * 2 ^ 59
def prefixEnd_3600394 : Nat := 4983230072969 + 3 ^ 40 * 3600394 * 2
def baseEnd_3600394 : Nat := 136943160560288272267933

theorem tailTrace_3600394 : CollatzResearch.WordTrace tailWord_3600394 prefixEnd_3600394 136943160560288272267933 := by
  unfold tailWord_3600394
  simp only [CollatzResearch.WordTrace]
  refine ⟨32829289329598727796438059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87544771545596607457168157 32829289329598727796438059)
  ·
    refine ⟨49243933994398091694657089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32829289329598727796438059 49243933994398091694657089)
    ·
      refine ⟨36932950495798568770992817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49243933994398091694657089 36932950495798568770992817)
      ·
        refine ⟨27699712871848926578244613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36932950495798568770992817 27699712871848926578244613)
        ·
          refine ⟨5193696163471673733420865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27699712871848926578244613 5193696163471673733420865)
          ·
            refine ⟨3895272122603755300065649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193696163471673733420865 3895272122603755300065649)
            ·
              refine ⟨2921454091952816475049237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895272122603755300065649 2921454091952816475049237)
              ·
                refine ⟨136943160560288272267933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2921454091952816475049237 136943160560288272267933)
                ·
                  rfl

theorem cell22_3600394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_3600394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600394 prefixEnd_3600394 := by exact prefixLift 3600394
  have htrace : WordTrace (prefixWord ++ tailWord_3600394) baseStart_3600394 baseEnd_3600394 := by
    simpa [prefixWord, tailWord_3600394, baseEnd_3600394] using wordTrace_append hprefix tailTrace_3600394
  have hstable : (prefixWord ++ tailWord_3600394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600394).length < 2 ^ (prefixWord ++ tailWord_3600394).sum := by decide
  have hdescent : baseEnd_3600394 < baseStart_3600394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600426 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3600426 : Nat := 118140960795 + 3600426 * 2 ^ 59
def prefixEnd_3600426 : Nat := 4983230072969 + 3 ^ 40 * 3600426 * 2
def baseEnd_3600426 : Nat := 1232499399296557033611299

theorem tailTrace_3600426 : CollatzResearch.WordTrace tailWord_3600426 prefixEnd_3600426 1232499399296557033611299 := by
  unfold tailWord_3600426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32829581113569745162729283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87545549636185987100611421 32829581113569745162729283)
  ·
    refine ⟨49244371670354617744093925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32829581113569745162729283 49244371670354617744093925)
    ·
      refine ⟨9233319688191490827017611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49244371670354617744093925 9233319688191490827017611)
      ·
        refine ⟨13849979532287236240526417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233319688191490827017611 13849979532287236240526417)
        ·
          refine ⟨10387484649215427180394813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13849979532287236240526417 10387484649215427180394813)
          ·
            refine ⟨3895306743455785192648055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10387484649215427180394813 3895306743455785192648055)
            ·
              refine ⟨5842960115183677788972083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895306743455785192648055 5842960115183677788972083)
              ·
                refine ⟨8764440172775516683458125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5842960115183677788972083 8764440172775516683458125)
                ·
                  refine ⟨3286665064790818756296797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8764440172775516683458125 3286665064790818756296797)
                  ·
                    refine ⟨1232499399296557033611299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286665064790818756296797 1232499399296557033611299)
                    ·
                      rfl

theorem cell22_3600426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3600426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600426 prefixEnd_3600426 := by exact prefixLift 3600426
  have htrace : WordTrace (prefixWord ++ tailWord_3600426) baseStart_3600426 baseEnd_3600426 := by
    simpa [prefixWord, tailWord_3600426, baseEnd_3600426] using wordTrace_append hprefix tailTrace_3600426
  have hstable : (prefixWord ++ tailWord_3600426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600426).length < 2 ^ (prefixWord ++ tailWord_3600426).sum := by decide
  have hdescent : baseEnd_3600426 < baseStart_3600426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600544 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_3600544 : Nat := 118140960795 + 3600544 * 2 ^ 59
def prefixEnd_3600544 : Nat := 4983230072969 + 3 ^ 40 * 3600544 * 2
def baseEnd_3600544 : Nat := 1232539793108044059160937

theorem tailTrace_3600544 : CollatzResearch.WordTrace tailWord_3600544 prefixEnd_3600544 1232539793108044059160937 := by
  unfold tailWord_3600544
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661314133925743401856343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87548418845234324535808457 65661314133925743401856343)
  ·
    refine ⟨98491971200888615102784515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65661314133925743401856343 98491971200888615102784515)
    ·
      refine ⟨147737956801332922654176773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98491971200888615102784515 147737956801332922654176773)
      ·
        refine ⟨27700866900249922997658145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147737956801332922654176773 27700866900249922997658145)
        ·
          refine ⟨20775650175187442248243609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27700866900249922997658145 20775650175187442248243609)
          ·
            refine ⟨15581737631390581686182707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20775650175187442248243609 15581737631390581686182707)
            ·
              refine ⟨23372606447085872529274061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15581737631390581686182707 23372606447085872529274061)
              ·
                refine ⟨8764727417657202198477773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23372606447085872529274061 8764727417657202198477773)
                ·
                  refine ⟨3286772781621450824429165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8764727417657202198477773 3286772781621450824429165)
                  ·
                    refine ⟨1232539793108044059160937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286772781621450824429165 1232539793108044059160937)
                    ·
                      rfl

theorem cell22_3600544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_3600544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600544 prefixEnd_3600544 := by exact prefixLift 3600544
  have htrace : WordTrace (prefixWord ++ tailWord_3600544) baseStart_3600544 baseEnd_3600544 := by
    simpa [prefixWord, tailWord_3600544, baseEnd_3600544] using wordTrace_append hprefix tailTrace_3600544
  have hstable : (prefixWord ++ tailWord_3600544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600544).length < 2 ^ (prefixWord ++ tailWord_3600544).sum := by decide
  have hdescent : baseEnd_3600544 < baseStart_3600544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600621 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3600621 : Nat := 118140960795 + 3600621 * 2 ^ 59
def prefixEnd_3600621 : Nat := 4983230072969 + 3 ^ 40 * 3600621 * 2
def baseEnd_3600621 : Nat := 1232566151781641524985701

theorem tailTrace_3600621 : CollatzResearch.WordTrace tailWord_3600621 prefixEnd_3600621 1232566151781641524985701 := by
  unfold tailWord_3600621
  simp only [CollatzResearch.WordTrace]
  refine ⟨131325436688572528954265717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87550291125715019302843811 131325436688572528954265717)
  ·
    refine ⟨12311759689553674589462411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131325436688572528954265717 12311759689553674589462411)
    ·
      refine ⟨18467639534330511884193617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12311759689553674589462411 18467639534330511884193617)
      ·
        refine ⟨13850729650747883913145213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18467639534330511884193617 13850729650747883913145213)
        ·
          refine ⟨5194023619030456467429455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13850729650747883913145213 5194023619030456467429455)
          ·
            refine ⟨7791035428545684701144183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194023619030456467429455 7791035428545684701144183)
            ·
              refine ⟨11686553142818527051716275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791035428545684701144183 11686553142818527051716275)
              ·
                refine ⟨17529829714227790577574413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686553142818527051716275 17529829714227790577574413)
                ·
                  refine ⟨6573686142835421466590405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17529829714227790577574413 6573686142835421466590405)
                  ·
                    refine ⟨1232566151781641524985701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573686142835421466590405 1232566151781641524985701)
                    ·
                      rfl

theorem cell22_3600621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3600621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600621 prefixEnd_3600621 := by exact prefixLift 3600621
  have htrace : WordTrace (prefixWord ++ tailWord_3600621) baseStart_3600621 baseEnd_3600621 := by
    simpa [prefixWord, tailWord_3600621, baseEnd_3600621] using wordTrace_append hprefix tailTrace_3600621
  have hstable : (prefixWord ++ tailWord_3600621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600621).length < 2 ^ (prefixWord ++ tailWord_3600621).sum := by decide
  have hdescent : baseEnd_3600621 < baseStart_3600621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600632 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_3600632 : Nat := 118140960795 + 3600632 * 2 ^ 59
def prefixEnd_3600632 : Nat := 4983230072969 + 3 ^ 40 * 3600632 * 2
def baseEnd_3600632 : Nat := 1232569917306441162960667

theorem tailTrace_3600632 : CollatzResearch.WordTrace tailWord_3600632 prefixEnd_3600632 1232569917306441162960667 := by
  unfold tailWord_3600632
  simp only [CollatzResearch.WordTrace]
  refine ⟨65662918945766338916458075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87550558594355118555277433 65662918945766338916458075)
  ·
    refine ⟨98494378418649508374687113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65662918945766338916458075 98494378418649508374687113)
    ·
      refine ⟨73870783813987131281015335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98494378418649508374687113 73870783813987131281015335)
      ·
        refine ⟨110806175720980696921523003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73870783813987131281015335 110806175720980696921523003)
        ·
          refine ⟨166209263581471045382284505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110806175720980696921523003 166209263581471045382284505)
          ·
            refine ⟨124656947686103284036713379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166209263581471045382284505 124656947686103284036713379)
            ·
              refine ⟨186985421529154926055070069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124656947686103284036713379 186985421529154926055070069)
              ·
                refine ⟨17529883268358274317662819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186985421529154926055070069 17529883268358274317662819)
                ·
                  refine ⟨26294824902537411476494229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17529883268358274317662819 26294824902537411476494229)
                  ·
                    refine ⟨1232569917306441162960667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26294824902537411476494229 1232569917306441162960667)
                    ·
                      rfl

theorem cell22_3600632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_3600632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600632 prefixEnd_3600632 := by exact prefixLift 3600632
  have htrace : WordTrace (prefixWord ++ tailWord_3600632) baseStart_3600632 baseEnd_3600632 := by
    simpa [prefixWord, tailWord_3600632, baseEnd_3600632] using wordTrace_append hprefix tailTrace_3600632
  have hstable : (prefixWord ++ tailWord_3600632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600632).length < 2 ^ (prefixWord ++ tailWord_3600632).sum := by decide
  have hdescent : baseEnd_3600632 < baseStart_3600632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600634 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3600634 : Nat := 118140960795 + 3600634 * 2 ^ 59
def prefixEnd_3600634 : Nat := 4983230072969 + 3 ^ 40 * 3600634 * 2
def baseEnd_3600634 : Nat := 1232570601947313824410661

theorem tailTrace_3600634 : CollatzResearch.WordTrace tailWord_3600634 prefixEnd_3600634 1232570601947313824410661 := by
  unfold tailWord_3600634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32831477709381358043622239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87550607225016954782992637 32831477709381358043622239)
  ·
    refine ⟨49247216564072037065433359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32831477709381358043622239 49247216564072037065433359)
    ·
      refine ⟨73870824846108055598150039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49247216564072037065433359 73870824846108055598150039)
      ·
        refine ⟨110806237269162083397225059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73870824846108055598150039 110806237269162083397225059)
        ·
          refine ⟨166209355903743125095837589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110806237269162083397225059 166209355903743125095837589)
          ·
            refine ⟨7791063557987958988867387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166209355903743125095837589 7791063557987958988867387)
            ·
              refine ⟨11686595336981938483301081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791063557987958988867387 11686595336981938483301081)
              ·
                refine ⟨8764946502736453862475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11686595336981938483301081 8764946502736453862475811)
                ·
                  refine ⟨13147419754104680793713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764946502736453862475811 13147419754104680793713717)
                  ·
                    refine ⟨1232570601947313824410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13147419754104680793713717 1232570601947313824410661)
                    ·
                      rfl

theorem cell22_3600634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3600634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600634 prefixEnd_3600634 := by exact prefixLift 3600634
  have htrace : WordTrace (prefixWord ++ tailWord_3600634) baseStart_3600634 baseEnd_3600634 := by
    simpa [prefixWord, tailWord_3600634, baseEnd_3600634] using wordTrace_append hprefix tailTrace_3600634
  have hstable : (prefixWord ++ tailWord_3600634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600634).length < 2 ^ (prefixWord ++ tailWord_3600634).sum := by decide
  have hdescent : baseEnd_3600634 < baseStart_3600634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600638 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3600638 : Nat := 118140960795 + 3600638 * 2 ^ 59
def prefixEnd_3600638 : Nat := 4983230072969 + 3 ^ 40 * 3600638 * 2
def baseEnd_3600638 : Nat := 1232571971229059147310649

theorem tailTrace_3600638 : CollatzResearch.WordTrace tailWord_3600638 prefixEnd_3600638 1232571971229059147310649 := by
  unfold tailWord_3600638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415757091188867607204321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87550704486340627238423045 16415757091188867607204321)
  ·
    refine ⟨12311817818391650705403241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16415757091188867607204321 12311817818391650705403241)
    ·
      refine ⟨9233863363793738029052431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12311817818391650705403241 9233863363793738029052431)
      ·
        refine ⟨13850795045690607043578647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233863363793738029052431 13850795045690607043578647)
        ·
          refine ⟨20776192568535910565367971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13850795045690607043578647 20776192568535910565367971)
          ·
            refine ⟨31164288852803865848051957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20776192568535910565367971 31164288852803865848051957)
            ·
              refine ⟨2921652079950362423254871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31164288852803865848051957 2921652079950362423254871)
              ·
                refine ⟨4382478119925543634882307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921652079950362423254871 4382478119925543634882307)
                ·
                  refine ⟨6573717179888315452323461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382478119925543634882307 6573717179888315452323461)
                  ·
                    refine ⟨1232571971229059147310649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573717179888315452323461 1232571971229059147310649)
                    ·
                      rfl

theorem cell22_3600638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3600638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600638 prefixEnd_3600638 := by exact prefixLift 3600638
  have htrace : WordTrace (prefixWord ++ tailWord_3600638) baseStart_3600638 baseEnd_3600638 := by
    simpa [prefixWord, tailWord_3600638, baseEnd_3600638] using wordTrace_append hprefix tailTrace_3600638
  have hstable : (prefixWord ++ tailWord_3600638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600638).length < 2 ^ (prefixWord ++ tailWord_3600638).sum := by decide
  have hdescent : baseEnd_3600638 < baseStart_3600638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600649 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_3600649 : Nat := 118140960795 + 3600649 * 2 ^ 59
def prefixEnd_3600649 : Nat := 4983230072969 + 3 ^ 40 * 3600649 * 2
def baseEnd_3600649 : Nat := 1232575736753858785285615

theorem tailTrace_3600649 : CollatzResearch.WordTrace tailWord_3600649 prefixEnd_3600649 1232575736753858785285615 := by
  unfold tailWord_3600649
  simp only [CollatzResearch.WordTrace]
  refine ⟨131326457932471089736285001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87550971954980726490856667 131326457932471089736285001)
  ·
    refine ⟨98494843449353317302213751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131326457932471089736285001 98494843449353317302213751)
    ·
      refine ⟨147742265174029975953320627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98494843449353317302213751 147742265174029975953320627)
      ·
        refine ⟨221613397761044963929980941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147742265174029975953320627 221613397761044963929980941)
        ·
          refine ⟨83105024160391861473742853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221613397761044963929980941 83105024160391861473742853)
          ·
            refine ⟨15582192030073474026326785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83105024160391861473742853 15582192030073474026326785)
            ·
              refine ⟨11686644022555105519745089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15582192030073474026326785 11686644022555105519745089)
              ·
                refine ⟨8764983016916329139808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11686644022555105519745089 8764983016916329139808817)
                ·
                  refine ⟨6573737262687246854856613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8764983016916329139808817 6573737262687246854856613)
                  ·
                    refine ⟨1232575736753858785285615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573737262687246854856613 1232575736753858785285615)
                    ·
                      rfl

theorem cell22_3600649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_3600649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600649 prefixEnd_3600649 := by exact prefixLift 3600649
  have htrace : WordTrace (prefixWord ++ tailWord_3600649) baseStart_3600649 baseEnd_3600649 := by
    simpa [prefixWord, tailWord_3600649, baseEnd_3600649] using wordTrace_append hprefix tailTrace_3600649
  have hstable : (prefixWord ++ tailWord_3600649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600649).length < 2 ^ (prefixWord ++ tailWord_3600649).sum := by decide
  have hdescent : baseEnd_3600649 < baseStart_3600649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600651 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 2, 3]
def baseStart_3600651 : Nat := 118140960795 + 3600651 * 2 ^ 59
def prefixEnd_3600651 : Nat := 4983230072969 + 3 ^ 40 * 3600651 * 2
def baseEnd_3600651 : Nat := 1232576421394731446735609

theorem tailTrace_3600651 : CollatzResearch.WordTrace tailWord_3600651 prefixEnd_3600651 1232576421394731446735609 := by
  unfold tailWord_3600651
  simp only [CollatzResearch.WordTrace]
  refine ⟨131326530878463844077857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87551020585642562718571871 131326530878463844077857807)
  ·
    refine ⟨196989796317695766116786711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131326530878463844077857807 196989796317695766116786711)
    ·
      refine ⟨295484694476543649175180067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196989796317695766116786711 295484694476543649175180067)
      ·
        refine ⟨443227041714815473762770101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295484694476543649175180067 443227041714815473762770101)
        ·
          refine ⟨41552535160763950665259697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 443227041714815473762770101 41552535160763950665259697)
          ·
            refine ⟨31164401370572962998944773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41552535160763950665259697 31164401370572962998944773)
            ·
              refine ⟨5843325256982430562302145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31164401370572962998944773 5843325256982430562302145)
              ·
                refine ⟨4382493942736822921726609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843325256982430562302145 4382493942736822921726609)
                ·
                  refine ⟨3286870457052617191294957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4382493942736822921726609 3286870457052617191294957)
                  ·
                    refine ⟨1232576421394731446735609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286870457052617191294957 1232576421394731446735609)
                    ·
                      rfl

theorem cell22_3600651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].length) (baseStart_3600651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600651 prefixEnd_3600651 := by exact prefixLift 3600651
  have htrace : WordTrace (prefixWord ++ tailWord_3600651) baseStart_3600651 baseEnd_3600651 := by
    simpa [prefixWord, tailWord_3600651, baseEnd_3600651] using wordTrace_append hprefix tailTrace_3600651
  have hstable : (prefixWord ++ tailWord_3600651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600651).length < 2 ^ (prefixWord ++ tailWord_3600651).sum := by decide
  have hdescent : baseEnd_3600651 < baseStart_3600651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600799 : List Nat := [1, 1, 2, 5, 1, 1, 1, 10]
def baseStart_3600799 : Nat := 118140960795 + 3600799 * 2 ^ 59
def prefixEnd_3600799 : Nat := 4983230072969 + 3 ^ 40 * 3600799 * 2
def baseEnd_3600799 : Nat := 136958564979923154892795

theorem tailTrace_3600799 : CollatzResearch.WordTrace tailWord_3600799 prefixEnd_3600799 136958564979923154892795 := by
  unfold tailWord_3600799
  simp only [CollatzResearch.WordTrace]
  refine ⟨131331928881927665354245451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87554619254618443569496967 131331928881927665354245451)
  ·
    refine ⟨196997893322891498031368177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131331928881927665354245451 196997893322891498031368177)
    ·
      refine ⟨147748419992168623523526133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196997893322891498031368177 147748419992168623523526133)
      ·
        refine ⟨13851414374265808455330575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147748419992168623523526133 13851414374265808455330575)
        ·
          refine ⟨20777121561398712682995863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13851414374265808455330575 20777121561398712682995863)
          ·
            refine ⟨31165682342098069024493795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20777121561398712682995863 31165682342098069024493795)
            ·
              refine ⟨46748523513147103536740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31165682342098069024493795 46748523513147103536740693)
              ·
                refine ⟨136958564979923154892795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46748523513147103536740693 136958564979923154892795)
                ·
                  rfl

theorem cell22_3600799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 10].length) (baseStart_3600799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600799 prefixEnd_3600799 := by exact prefixLift 3600799
  have htrace : WordTrace (prefixWord ++ tailWord_3600799) baseStart_3600799 baseEnd_3600799 := by
    simpa [prefixWord, tailWord_3600799, baseEnd_3600799] using wordTrace_append hprefix tailTrace_3600799
  have hstable : (prefixWord ++ tailWord_3600799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600799).length < 2 ^ (prefixWord ++ tailWord_3600799).sum := by decide
  have hdescent : baseEnd_3600799 < baseStart_3600799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600850 : List Nat := [3, 2, 2, 4, 1, 1, 3, 6]
def baseStart_3600850 : Nat := 118140960795 + 3600850 * 2 ^ 59
def prefixEnd_3600850 : Nat := 4983230072969 + 3 ^ 40 * 3600850 * 2
def baseEnd_3600850 : Nat := 136960504795729029001111

theorem tailTrace_3600850 : CollatzResearch.WordTrace tailWord_3600850 prefixEnd_3600850 136960504795729029001111 := by
  unfold tailWord_3600850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833447251185725266088001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87555859336495267376234669 32833447251185725266088001)
  ·
    refine ⟨24625085438389293949566001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32833447251185725266088001 24625085438389293949566001)
    ·
      refine ⟨18468814078791970462174501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24625085438389293949566001 18468814078791970462174501)
      ·
        refine ⟨3462902639773494461657719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18468814078791970462174501 3462902639773494461657719)
        ·
          refine ⟨5194353959660241692486579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462902639773494461657719 5194353959660241692486579)
          ·
            refine ⟨7791530939490362538729869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194353959660241692486579 7791530939490362538729869)
            ·
              refine ⟨2921824102308885952023701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7791530939490362538729869 2921824102308885952023701)
              ·
                refine ⟨136960504795729029001111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2921824102308885952023701 136960504795729029001111)
                ·
                  rfl

theorem cell22_3600850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_3600850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600850 prefixEnd_3600850 := by exact prefixLift 3600850
  have htrace : WordTrace (prefixWord ++ tailWord_3600850) baseStart_3600850 baseEnd_3600850 := by
    simpa [prefixWord, tailWord_3600850, baseEnd_3600850] using wordTrace_append hprefix tailTrace_3600850
  have hstable : (prefixWord ++ tailWord_3600850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600850).length < 2 ^ (prefixWord ++ tailWord_3600850).sum := by decide
  have hdescent : baseEnd_3600850 < baseStart_3600850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600861 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3600861 : Nat := 118140960795 + 3600861 * 2 ^ 59
def prefixEnd_3600861 : Nat := 4983230072969 + 3 ^ 40 * 3600861 * 2
def baseEnd_3600861 : Nat := 410882769562120299661655

theorem tailTrace_3600861 : CollatzResearch.WordTrace tailWord_3600861 prefixEnd_3600861 410882769562120299661655 := by
  unfold tailWord_3600861
  simp only [CollatzResearch.WordTrace]
  refine ⟨131334190207703049943002437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87556126805135366628668291 131334190207703049943002437)
  ·
    refine ⟨24625160663944321864312957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131334190207703049943002437 24625160663944321864312957)
    ·
      refine ⟨9234435248979120699117359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24625160663944321864312957 9234435248979120699117359)
      ·
        refine ⟨13851652873468681048676039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234435248979120699117359 13851652873468681048676039)
        ·
          refine ⟨20777479310203021573014059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13851652873468681048676039 20777479310203021573014059)
          ·
            refine ⟨31166218965304532359521089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20777479310203021573014059 31166218965304532359521089)
            ·
              refine ⟨23374664223978399269640817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31166218965304532359521089 23374664223978399269640817)
              ·
                refine ⟨17530998167983799452230613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23374664223978399269640817 17530998167983799452230613)
                ·
                  refine ⟨410882769562120299661655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17530998167983799452230613 410882769562120299661655)
                  ·
                    rfl

theorem cell22_3600861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3600861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600861 prefixEnd_3600861 := by exact prefixLift 3600861
  have htrace : WordTrace (prefixWord ++ tailWord_3600861) baseStart_3600861 baseEnd_3600861 := by
    simpa [prefixWord, tailWord_3600861, baseEnd_3600861] using wordTrace_append hprefix tailTrace_3600861
  have hstable : (prefixWord ++ tailWord_3600861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600861).length < 2 ^ (prefixWord ++ tailWord_3600861).sum := by decide
  have hdescent : baseEnd_3600861 < baseStart_3600861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600865 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3600865 : Nat := 118140960795 + 3600865 * 2 ^ 59
def prefixEnd_3600865 : Nat := 4983230072969 + 3 ^ 40 * 3600865 * 2
def baseEnd_3600865 : Nat := 1232649677968106221884953

theorem tailTrace_3600865 : CollatzResearch.WordTrace tailWord_3600865 prefixEnd_3600865 1232649677968106221884953 := by
  unfold tailWord_3600865
  simp only [CollatzResearch.WordTrace]
  refine ⟨131334336099688558626148049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87556224066459039084098699 131334336099688558626148049)
  ·
    refine ⟨98500752074766418969611037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131334336099688558626148049 98500752074766418969611037)
    ·
      refine ⟨36937782028037407113604139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98500752074766418969611037 36937782028037407113604139)
      ·
        refine ⟨55406673042056110670406209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36937782028037407113604139 55406673042056110670406209)
        ·
          refine ⟨41555004781542083002804657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55406673042056110670406209 41555004781542083002804657)
          ·
            refine ⟨31166253586156562252103493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41555004781542083002804657 31166253586156562252103493)
            ·
              refine ⟨5843672547404355422269405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31166253586156562252103493 5843672547404355422269405)
              ·
                refine ⟨2191377205276633283351027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5843672547404355422269405 2191377205276633283351027)
                ·
                  refine ⟨3287065807914949925026541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191377205276633283351027 3287065807914949925026541)
                  ·
                    refine ⟨1232649677968106221884953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287065807914949925026541 1232649677968106221884953)
                    ·
                      rfl

theorem cell22_3600865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3600865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600865 prefixEnd_3600865 := by exact prefixLift 3600865
  have htrace : WordTrace (prefixWord ++ tailWord_3600865) baseStart_3600865 baseEnd_3600865 := by
    simpa [prefixWord, tailWord_3600865, baseEnd_3600865] using wordTrace_append hprefix tailTrace_3600865
  have hstable : (prefixWord ++ tailWord_3600865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600865).length < 2 ^ (prefixWord ++ tailWord_3600865).sum := by decide
  have hdescent : baseEnd_3600865 < baseStart_3600865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600878 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_3600878 : Nat := 118140960795 + 3600878 * 2 ^ 59
def prefixEnd_3600878 : Nat := 4983230072969 + 3 ^ 40 * 3600878 * 2
def baseEnd_3600878 : Nat := 410884709377926173769971

theorem tailTrace_3600878 : CollatzResearch.WordTrace tailWord_3600878 prefixEnd_3600878 410884709377926173769971 := by
  unfold tailWord_3600878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416851281080182730796411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87556540165760974564247525 16416851281080182730796411)
  ·
    refine ⟨24625276921620274096194617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16416851281080182730796411 24625276921620274096194617)
    ·
      refine ⟨18468957691215205572145963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24625276921620274096194617 18468957691215205572145963)
      ·
        refine ⟨27703436536822808358218945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18468957691215205572145963 27703436536822808358218945)
        ·
          refine ⟨20777577402617106268664209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27703436536822808358218945 20777577402617106268664209)
          ·
            refine ⟨15583183051962829701498157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20777577402617106268664209 15583183051962829701498157)
            ·
              refine ⟨5843693644486061138061809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15583183051962829701498157 5843693644486061138061809)
              ·
                refine ⟨4382770233364545853546357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843693644486061138061809 4382770233364545853546357)
                ·
                  refine ⟨410884709377926173769971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4382770233364545853546357 410884709377926173769971)
                  ·
                    rfl

theorem cell22_3600878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_3600878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600878 prefixEnd_3600878 := by exact prefixLift 3600878
  have htrace : WordTrace (prefixWord ++ tailWord_3600878) baseStart_3600878 baseEnd_3600878 := by
    simpa [prefixWord, tailWord_3600878, baseEnd_3600878] using wordTrace_append hprefix tailTrace_3600878
  have hstable : (prefixWord ++ tailWord_3600878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600878).length < 2 ^ (prefixWord ++ tailWord_3600878).sum := by decide
  have hdescent : baseEnd_3600878 < baseStart_3600878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600906 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3600906 : Nat := 118140960795 + 3600906 * 2 ^ 59
def prefixEnd_3600906 : Nat := 4983230072969 + 3 ^ 40 * 3600906 * 2
def baseEnd_3600906 : Nat := 410887904368665260536609

theorem tailTrace_3600906 : CollatzResearch.WordTrace tailWord_3600906 prefixEnd_3600906 410887904368665260536609 := by
  unfold tailWord_3600906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833957873135005657097643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87557220995026681752260381 32833957873135005657097643)
  ·
    refine ⟨49250936809702508485646465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32833957873135005657097643 49250936809702508485646465)
    ·
      refine ⟨36938202607276881364234849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49250936809702508485646465 36938202607276881364234849)
      ·
        refine ⟨27703651955457661023176137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36938202607276881364234849 27703651955457661023176137)
        ·
          refine ⟨20777738966593245767382103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27703651955457661023176137 20777738966593245767382103)
          ·
            refine ⟨31166608449889868651073155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20777738966593245767382103 31166608449889868651073155)
            ·
              refine ⟨46749912674834802976609733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31166608449889868651073155 46749912674834802976609733)
              ·
                refine ⟨8765608626531525558114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46749912674834802976609733 8765608626531525558114325)
                ·
                  refine ⟨410887904368665260536609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8765608626531525558114325 410887904368665260536609)
                  ·
                    rfl

theorem cell22_3600906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3600906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600906 prefixEnd_3600906 := by exact prefixLift 3600906
  have htrace : WordTrace (prefixWord ++ tailWord_3600906) baseStart_3600906 baseEnd_3600906 := by
    simpa [prefixWord, tailWord_3600906, baseEnd_3600906] using wordTrace_append hprefix tailTrace_3600906
  have hstable : (prefixWord ++ tailWord_3600906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600906).length < 2 ^ (prefixWord ++ tailWord_3600906).sum := by decide
  have hdescent : baseEnd_3600906 < baseStart_3600906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600908 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_3600908 : Nat := 118140960795 + 3600908 * 2 ^ 59
def prefixEnd_3600908 : Nat := 4983230072969 + 3 ^ 40 * 3600908 * 2
def baseEnd_3600908 : Nat := 1232664397746868443059821

theorem tailTrace_3600908 : CollatzResearch.WordTrace tailWord_3600908 prefixEnd_3600908 1232664397746868443059821 := by
  unfold tailWord_3600908
  simp only [CollatzResearch.WordTrace]
  refine ⟨65667952219266388484981689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87557269625688517979975585 65667952219266388484981689)
  ·
    refine ⟨49250964164449791363736267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65667952219266388484981689 49250964164449791363736267)
    ·
      refine ⟨73876446246674687045604401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49250964164449791363736267 73876446246674687045604401)
      ·
        refine ⟨55407334685006015284203301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73876446246674687045604401 55407334685006015284203301)
        ·
          refine ⟨10388875253438627865788119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55407334685006015284203301 10388875253438627865788119)
          ·
            refine ⟨15583312880157941798682179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10388875253438627865788119 15583312880157941798682179)
            ·
              refine ⟨23374969320236912698023269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15583312880157941798682179 23374969320236912698023269)
              ·
                refine ⟨4382806747544421130879363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23374969320236912698023269 4382806747544421130879363)
                ·
                  refine ⟨6574210121316631696319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382806747544421130879363 6574210121316631696319045)
                  ·
                    refine ⟨1232664397746868443059821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574210121316631696319045 1232664397746868443059821)
                    ·
                      rfl

theorem cell22_3600908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_3600908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600908 prefixEnd_3600908 := by exact prefixLift 3600908
  have htrace : WordTrace (prefixWord ++ tailWord_3600908) baseStart_3600908 baseEnd_3600908 := by
    simpa [prefixWord, tailWord_3600908, baseEnd_3600908] using wordTrace_append hprefix tailTrace_3600908
  have hstable : (prefixWord ++ tailWord_3600908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600908).length < 2 ^ (prefixWord ++ tailWord_3600908).sum := by decide
  have hdescent : baseEnd_3600908 < baseStart_3600908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3600951 : List Nat := [1, 1, 3, 1, 2, 3, 4, 7]
def baseStart_3600951 : Nat := 118140960795 + 3600951 * 2 ^ 59
def prefixEnd_3600951 : Nat := 4983230072969 + 3 ^ 40 * 3600951 * 2
def baseEnd_3600951 : Nat := 136964346391736740470521

theorem tailTrace_3600951 : CollatzResearch.WordTrace tailWord_3600951 prefixEnd_3600951 136964346391736740470521 := by
  unfold tailWord_3600951
  simp only [CollatzResearch.WordTrace]
  refine ⟨131337472777376995313778707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87558315184917996875852471 131337472777376995313778707)
  ·
    refine ⟨197006209166065492970668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131337472777376995313778707 197006209166065492970668061)
    ·
      refine ⟨73877328437274559864000523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197006209166065492970668061 73877328437274559864000523)
      ·
        refine ⟨110815992655911839796000785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73877328437274559864000523 110815992655911839796000785)
        ·
          refine ⟨83111994491933879847000589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110815992655911839796000785 83111994491933879847000589)
          ·
            refine ⟨31166997934475204942625221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83111994491933879847000589 31166997934475204942625221)
            ·
              refine ⟨5843812112714100926742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31166997934475204942625221 5843812112714100926742229)
              ·
                refine ⟨136964346391736740470521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5843812112714100926742229 136964346391736740470521)
                ·
                  rfl

theorem cell22_3600951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 7].length) (baseStart_3600951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3600951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3600951 prefixEnd_3600951 := by exact prefixLift 3600951
  have htrace : WordTrace (prefixWord ++ tailWord_3600951) baseStart_3600951 baseEnd_3600951 := by
    simpa [prefixWord, tailWord_3600951, baseEnd_3600951] using wordTrace_append hprefix tailTrace_3600951
  have hstable : (prefixWord ++ tailWord_3600951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3600951).length < 2 ^ (prefixWord ++ tailWord_3600951).sum := by decide
  have hdescent : baseEnd_3600951 < baseStart_3600951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3600951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601034 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3601034 : Nat := 118140960795 + 3601034 * 2 ^ 59
def prefixEnd_3601034 : Nat := 4983230072969 + 3 ^ 40 * 3601034 * 2
def baseEnd_3601034 : Nat := 1232707530121846114409435

theorem tailTrace_3601034 : CollatzResearch.WordTrace tailWord_3601034 prefixEnd_3601034 1232707530121846114409435 := by
  unfold tailWord_3601034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32835125009019075122262539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87560333357384200326033437 32835125009019075122262539)
  ·
    refine ⟨49252687513528612683393809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32835125009019075122262539 49252687513528612683393809)
    ·
      refine ⟨36939515635146459512545357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49252687513528612683393809 36939515635146459512545357)
      ·
        refine ⟨13852318363179922317204509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36939515635146459512545357 13852318363179922317204509)
        ·
          refine ⟨5194619386192470868951691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13852318363179922317204509 5194619386192470868951691)
          ·
            refine ⟨7791929079288706303427537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194619386192470868951691 7791929079288706303427537)
            ·
              refine ⟨5843946809466529727570653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791929079288706303427537 5843946809466529727570653)
              ·
                refine ⟨2191480053549948647838995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5843946809466529727570653 2191480053549948647838995)
                ·
                  refine ⟨3287220080324922971758493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191480053549948647838995 3287220080324922971758493)
                  ·
                    refine ⟨1232707530121846114409435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287220080324922971758493 1232707530121846114409435)
                    ·
                      rfl

theorem cell22_3601034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3601034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601034 prefixEnd_3601034 := by exact prefixLift 3601034
  have htrace : WordTrace (prefixWord ++ tailWord_3601034) baseStart_3601034 baseEnd_3601034 := by
    simpa [prefixWord, tailWord_3601034, baseEnd_3601034] using wordTrace_append hprefix tailTrace_3601034
  have hstable : (prefixWord ++ tailWord_3601034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601034).length < 2 ^ (prefixWord ++ tailWord_3601034).sum := by decide
  have hdescent : baseEnd_3601034 < baseStart_3601034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601043 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 1, 4]
def baseStart_3601043 : Nat := 118140960795 + 3601043 * 2 ^ 59
def prefixEnd_3601043 : Nat := 4983230072969 + 3 ^ 40 * 3601043 * 2
def baseEnd_3601043 : Nat := 1232710611005773090934407

theorem tailTrace_3601043 : CollatzResearch.WordTrace tailWord_3601043 prefixEnd_3601043 1232710611005773090934407 := by
  unfold tailWord_3601043
  simp only [CollatzResearch.WordTrace]
  refine ⟨131340828293043695026127783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87560552195362463350751855 131340828293043695026127783)
  ·
    refine ⟨197011242439565542539191675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131340828293043695026127783 197011242439565542539191675)
    ·
      refine ⟨295516863659348313808787513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197011242439565542539191675 295516863659348313808787513)
      ·
        refine ⟨221637647744511235356590635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295516863659348313808787513 221637647744511235356590635)
        ·
          refine ⟨332456471616766853034885953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221637647744511235356590635 332456471616766853034885953)
          ·
            refine ⟨249342353712575139776164465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332456471616766853034885953 249342353712575139776164465)
            ·
              refine ⟨187006765284431354832123349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249342353712575139776164465 187006765284431354832123349)
              ·
                refine ⟨4382971061353859878877891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187006765284431354832123349 4382971061353859878877891)
                ·
                  refine ⟨6574456592030789818316837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382971061353859878877891 6574456592030789818316837)
                  ·
                    refine ⟨1232710611005773090934407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574456592030789818316837 1232710611005773090934407)
                    ·
                      rfl

theorem cell22_3601043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_3601043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601043 prefixEnd_3601043 := by exact prefixLift 3601043
  have htrace : WordTrace (prefixWord ++ tailWord_3601043) baseStart_3601043 baseEnd_3601043 := by
    simpa [prefixWord, tailWord_3601043, baseEnd_3601043] using wordTrace_append hprefix tailTrace_3601043
  have hstable : (prefixWord ++ tailWord_3601043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601043).length < 2 ^ (prefixWord ++ tailWord_3601043).sum := by decide
  have hdescent : baseEnd_3601043 < baseStart_3601043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601077 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3601077 : Nat := 118140960795 + 3601077 * 2 ^ 59
def prefixEnd_3601077 : Nat := 4983230072969 + 3 ^ 40 * 3601077 * 2
def baseEnd_3601077 : Nat := 1232722249900608335584303

theorem tailTrace_3601077 : CollatzResearch.WordTrace tailWord_3601077 prefixEnd_3601077 1232722249900608335584303 := by
  unfold tailWord_3601077
  simp only [CollatzResearch.WordTrace]
  refine ⟨131342068374920518832865485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87561378916613679221910323 131342068374920518832865485)
  ·
    refine ⟨49253275640595194562324557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131342068374920518832865485 49253275640595194562324557)
    ·
      refine ⟨18469978365223197960871709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49253275640595194562324557 18469978365223197960871709)
      ·
        refine ⟨6926241886958699235326891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18469978365223197960871709 6926241886958699235326891)
        ·
          refine ⟨10389362830438048852990337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926241886958699235326891 10389362830438048852990337)
          ·
            refine ⟨7792022122828536639742753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10389362830438048852990337 7792022122828536639742753)
            ·
              refine ⟨5844016592121402479807065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7792022122828536639742753 5844016592121402479807065)
              ·
                refine ⟨4383012444091051859855299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844016592121402479807065 4383012444091051859855299)
                ·
                  refine ⟨6574518666136577789782949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383012444091051859855299 6574518666136577789782949)
                  ·
                    refine ⟨1232722249900608335584303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574518666136577789782949 1232722249900608335584303)
                    ·
                      rfl

theorem cell22_3601077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3601077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601077 prefixEnd_3601077 := by exact prefixLift 3601077
  have htrace : WordTrace (prefixWord ++ tailWord_3601077) baseStart_3601077 baseEnd_3601077 := by
    simpa [prefixWord, tailWord_3601077, baseEnd_3601077] using wordTrace_append hprefix tailTrace_3601077
  have hstable : (prefixWord ++ tailWord_3601077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601077).length < 2 ^ (prefixWord ++ tailWord_3601077).sum := by decide
  have hdescent : baseEnd_3601077 < baseStart_3601077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601088 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_3601088 : Nat := 118140960795 + 3601088 * 2 ^ 59
def prefixEnd_3601088 : Nat := 4983230072969 + 3 ^ 40 * 3601088 * 2
def baseEnd_3601088 : Nat := 1232726015425407973559269

theorem tailTrace_3601088 : CollatzResearch.WordTrace tailWord_3601088 prefixEnd_3601088 1232726015425407973559269 := by
  unfold tailWord_3601088
  simp only [CollatzResearch.WordTrace]
  refine ⟨65671234788940333855757959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87561646385253778474343945 65671234788940333855757959)
  ·
    refine ⟨98506852183410500783636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65671234788940333855757959 98506852183410500783636939)
    ·
      refine ⟨147760278275115751175455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98506852183410500783636939 147760278275115751175455409)
      ·
        refine ⟨110820208706336813381591557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147760278275115751175455409 110820208706336813381591557)
        ·
          refine ⟨20778789132438152509048417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110820208706336813381591557 20778789132438152509048417)
          ·
            refine ⟨15584091849328614381786313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20778789132438152509048417 15584091849328614381786313)
            ·
              refine ⟨11688068886996460786339735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15584091849328614381786313 11688068886996460786339735)
              ·
                refine ⟨17532103330494691179509603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11688068886996460786339735 17532103330494691179509603)
                ·
                  refine ⟨26298154995742036769264405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17532103330494691179509603 26298154995742036769264405)
                  ·
                    refine ⟨1232726015425407973559269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26298154995742036769264405 1232726015425407973559269)
                    ·
                      rfl

theorem cell22_3601088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_3601088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601088 prefixEnd_3601088 := by exact prefixLift 3601088
  have htrace : WordTrace (prefixWord ++ tailWord_3601088) baseStart_3601088 baseEnd_3601088 := by
    simpa [prefixWord, tailWord_3601088, baseEnd_3601088] using wordTrace_append hprefix tailTrace_3601088
  have hstable : (prefixWord ++ tailWord_3601088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601088).length < 2 ^ (prefixWord ++ tailWord_3601088).sum := by decide
  have hdescent : baseEnd_3601088 < baseStart_3601088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601092 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3601092 : Nat := 118140960795 + 3601092 * 2 ^ 59
def prefixEnd_3601092 : Nat := 4983230072969 + 3 ^ 40 * 3601092 * 2
def baseEnd_3601092 : Nat := 410909128235717765486419

theorem tailTrace_3601092 : CollatzResearch.WordTrace tailWord_3601092 prefixEnd_3601092 410909128235717765486419 := by
  unfold tailWord_3601092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65671307734933088197330765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87561743646577450929774353 65671307734933088197330765)
  ·
    refine ⟨24626740400599908073999037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65671307734933088197330765 24626740400599908073999037)
    ·
      refine ⟨9235027650224965527749639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24626740400599908073999037 9235027650224965527749639)
      ·
        refine ⟨13852541475337448291624459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9235027650224965527749639 13852541475337448291624459)
        ·
          refine ⟨20778812213006172437436689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13852541475337448291624459 20778812213006172437436689)
          ·
            refine ⟨15584109159754629328077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20778812213006172437436689 15584109159754629328077517)
            ·
              refine ⟨5844040934907985998029069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15584109159754629328077517 5844040934907985998029069)
              ·
                refine ⟨2191515350590494749260901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5844040934907985998029069 2191515350590494749260901)
                ·
                  refine ⟨410909128235717765486419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191515350590494749260901 410909128235717765486419)
                  ·
                    rfl

theorem cell22_3601092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3601092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601092 prefixEnd_3601092 := by exact prefixLift 3601092
  have htrace : WordTrace (prefixWord ++ tailWord_3601092) baseStart_3601092 baseEnd_3601092 := by
    simpa [prefixWord, tailWord_3601092, baseEnd_3601092] using wordTrace_append hprefix tailTrace_3601092
  have hstable : (prefixWord ++ tailWord_3601092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601092).length < 2 ^ (prefixWord ++ tailWord_3601092).sum := by decide
  have hdescent : baseEnd_3601092 < baseStart_3601092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601109 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 6]
def baseStart_3601109 : Nat := 118140960795 + 3601109 * 2 ^ 59
def prefixEnd_3601109 : Nat := 4983230072969 + 3 ^ 40 * 3601109 * 2
def baseEnd_3601109 : Nat := 410911068051523639594735

theorem tailTrace_3601109 : CollatzResearch.WordTrace tailWord_3601109 prefixEnd_3601109 410911068051523639594735 := by
  unfold tailWord_3601109
  simp only [CollatzResearch.WordTrace]
  refine ⟨131343235510804588298030381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87562157007203058865353587 131343235510804588298030381)
  ·
    refine ⟨49253713316551720611761393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131343235510804588298030381 49253713316551720611761393)
    ·
      refine ⟨36940284987413790458821045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49253713316551720611761393 36940284987413790458821045)
      ·
        refine ⟨3463151717570042855514473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36940284987413790458821045 3463151717570042855514473)
        ·
          refine ⟨2597363788177532141635855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463151717570042855514473 2597363788177532141635855)
          ·
            refine ⟨3896045682266298212453783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597363788177532141635855 3896045682266298212453783)
            ·
              refine ⟨5844068523399447318680675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896045682266298212453783 5844068523399447318680675)
              ·
                refine ⟨8766102785099170978021013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844068523399447318680675 8766102785099170978021013)
                ·
                  refine ⟨410911068051523639594735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8766102785099170978021013 410911068051523639594735)
                  ·
                    rfl

theorem cell22_3601109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_3601109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601109 prefixEnd_3601109 := by exact prefixLift 3601109
  have htrace : WordTrace (prefixWord ++ tailWord_3601109) baseStart_3601109 baseEnd_3601109 := by
    simpa [prefixWord, tailWord_3601109, baseEnd_3601109] using wordTrace_append hprefix tailTrace_3601109
  have hstable : (prefixWord ++ tailWord_3601109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601109).length < 2 ^ (prefixWord ++ tailWord_3601109).sum := by decide
  have hdescent : baseEnd_3601109 < baseStart_3601109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601124 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_3601124 : Nat := 118140960795 + 3601124 * 2 ^ 59
def prefixEnd_3601124 : Nat := 4983230072969 + 3 ^ 40 * 3601124 * 2
def baseEnd_3601124 : Nat := 1232738338961115879659159

theorem tailTrace_3601124 : CollatzResearch.WordTrace tailWord_3601124 prefixEnd_3601124 1232738338961115879659159 := by
  unfold tailWord_3601124
  simp only [CollatzResearch.WordTrace]
  refine ⟨65671891302875122929913213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87562521737166830573217617 65671891302875122929913213)
  ·
    refine ⟨24626959238578171098717455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65671891302875122929913213 24626959238578171098717455)
    ·
      refine ⟨36940438857867256648076183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24626959238578171098717455 36940438857867256648076183)
      ·
        refine ⟨55410658286800884972114275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36940438857867256648076183 55410658286800884972114275)
        ·
          refine ⟨83115987430201327458171413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55410658286800884972114275 83115987430201327458171413)
          ·
            refine ⟨3896061910790687224601785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83115987430201327458171413 3896061910790687224601785)
            ·
              refine ⟨2922046433093015418451339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896061910790687224601785 2922046433093015418451339)
              ·
                refine ⟨4383069649639523127677009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922046433093015418451339 4383069649639523127677009)
                ·
                  refine ⟨3287302237229642345757757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383069649639523127677009 3287302237229642345757757)
                  ·
                    refine ⟨1232738338961115879659159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287302237229642345757757 1232738338961115879659159)
                    ·
                      rfl

theorem cell22_3601124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_3601124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601124 prefixEnd_3601124 := by exact prefixLift 3601124
  have htrace : WordTrace (prefixWord ++ tailWord_3601124) baseStart_3601124 baseEnd_3601124 := by
    simpa [prefixWord, tailWord_3601124, baseEnd_3601124] using wordTrace_append hprefix tailTrace_3601124
  have hstable : (prefixWord ++ tailWord_3601124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601124).length < 2 ^ (prefixWord ++ tailWord_3601124).sum := by decide
  have hdescent : baseEnd_3601124 < baseStart_3601124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601163 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_3601163 : Nat := 118140960795 + 3601163 * 2 ^ 59
def prefixEnd_3601163 : Nat := 4983230072969 + 3 ^ 40 * 3601163 * 2
def baseEnd_3601163 : Nat := 1232751689458132777934039

theorem tailTrace_3601163 : CollatzResearch.WordTrace tailWord_3601163 prefixEnd_3601163 1232751689458132777934039 := by
  unfold tailWord_3601163
  simp only [CollatzResearch.WordTrace]
  refine ⟨131345205052608955520496143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87563470035072637013664095 131345205052608955520496143)
  ·
    refine ⟨197017807578913433280744215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131345205052608955520496143 197017807578913433280744215)
    ·
      refine ⟨295526711368370149921116323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197017807578913433280744215 295526711368370149921116323)
      ·
        refine ⟨443290067052555224881674485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295526711368370149921116323 443290067052555224881674485)
        ·
          refine ⟨41558443786177052332656983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 443290067052555224881674485 41558443786177052332656983)
          ·
            refine ⟨62337665679265578498985475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41558443786177052332656983 62337665679265578498985475)
            ·
              refine ⟨93506498518898367748478213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62337665679265578498985475 93506498518898367748478213)
              ·
                refine ⟨17532468472293443952839665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93506498518898367748478213 17532468472293443952839665)
                ·
                  refine ⟨13149351354220082964629749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17532468472293443952839665 13149351354220082964629749)
                  ·
                    refine ⟨1232751689458132777934039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13149351354220082964629749 1232751689458132777934039)
                    ·
                      rfl

theorem cell22_3601163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_3601163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601163 prefixEnd_3601163 := by exact prefixLift 3601163
  have htrace : WordTrace (prefixWord ++ tailWord_3601163) baseStart_3601163 baseEnd_3601163 := by
    simpa [prefixWord, tailWord_3601163, baseEnd_3601163] using wordTrace_append hprefix tailTrace_3601163
  have hstable : (prefixWord ++ tailWord_3601163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601163).length < 2 ^ (prefixWord ++ tailWord_3601163).sum := by decide
  have hdescent : baseEnd_3601163 < baseStart_3601163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601169 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_3601169 : Nat := 118140960795 + 3601169 * 2 ^ 59
def prefixEnd_3601169 : Nat := 4983230072969 + 3 ^ 40 * 3601169 * 2
def baseEnd_3601169 : Nat := 1232753743380750762284021

theorem tailTrace_3601169 : CollatzResearch.WordTrace tailWord_3601169 prefixEnd_3601169 1232753743380750762284021 := by
  unfold tailWord_3601169
  simp only [CollatzResearch.WordTrace]
  refine ⟨131345423890587218545214561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87563615927058145696809707 131345423890587218545214561)
  ·
    refine ⟨98509067917940413908910921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131345423890587218545214561 98509067917940413908910921)
    ·
      refine ⟨73881800938455310431683191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98509067917940413908910921 73881800938455310431683191)
      ·
        refine ⟨110822701407682965647524787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73881800938455310431683191 110822701407682965647524787)
        ·
          refine ⟨166234052111524448471287181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110822701407682965647524787 166234052111524448471287181)
          ·
            refine ⟨62337769541821668176732693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166234052111524448471287181 62337769541821668176732693)
            ·
              refine ⟨2922082947272890695784345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62337769541821668176732693 2922082947272890695784345)
              ·
                refine ⟨2191562210454668021838259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922082947272890695784345 2191562210454668021838259)
                ·
                  refine ⟨3287343315682002032757389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191562210454668021838259 3287343315682002032757389)
                  ·
                    refine ⟨1232753743380750762284021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287343315682002032757389 1232753743380750762284021)
                    ·
                      rfl

theorem cell22_3601169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_3601169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601169 prefixEnd_3601169 := by exact prefixLift 3601169
  have htrace : WordTrace (prefixWord ++ tailWord_3601169) baseStart_3601169 baseEnd_3601169 := by
    simpa [prefixWord, tailWord_3601169, baseEnd_3601169] using wordTrace_append hprefix tailTrace_3601169
  have hstable : (prefixWord ++ tailWord_3601169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601169).length < 2 ^ (prefixWord ++ tailWord_3601169).sum := by decide
  have hdescent : baseEnd_3601169 < baseStart_3601169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601180 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3601180 : Nat := 118140960795 + 3601180 * 2 ^ 59
def prefixEnd_3601180 : Nat := 4983230072969 + 3 ^ 40 * 3601180 * 2
def baseEnd_3601180 : Nat := 1232757508905550400258987

theorem tailTrace_3601180 : CollatzResearch.WordTrace tailWord_3601180 prefixEnd_3601180 1232757508905550400258987 := by
  unfold tailWord_3601180
  simp only [CollatzResearch.WordTrace]
  refine ⟨65672912546773683711932497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87563883395698244949243329 65672912546773683711932497)
  ·
    refine ⟨49254684410080262783949373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65672912546773683711932497 49254684410080262783949373)
    ·
      refine ⟨18470506653780098543981015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49254684410080262783949373 18470506653780098543981015)
      ·
        refine ⟨27705759980670147815971523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18470506653780098543981015 27705759980670147815971523)
        ·
          refine ⟨41558639971005221723957285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27705759980670147815971523 41558639971005221723957285)
          ·
            refine ⟨7792244994563479073241991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41558639971005221723957285 7792244994563479073241991)
            ·
              refine ⟨11688367491845218609862987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792244994563479073241991 11688367491845218609862987)
              ·
                refine ⟨17532551237767827914794481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11688367491845218609862987 17532551237767827914794481)
                ·
                  refine ⟨13149413428325870936095861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17532551237767827914794481 13149413428325870936095861)
                  ·
                    refine ⟨1232757508905550400258987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13149413428325870936095861 1232757508905550400258987)
                    ·
                      rfl

theorem cell22_3601180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3601180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601180 prefixEnd_3601180 := by exact prefixLift 3601180
  have htrace : WordTrace (prefixWord ++ tailWord_3601180) baseStart_3601180 baseEnd_3601180 := by
    simpa [prefixWord, tailWord_3601180, baseEnd_3601180] using wordTrace_append hprefix tailTrace_3601180
  have hstable : (prefixWord ++ tailWord_3601180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601180).length < 2 ^ (prefixWord ++ tailWord_3601180).sum := by decide
  have hdescent : baseEnd_3601180 < baseStart_3601180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601193 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 6]
def baseStart_3601193 : Nat := 118140960795 + 3601193 * 2 ^ 59
def prefixEnd_3601193 : Nat := 4983230072969 + 3 ^ 40 * 3601193 * 2
def baseEnd_3601193 : Nat := 410920653023740899894649

theorem tailTrace_3601193 : CollatzResearch.WordTrace tailWord_3601193 prefixEnd_3601193 410920653023740899894649 := by
  unfold tailWord_3601193
  simp only [CollatzResearch.WordTrace]
  refine ⟨131346299242500270644088233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87564199495000180429392155 131346299242500270644088233)
  ·
    refine ⟨98509724431875202983066175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131346299242500270644088233 98509724431875202983066175)
    ·
      refine ⟨147764586647812804474599263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98509724431875202983066175 147764586647812804474599263)
      ·
        refine ⟨221646879971719206711898895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147764586647812804474599263 221646879971719206711898895)
        ·
          refine ⟨332470319957578810067848343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221646879971719206711898895 332470319957578810067848343)
          ·
            refine ⟨498705479936368215101772515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332470319957578810067848343 498705479936368215101772515)
            ·
              refine ⟨748058219904552322652658773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498705479936368215101772515 748058219904552322652658773)
              ·
                refine ⟨8766307264506472531085845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 748058219904552322652658773 8766307264506472531085845)
                ·
                  refine ⟨410920653023740899894649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8766307264506472531085845 410920653023740899894649)
                  ·
                    rfl

theorem cell22_3601193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_3601193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601193 prefixEnd_3601193 := by exact prefixLift 3601193
  have htrace : WordTrace (prefixWord ++ tailWord_3601193) baseStart_3601193 baseEnd_3601193 := by
    simpa [prefixWord, tailWord_3601193, baseEnd_3601193] using wordTrace_append hprefix tailTrace_3601193
  have hstable : (prefixWord ++ tailWord_3601193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601193).length < 2 ^ (prefixWord ++ tailWord_3601193).sum := by decide
  have hdescent : baseEnd_3601193 < baseStart_3601193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601242 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_3601242 : Nat := 118140960795 + 3601242 * 2 ^ 59
def prefixEnd_3601242 : Nat := 4983230072969 + 3 ^ 40 * 3601242 * 2
def baseEnd_3601242 : Nat := 1232778732772602905208797

theorem tailTrace_3601242 : CollatzResearch.WordTrace tailWord_3601242 prefixEnd_3601242 1232778732772602905208797 := by
  unfold tailWord_3601242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837021604830688003155495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87565390946215168008414653 32837021604830688003155495)
  ·
    refine ⟨49255532407246032004733243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32837021604830688003155495 49255532407246032004733243)
    ·
      refine ⟨73883298610869048007099865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49255532407246032004733243 73883298610869048007099865)
      ·
        refine ⟨55412473958151786005324899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73883298610869048007099865 55412473958151786005324899)
        ·
          refine ⟨83118710937227679007987349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55412473958151786005324899 83118710937227679007987349)
          ·
            refine ⟨3896189575182547453499407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83118710937227679007987349 3896189575182547453499407)
            ·
              refine ⟨5844284362773821180249111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896189575182547453499407 5844284362773821180249111)
              ·
                refine ⟨8766426544160731770373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844284362773821180249111 8766426544160731770373667)
                ·
                  refine ⟨13149639816241097655560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766426544160731770373667 13149639816241097655560501)
                  ·
                    refine ⟨1232778732772602905208797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13149639816241097655560501 1232778732772602905208797)
                    ·
                      rfl

theorem cell22_3601242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_3601242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601242 prefixEnd_3601242 := by exact prefixLift 3601242
  have htrace : WordTrace (prefixWord ++ tailWord_3601242) baseStart_3601242 baseEnd_3601242 := by
    simpa [prefixWord, tailWord_3601242, baseEnd_3601242] using wordTrace_append hprefix tailTrace_3601242
  have hstable : (prefixWord ++ tailWord_3601242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601242).length < 2 ^ (prefixWord ++ tailWord_3601242).sum := by decide
  have hdescent : baseEnd_3601242 < baseStart_3601242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601255 : List Nat := [1, 1, 5, 1, 2, 3, 1, 8]
def baseStart_3601255 : Nat := 118140960795 + 3601255 * 2 ^ 59
def prefixEnd_3601255 : Nat := 4983230072969 + 3 ^ 40 * 3601255 * 2
def baseEnd_3601255 : Nat := 136975909215363911625973

theorem tailTrace_3601255 : CollatzResearch.WordTrace tailWord_3601255 prefixEnd_3601255 136975909215363911625973 := by
  unfold tailWord_3601255
  simp only [CollatzResearch.WordTrace]
  refine ⟨131348560568275655232845219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87565707045517103488563479 131348560568275655232845219)
  ·
    refine ⟨197022840852413482849267829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131348560568275655232845219 197022840852413482849267829)
    ·
      refine ⟨18470891329913764017118859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197022840852413482849267829 18470891329913764017118859)
      ·
        refine ⟨27706336994870646025678289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18470891329913764017118859 27706336994870646025678289)
        ·
          refine ⟨20779752746152984519258717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27706336994870646025678289 20779752746152984519258717)
          ·
            refine ⟨7792407279807369194722019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20779752746152984519258717 7792407279807369194722019)
            ·
              refine ⟨11688610919711053792083029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792407279807369194722019 11688610919711053792083029)
              ·
                refine ⟨136975909215363911625973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11688610919711053792083029 136975909215363911625973)
                ·
                  rfl

theorem cell22_3601255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 8].length) (baseStart_3601255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601255 prefixEnd_3601255 := by exact prefixLift 3601255
  have htrace : WordTrace (prefixWord ++ tailWord_3601255) baseStart_3601255 baseEnd_3601255 := by
    simpa [prefixWord, tailWord_3601255, baseEnd_3601255] using wordTrace_append hprefix tailTrace_3601255
  have hstable : (prefixWord ++ tailWord_3601255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601255).length < 2 ^ (prefixWord ++ tailWord_3601255).sum := by decide
  have hdescent : baseEnd_3601255 < baseStart_3601255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601278 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3601278 : Nat := 118140960795 + 3601278 * 2 ^ 59
def prefixEnd_3601278 : Nat := 4983230072969 + 3 ^ 40 * 3601278 * 2
def baseEnd_3601278 : Nat := 410930352102770270436229

theorem tailTrace_3601278 : CollatzResearch.WordTrace tailWord_3601278 prefixEnd_3601278 410930352102770270436229 := by
  unfold tailWord_3601278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16418674930899041270116561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87566266298128220107288325 16418674930899041270116561)
  ·
    refine ⟨12314006198174280952587421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16418674930899041270116561 12314006198174280952587421)
    ·
      refine ⟨4617752324315355357220283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12314006198174280952587421 4617752324315355357220283)
      ·
        refine ⟨6926628486473033035830425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617752324315355357220283 6926628486473033035830425)
        ·
          refine ⟨5194971364854774776872819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6926628486473033035830425 5194971364854774776872819)
          ·
            refine ⟨7792457047282162165309229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194971364854774776872819 7792457047282162165309229)
            ·
              refine ⟨2922171392730810811990961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7792457047282162165309229 2922171392730810811990961)
              ·
                refine ⟨2191628544548108108993221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922171392730810811990961 2191628544548108108993221)
                ·
                  refine ⟨410930352102770270436229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191628544548108108993221 410930352102770270436229)
                  ·
                    rfl

theorem cell22_3601278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3601278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601278 prefixEnd_3601278 := by exact prefixLift 3601278
  have htrace : WordTrace (prefixWord ++ tailWord_3601278) baseStart_3601278 baseEnd_3601278 := by
    simpa [prefixWord, tailWord_3601278, baseEnd_3601278] using wordTrace_append hprefix tailTrace_3601278
  have hstable : (prefixWord ++ tailWord_3601278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601278).length < 2 ^ (prefixWord ++ tailWord_3601278).sum := by decide
  have hdescent : baseEnd_3601278 < baseStart_3601278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601362 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3601362 : Nat := 118140960795 + 3601362 * 2 ^ 59
def prefixEnd_3601362 : Nat := 4983230072969 + 3 ^ 40 * 3601362 * 2
def baseEnd_3601362 : Nat := 410939937074987530736143

theorem tailTrace_3601362 : CollatzResearch.WordTrace tailWord_3601362 prefixEnd_3601362 410939937074987530736143 := by
  unfold tailWord_3601362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32838115794722003126747585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87568308785925341671326893 32838115794722003126747585)
  ·
    refine ⟨24628586846041502345060689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32838115794722003126747585 24628586846041502345060689)
    ·
      refine ⟨18471440134531126758795517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24628586846041502345060689 18471440134531126758795517)
      ·
        refine ⟨6926790050449172534548319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18471440134531126758795517 6926790050449172534548319)
        ·
          refine ⟨10390185075673758801822479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926790050449172534548319 10390185075673758801822479)
          ·
            refine ⟨15585277613510638202733719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390185075673758801822479 15585277613510638202733719)
            ·
              refine ⟨23377916420265957304100579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15585277613510638202733719 23377916420265957304100579)
              ·
                refine ⟨35066874630398935956150869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23377916420265957304100579 35066874630398935956150869)
                ·
                  refine ⟨410939937074987530736143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35066874630398935956150869 410939937074987530736143)
                  ·
                    rfl

theorem cell22_3601362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3601362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601362 prefixEnd_3601362 := by exact prefixLift 3601362
  have htrace : WordTrace (prefixWord ++ tailWord_3601362) baseStart_3601362 baseEnd_3601362 := by
    simpa [prefixWord, tailWord_3601362, baseEnd_3601362] using wordTrace_append hprefix tailTrace_3601362
  have hstable : (prefixWord ++ tailWord_3601362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601362).length < 2 ^ (prefixWord ++ tailWord_3601362).sum := by decide
  have hdescent : baseEnd_3601362 < baseStart_3601362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601377 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3601377 : Nat := 118140960795 + 3601377 * 2 ^ 59
def prefixEnd_3601377 : Nat := 4983230072969 + 3 ^ 40 * 3601377 * 2
def baseEnd_3601377 : Nat := 1232824946031507553083383

theorem tailTrace_3601377 : CollatzResearch.WordTrace tailWord_3601377 prefixEnd_3601377 1232824946031507553083383 := by
  unfold tailWord_3601377
  simp only [CollatzResearch.WordTrace]
  refine ⟨131353010273833670068786385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87568673515889113379190923 131353010273833670068786385)
  ·
    refine ⟨98514757705375252551589789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131353010273833670068786385 98514757705375252551589789)
    ·
      refine ⟨36943034139515719706846171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98514757705375252551589789 36943034139515719706846171)
      ·
        refine ⟨55414551209273579560269257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36943034139515719706846171 55414551209273579560269257)
        ·
          refine ⟨41560913406955184670201943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55414551209273579560269257 41560913406955184670201943)
          ·
            refine ⟨62341370110432777005302915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41560913406955184670201943 62341370110432777005302915)
            ·
              refine ⟨93512055165649165507954373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62341370110432777005302915 93512055165649165507954373)
              ·
                refine ⟨17533510343559218532741445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93512055165649165507954373 17533510343559218532741445)
                ·
                  refine ⟨3287533189417353474889021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17533510343559218532741445 3287533189417353474889021)
                  ·
                    refine ⟨1232824946031507553083383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287533189417353474889021 1232824946031507553083383)
                    ·
                      rfl

theorem cell22_3601377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3601377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601377 prefixEnd_3601377 := by exact prefixLift 3601377
  have htrace : WordTrace (prefixWord ++ tailWord_3601377) baseStart_3601377 baseEnd_3601377 := by
    simpa [prefixWord, tailWord_3601377, baseEnd_3601377] using wordTrace_append hprefix tailTrace_3601377
  have hstable : (prefixWord ++ tailWord_3601377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601377).length < 2 ^ (prefixWord ++ tailWord_3601377).sum := by decide
  have hdescent : baseEnd_3601377 < baseStart_3601377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601379 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 4]
def baseStart_3601379 : Nat := 118140960795 + 3601379 * 2 ^ 59
def prefixEnd_3601379 : Nat := 4983230072969 + 3 ^ 40 * 3601379 * 2
def baseEnd_3601379 : Nat := 410941876890793404844459

theorem tailTrace_3601379 : CollatzResearch.WordTrace tailWord_3601379 prefixEnd_3601379 410941876890793404844459 := by
  unfold tailWord_3601379
  simp only [CollatzResearch.WordTrace]
  refine ⟨131353083219826424410359191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87568722146550949606906127 131353083219826424410359191)
  ·
    refine ⟨197029624829739636615538787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131353083219826424410359191 197029624829739636615538787)
    ·
      refine ⟨295544437244609454923308181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197029624829739636615538787 295544437244609454923308181)
      ·
        refine ⟨13853645495841068199530071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295544437244609454923308181 13853645495841068199530071)
        ·
          refine ⟨20780468243761602299295107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13853645495841068199530071 20780468243761602299295107)
          ·
            refine ⟨31170702365642403448942661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20780468243761602299295107 31170702365642403448942661)
            ·
              refine ⟨5844506693557950646676749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31170702365642403448942661 5844506693557950646676749)
              ·
                refine ⟨2191690010084231492503781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5844506693557950646676749 2191690010084231492503781)
                ·
                  refine ⟨410941876890793404844459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191690010084231492503781 410941876890793404844459)
                  ·
                    rfl

theorem cell22_3601379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 4].length) (baseStart_3601379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601379 prefixEnd_3601379 := by exact prefixLift 3601379
  have htrace : WordTrace (prefixWord ++ tailWord_3601379) baseStart_3601379 baseEnd_3601379 := by
    simpa [prefixWord, tailWord_3601379, baseEnd_3601379] using wordTrace_append hprefix tailTrace_3601379
  have hstable : (prefixWord ++ tailWord_3601379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601379).length < 2 ^ (prefixWord ++ tailWord_3601379).sum := by decide
  have hdescent : baseEnd_3601379 < baseStart_3601379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601381 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_3601381 : Nat := 118140960795 + 3601381 * 2 ^ 59
def prefixEnd_3601381 : Nat := 4983230072969 + 3 ^ 40 * 3601381 * 2
def baseEnd_3601381 : Nat := 1232826315313252875983371

theorem tailTrace_3601381 : CollatzResearch.WordTrace tailWord_3601381 prefixEnd_3601381 1232826315313252875983371 := by
  unfold tailWord_3601381
  simp only [CollatzResearch.WordTrace]
  refine ⟨131353156165819178751931997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87568770777212785834621331 131353156165819178751931997)
  ·
    refine ⟨49257433562182192031974499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131353156165819178751931997 49257433562182192031974499)
    ·
      refine ⟨73886150343273288047961749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49257433562182192031974499 73886150343273288047961749)
      ·
        refine ⟨3463413297340935377248207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73886150343273288047961749 3463413297340935377248207)
        ·
          refine ⟨5195119946011403065872311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463413297340935377248207 5195119946011403065872311)
          ·
            refine ⟨7792679919017104598808467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195119946011403065872311 7792679919017104598808467)
            ·
              refine ⟨11689019878525656898212701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792679919017104598808467 11689019878525656898212701)
              ·
                refine ⟨4383382454447121336829763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11689019878525656898212701 4383382454447121336829763)
                ·
                  refine ⟨6575073681670682005244645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383382454447121336829763 6575073681670682005244645)
                  ·
                    refine ⟨1232826315313252875983371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575073681670682005244645 1232826315313252875983371)
                    ·
                      rfl

theorem cell22_3601381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_3601381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601381 prefixEnd_3601381 := by exact prefixLift 3601381
  have htrace : WordTrace (prefixWord ++ tailWord_3601381) baseStart_3601381 baseEnd_3601381 := by
    simpa [prefixWord, tailWord_3601381, baseEnd_3601381] using wordTrace_append hprefix tailTrace_3601381
  have hstable : (prefixWord ++ tailWord_3601381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601381).length < 2 ^ (prefixWord ++ tailWord_3601381).sum := by decide
  have hdescent : baseEnd_3601381 < baseStart_3601381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601452 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_3601452 : Nat := 118140960795 + 3601452 * 2 ^ 59
def prefixEnd_3601452 : Nat := 4983230072969 + 3 ^ 40 * 3601452 * 2
def baseEnd_3601452 : Nat := 410950206688077452486051

theorem tailTrace_3601452 : CollatzResearch.WordTrace tailWord_3601452 prefixEnd_3601452 410950206688077452486051 := by
  unfold tailWord_3601452
  simp only [CollatzResearch.WordTrace]
  refine ⟨65677872874280978938883305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87570497165707971918511073 65677872874280978938883305)
  ·
    refine ⟨49258404655710734204162479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65677872874280978938883305 49258404655710734204162479)
    ·
      refine ⟨73887606983566101306243719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49258404655710734204162479 73887606983566101306243719)
      ·
        refine ⟨110831410475349151959365579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73887606983566101306243719 110831410475349151959365579)
        ·
          refine ⟨166247115713023727939048369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110831410475349151959365579 166247115713023727939048369)
          ·
            refine ⟨124685336784767795954286277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166247115713023727939048369 124685336784767795954286277)
            ·
              refine ⟨23378500647143961741428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124685336784767795954286277 23378500647143961741428677)
              ·
                refine ⟨4383468871339492826517877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23378500647143961741428677 4383468871339492826517877)
                ·
                  refine ⟨410950206688077452486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4383468871339492826517877 410950206688077452486051)
                  ·
                    rfl

theorem cell22_3601452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_3601452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601452 prefixEnd_3601452 := by exact prefixLift 3601452
  have htrace : WordTrace (prefixWord ++ tailWord_3601452) baseStart_3601452 baseEnd_3601452 := by
    simpa [prefixWord, tailWord_3601452, baseEnd_3601452] using wordTrace_append hprefix tailTrace_3601452
  have hstable : (prefixWord ++ tailWord_3601452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601452).length < 2 ^ (prefixWord ++ tailWord_3601452).sum := by decide
  have hdescent : baseEnd_3601452 < baseStart_3601452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601469 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 5]
def baseStart_3601469 : Nat := 118140960795 + 3601469 * 2 ^ 59
def prefixEnd_3601469 : Nat := 4983230072969 + 3 ^ 40 * 3601469 * 2
def baseEnd_3601469 : Nat := 410952146503883326594367

theorem tailTrace_3601469 : CollatzResearch.WordTrace tailWord_3601469 prefixEnd_3601469 410952146503883326594367 := by
  unfold tailWord_3601469
  simp only [CollatzResearch.WordTrace]
  refine ⟨131356365789500369781135461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87570910526333579854090307 131356365789500369781135461)
  ·
    refine ⟨24629318585531319333962899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131356365789500369781135461 24629318585531319333962899)
    ·
      refine ⟨36943977878296979000944349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24629318585531319333962899 36943977878296979000944349)
      ·
        refine ⟨13853991704361367125354131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36943977878296979000944349 13853991704361367125354131)
        ·
          refine ⟨20780987556542050688031197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13853991704361367125354131 20780987556542050688031197)
          ·
            refine ⟨7792870333703269008011699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20780987556542050688031197 7792870333703269008011699)
            ·
              refine ⟨11689305500554903512017549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792870333703269008011699 11689305500554903512017549)
              ·
                refine ⟨4383489562708088817006581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11689305500554903512017549 4383489562708088817006581)
                ·
                  refine ⟨410952146503883326594367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4383489562708088817006581 410952146503883326594367)
                  ·
                    rfl

theorem cell22_3601469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_3601469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601469 prefixEnd_3601469 := by exact prefixLift 3601469
  have htrace : WordTrace (prefixWord ++ tailWord_3601469) baseStart_3601469 baseEnd_3601469 := by
    simpa [prefixWord, tailWord_3601469, baseEnd_3601469] using wordTrace_append hprefix tailTrace_3601469
  have hstable : (prefixWord ++ tailWord_3601469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601469).length < 2 ^ (prefixWord ++ tailWord_3601469).sum := by decide
  have hdescent : baseEnd_3601469 < baseStart_3601469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601527 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3601527 : Nat := 118140960795 + 3601527 * 2 ^ 59
def prefixEnd_3601527 : Nat := 4983230072969 + 3 ^ 40 * 3601527 * 2
def baseEnd_3601527 : Nat := 1232876294096957161832923

theorem tailTrace_3601527 : CollatzResearch.WordTrace tailWord_3601527 prefixEnd_3601527 1232876294096957161832923 := by
  unfold tailWord_3601527
  simp only [CollatzResearch.WordTrace]
  refine ⟨131358481223290245686746835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87572320815526830457831223 131358481223290245686746835)
  ·
    refine ⟨197037721834935368530120253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131358481223290245686746835 197037721834935368530120253)
    ·
      refine ⟨73889145688100763198795095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197037721834935368530120253 73889145688100763198795095)
      ·
        refine ⟨110833718532151144798192643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73889145688100763198795095 110833718532151144798192643)
        ·
          refine ⟨166250577798226717197288965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110833718532151144798192643 166250577798226717197288965)
          ·
            refine ⟨31171983337167509474491681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166250577798226717197288965 31171983337167509474491681)
            ·
              refine ⟨23378987502875632105868761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31171983337167509474491681 23378987502875632105868761)
              ·
                refine ⟨17534240627156724079401571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23378987502875632105868761 17534240627156724079401571)
                ·
                  refine ⟨26301360940735086119102357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17534240627156724079401571 26301360940735086119102357)
                  ·
                    refine ⟨1232876294096957161832923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26301360940735086119102357 1232876294096957161832923)
                    ·
                      rfl

theorem cell22_3601527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3601527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601527 prefixEnd_3601527 := by exact prefixLift 3601527
  have htrace : WordTrace (prefixWord ++ tailWord_3601527) baseStart_3601527 baseEnd_3601527 := by
    simpa [prefixWord, tailWord_3601527, baseEnd_3601527] using wordTrace_append hprefix tailTrace_3601527
  have hstable : (prefixWord ++ tailWord_3601527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601527).length < 2 ^ (prefixWord ++ tailWord_3601527).sum := by decide
  have hdescent : baseEnd_3601527 < baseStart_3601527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601608 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_3601608 : Nat := 118140960795 + 3601608 * 2 ^ 59
def prefixEnd_3601608 : Nat := 4983230072969 + 3 ^ 40 * 3601608 * 2
def baseEnd_3601608 : Nat := 1232904022052299950557675

theorem tailTrace_3601608 : CollatzResearch.WordTrace tailWord_3601608 prefixEnd_3601608 1232904022052299950557675 := by
  unfold tailWord_3601608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65680717767998398260222739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87574290357331197680296985 65680717767998398260222739)
  ·
    refine ⟨98521076651997597390334109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65680717767998398260222739 98521076651997597390334109)
    ·
      refine ⟨36945403744499099021375291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98521076651997597390334109 36945403744499099021375291)
      ·
        refine ⟨55418105616748648532062937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36945403744499099021375291 55418105616748648532062937)
        ·
          refine ⟨41563579212561486399047203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55418105616748648532062937 41563579212561486399047203)
          ·
            refine ⟨62345368818842229598570805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41563579212561486399047203 62345368818842229598570805)
            ·
              refine ⟨5844878326766459024866013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62345368818842229598570805 5844878326766459024866013)
              ·
                refine ⟨2191829372537422134324755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5844878326766459024866013 2191829372537422134324755)
                ·
                  refine ⟨3287744058806133201487133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191829372537422134324755 3287744058806133201487133)
                  ·
                    refine ⟨1232904022052299950557675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287744058806133201487133 1232904022052299950557675)
                    ·
                      rfl

theorem cell22_3601608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_3601608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601608 prefixEnd_3601608 := by exact prefixLift 3601608
  have htrace : WordTrace (prefixWord ++ tailWord_3601608) baseStart_3601608 baseEnd_3601608 := by
    simpa [prefixWord, tailWord_3601608, baseEnd_3601608] using wordTrace_append hprefix tailTrace_3601608
  have hstable : (prefixWord ++ tailWord_3601608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601608).length < 2 ^ (prefixWord ++ tailWord_3601608).sum := by decide
  have hdescent : baseEnd_3601608 < baseStart_3601608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601651 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 1, 4]
def baseStart_3601651 : Nat := 118140960795 + 3601651 * 2 ^ 59
def prefixEnd_3601651 : Nat := 4983230072969 + 3 ^ 40 * 3601651 * 2
def baseEnd_3601651 : Nat := 1232918741831062171732543

theorem tailTrace_3601651 : CollatzResearch.WordTrace tailWord_3601651 prefixEnd_3601651 1232918741831062171732543 := by
  unfold tailWord_3601651
  simp only [CollatzResearch.WordTrace]
  refine ⟨131363003874841014864260807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87575335916560676576173871 131363003874841014864260807)
  ·
    refine ⟨197044505812261522296391211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131363003874841014864260807 197044505812261522296391211)
    ·
      refine ⟨295566758718392283444586817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197044505812261522296391211 295566758718392283444586817)
      ·
        refine ⟨221675069038794212583440113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295566758718392283444586817 221675069038794212583440113)
        ·
          refine ⟨166256301779095659437580085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221675069038794212583440113 166256301779095659437580085)
          ·
            refine ⟨15586528291790218072273133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166256301779095659437580085 15586528291790218072273133)
            ·
              refine ⟨5844948109421331777102425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15586528291790218072273133 5844948109421331777102425)
              ·
                refine ⟨4383711082065998832826819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844948109421331777102425 4383711082065998832826819)
                ·
                  refine ⟨6575566623098998249240229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383711082065998832826819 6575566623098998249240229)
                  ·
                    refine ⟨1232918741831062171732543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575566623098998249240229 1232918741831062171732543)
                    ·
                      rfl

theorem cell22_3601651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_3601651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601651 prefixEnd_3601651 := by exact prefixLift 3601651
  have htrace : WordTrace (prefixWord ++ tailWord_3601651) baseStart_3601651 baseEnd_3601651 := by
    simpa [prefixWord, tailWord_3601651, baseEnd_3601651] using wordTrace_append hprefix tailTrace_3601651
  have hstable : (prefixWord ++ tailWord_3601651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601651).length < 2 ^ (prefixWord ++ tailWord_3601651).sum := by decide
  have hdescent : baseEnd_3601651 < baseStart_3601651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601698 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3601698 : Nat := 118140960795 + 3601698 * 2 ^ 59
def prefixEnd_3601698 : Nat := 4983230072969 + 3 ^ 40 * 3601698 * 2
def baseEnd_3601698 : Nat := 1232934830891569715807399

theorem tailTrace_3601698 : CollatzResearch.WordTrace tailWord_3601698 prefixEnd_3601698 1232934830891569715807399 := by
  unfold tailWord_3601698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32841179526417685472805437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87576478737113827927481165 32841179526417685472805437)
  ·
    refine ⟨12315442322406632052302039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32841179526417685472805437 12315442322406632052302039)
    ·
      refine ⟨18473163483609948078453059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315442322406632052302039 18473163483609948078453059)
      ·
        refine ⟨27709745225414922117679589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18473163483609948078453059 27709745225414922117679589)
        ·
          refine ⟨5195577229765297897064923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27709745225414922117679589 5195577229765297897064923)
          ·
            refine ⟨7793365844647946845597385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195577229765297897064923 7793365844647946845597385)
            ·
              refine ⟨5845024383485960134198039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7793365844647946845597385 5845024383485960134198039)
              ·
                refine ⟨8767536575228940201297059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845024383485960134198039 8767536575228940201297059)
                ·
                  refine ⟨13151304862843410301945589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8767536575228940201297059 13151304862843410301945589)
                  ·
                    refine ⟨1232934830891569715807399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13151304862843410301945589 1232934830891569715807399)
                    ·
                      rfl

theorem cell22_3601698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3601698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601698 prefixEnd_3601698 := by exact prefixLift 3601698
  have htrace : WordTrace (prefixWord ++ tailWord_3601698) baseStart_3601698 baseEnd_3601698 := by
    simpa [prefixWord, tailWord_3601698, baseEnd_3601698] using wordTrace_append hprefix tailTrace_3601698
  have hstable : (prefixWord ++ tailWord_3601698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601698).length < 2 ^ (prefixWord ++ tailWord_3601698).sum := by decide
  have hdescent : baseEnd_3601698 < baseStart_3601698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601713 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3601713 : Nat := 118140960795 + 3601713 * 2 ^ 59
def prefixEnd_3601713 : Nat := 4983230072969 + 3 ^ 40 * 3601713 * 2
def baseEnd_3601713 : Nat := 1232939965698114676682353

theorem tailTrace_3601713 : CollatzResearch.WordTrace tailWord_3601713 prefixEnd_3601713 1232939965698114676682353 := by
  unfold tailWord_3601713
  simp only [CollatzResearch.WordTrace]
  refine ⟨131365265200616399453017793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87576843467077599635345195 131365265200616399453017793)
  ·
    refine ⟨98523948900462299589763345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131365265200616399453017793 98523948900462299589763345)
    ·
      refine ⟨73892961675346724692322509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98523948900462299589763345 73892961675346724692322509)
      ·
        refine ⟨27709860628255021759620941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73892961675346724692322509 27709860628255021759620941)
        ·
          refine ⟨10391197735595633159857853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27709860628255021759620941 10391197735595633159857853)
          ·
            refine ⟨3896699150848362434946695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10391197735595633159857853 3896699150848362434946695)
            ·
              refine ⟨5845048726272543652420043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896699150848362434946695 5845048726272543652420043)
              ·
                refine ⟨8767573089408815478630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845048726272543652420043 8767573089408815478630065)
                ·
                  refine ⟨6575679817056611608972549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8767573089408815478630065 6575679817056611608972549)
                  ·
                    refine ⟨1232939965698114676682353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575679817056611608972549 1232939965698114676682353)
                    ·
                      rfl

theorem cell22_3601713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3601713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601713 prefixEnd_3601713 := by exact prefixLift 3601713
  have htrace : WordTrace (prefixWord ++ tailWord_3601713) baseStart_3601713 baseEnd_3601713 := by
    simpa [prefixWord, tailWord_3601713, baseEnd_3601713] using wordTrace_append hprefix tailTrace_3601713
  have hstable : (prefixWord ++ tailWord_3601713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601713).length < 2 ^ (prefixWord ++ tailWord_3601713).sum := by decide
  have hdescent : baseEnd_3601713 < baseStart_3601713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601732 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3601732 : Nat := 118140960795 + 3601732 * 2 ^ 59
def prefixEnd_3601732 : Nat := 4983230072969 + 3 ^ 40 * 3601732 * 2
def baseEnd_3601732 : Nat := 1232946469786404960457295

theorem tailTrace_3601732 : CollatzResearch.WordTrace tailWord_3601732 prefixEnd_3601732 1232946469786404960457295 := by
  unfold tailWord_3601732
  simp only [CollatzResearch.WordTrace]
  refine ⟨65682979093773782848979725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87577305458365043798639633 65682979093773782848979725)
  ·
    refine ⟨24631117160165168568367397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65682979093773782848979725 24631117160165168568367397)
    ·
      refine ⟨4618334467530969106568887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24631117160165168568367397 4618334467530969106568887)
      ·
        refine ⟨6927501701296453659853331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618334467530969106568887 6927501701296453659853331)
        ·
          refine ⟨10391252551944680489779997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927501701296453659853331 10391252551944680489779997)
          ·
            refine ⟨3896719706979255183667499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10391252551944680489779997 3896719706979255183667499)
            ·
              refine ⟨5845079560468882775501249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896719706979255183667499 5845079560468882775501249)
              ·
                refine ⟨4383809670351662081625937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845079560468882775501249 4383809670351662081625937)
                ·
                  refine ⟨3287857252763746561219453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383809670351662081625937 3287857252763746561219453)
                  ·
                    refine ⟨1232946469786404960457295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287857252763746561219453 1232946469786404960457295)
                    ·
                      rfl

theorem cell22_3601732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3601732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601732 prefixEnd_3601732 := by exact prefixLift 3601732
  have htrace : WordTrace (prefixWord ++ tailWord_3601732) baseStart_3601732 baseEnd_3601732 := by
    simpa [prefixWord, tailWord_3601732, baseEnd_3601732] using wordTrace_append hprefix tailTrace_3601732
  have hstable : (prefixWord ++ tailWord_3601732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601732).length < 2 ^ (prefixWord ++ tailWord_3601732).sum := by decide
  have hdescent : baseEnd_3601732 < baseStart_3601732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601820 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3601820 : Nat := 118140960795 + 3601820 * 2 ^ 59
def prefixEnd_3601820 : Nat := 4983230072969 + 3 ^ 40 * 3601820 * 2
def baseEnd_3601820 : Nat := 1232976593984802064257025

theorem tailTrace_3601820 : CollatzResearch.WordTrace tailWord_3601820 prefixEnd_3601820 1232976593984802064257025 := by
  unfold tailWord_3601820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65684583905614378363581457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87579445207485837818108609 65684583905614378363581457)
  ·
    refine ⟨49263437929210783772686093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65684583905614378363581457 49263437929210783772686093)
    ·
      refine ⟨18473789223454043914757285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49263437929210783772686093 18473789223454043914757285)
      ·
        refine ⟨3463835479397633234016991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18473789223454043914757285 3463835479397633234016991)
        ·
          refine ⟨5195753219096449851025487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463835479397633234016991 5195753219096449851025487)
          ·
            refine ⟨7793629828644674776538231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195753219096449851025487 7793629828644674776538231)
            ·
              refine ⟨11690444742967012164807347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793629828644674776538231 11690444742967012164807347)
              ·
                refine ⟨17535667114450518247211021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690444742967012164807347 17535667114450518247211021)
                ·
                  refine ⟨6575875167918944342704133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17535667114450518247211021 6575875167918944342704133)
                  ·
                    refine ⟨1232976593984802064257025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575875167918944342704133 1232976593984802064257025)
                    ·
                      rfl

theorem cell22_3601820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3601820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601820 prefixEnd_3601820 := by exact prefixLift 3601820
  have htrace : WordTrace (prefixWord ++ tailWord_3601820) baseStart_3601820 baseEnd_3601820 := by
    simpa [prefixWord, tailWord_3601820, baseEnd_3601820] using wordTrace_append hprefix tailTrace_3601820
  have hstable : (prefixWord ++ tailWord_3601820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601820).length < 2 ^ (prefixWord ++ tailWord_3601820).sum := by decide
  have hdescent : baseEnd_3601820 < baseStart_3601820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601837 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3601837 : Nat := 118140960795 + 3601837 * 2 ^ 59
def prefixEnd_3601837 : Nat := 4983230072969 + 3 ^ 40 * 3601837 * 2
def baseEnd_3601837 : Nat := 1232982413432219686581973

theorem tailTrace_3601837 : CollatzResearch.WordTrace tailWord_3601837 prefixEnd_3601837 1232982413432219686581973 := by
  unfold tailWord_3601837
  simp only [CollatzResearch.WordTrace]
  refine ⟨131369787852167168630531765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87579858568111445753687843 131369787852167168630531765)
  ·
    refine ⟨12315917611140672059112353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131369787852167168630531765 12315917611140672059112353)
    ·
      refine ⟨9236938208355504044334265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12315917611140672059112353 9236938208355504044334265)
      ·
        refine ⟨6927703656266628033250699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9236938208355504044334265 6927703656266628033250699)
        ·
          refine ⟨10391555484399942049876049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927703656266628033250699 10391555484399942049876049)
          ·
            refine ⟨7793666613299956537407037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10391555484399942049876049 7793666613299956537407037)
            ·
              refine ⟨2922624979987483701527639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7793666613299956537407037 2922624979987483701527639)
              ·
                refine ⟨4383937469981225552291459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922624979987483701527639 4383937469981225552291459)
                ·
                  refine ⟨6575906204971838328437189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383937469981225552291459 6575906204971838328437189)
                  ·
                    refine ⟨1232982413432219686581973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575906204971838328437189 1232982413432219686581973)
                    ·
                      rfl

theorem cell22_3601837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3601837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3601837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3601837 prefixEnd_3601837 := by exact prefixLift 3601837
  have htrace : WordTrace (prefixWord ++ tailWord_3601837) baseStart_3601837 baseEnd_3601837 := by
    simpa [prefixWord, tailWord_3601837, baseEnd_3601837] using wordTrace_append hprefix tailTrace_3601837
  have hstable : (prefixWord ++ tailWord_3601837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601837).length < 2 ^ (prefixWord ++ tailWord_3601837).sum := by decide
  have hdescent : baseEnd_3601837 < baseStart_3601837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602043 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 5]
def baseStart_3602043 : Nat := 118140960795 + 3602043 * 2 ^ 59
def prefixEnd_3602043 : Nat := 4983230072969 + 3 ^ 40 * 3602043 * 2
def baseEnd_3602043 : Nat := 411017643814034605310447

theorem tailTrace_3602043 : CollatzResearch.WordTrace tailWord_3602043 prefixEnd_3602043 411017643814034605310447 := by
  unfold tailWord_3602043
  simp only [CollatzResearch.WordTrace]
  refine ⟨131377301289420865812530783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87584867526280577208353855 131377301289420865812530783)
  ·
    refine ⟨197065951934131298718796175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131377301289420865812530783 197065951934131298718796175)
    ·
      refine ⟨295598927901196948078194263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197065951934131298718796175 295598927901196948078194263)
      ·
        refine ⟨443398391851795422117291395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295598927901196948078194263 443398391851795422117291395)
        ·
          refine ⟨665097587777693133175937093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443398391851795422117291395 665097587777693133175937093)
          ·
            refine ⟨124705797708317462470488205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 665097587777693133175937093 124705797708317462470488205)
            ·
              refine ⟨46764674140619048426433077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124705797708317462470488205 46764674140619048426433077)
              ·
                refine ⟨4384188200683035789978101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46764674140619048426433077 4384188200683035789978101)
                ·
                  refine ⟨411017643814034605310447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384188200683035789978101 411017643814034605310447)
                  ·
                    rfl

theorem cell22_3602043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].length) (baseStart_3602043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602043 prefixEnd_3602043 := by exact prefixLift 3602043
  have htrace : WordTrace (prefixWord ++ tailWord_3602043) baseStart_3602043 baseEnd_3602043 := by
    simpa [prefixWord, tailWord_3602043, baseEnd_3602043] using wordTrace_append hprefix tailTrace_3602043
  have hstable : (prefixWord ++ tailWord_3602043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602043).length < 2 ^ (prefixWord ++ tailWord_3602043).sum := by decide
  have hdescent : baseEnd_3602043 < baseStart_3602043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602073 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_3602073 : Nat := 118140960795 + 3602073 * 2 ^ 59
def prefixEnd_3602073 : Nat := 4983230072969 + 3 ^ 40 * 3602073 * 2
def baseEnd_3602073 : Nat := 1233063201055193737681249

theorem tailTrace_3602073 : CollatzResearch.WordTrace tailWord_3602073 prefixEnd_3602073 1233063201055193737681249 := by
  unfold tailWord_3602073
  simp only [CollatzResearch.WordTrace]
  refine ⟨131378395479312180936122873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87585596986208120624081915 131378395479312180936122873)
  ·
    refine ⟨98533796609484135702092155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131378395479312180936122873 98533796609484135702092155)
    ·
      refine ⟨147800694914226203553138233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98533796609484135702092155 147800694914226203553138233)
      ·
        refine ⟨110850521185669652664853675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147800694914226203553138233 110850521185669652664853675)
        ·
          refine ⟨166275781778504478997280513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110850521185669652664853675 166275781778504478997280513)
          ·
            refine ⟨124706836333878359247960385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166275781778504478997280513 124706836333878359247960385)
            ·
              refine ⟨93530127250408769435970289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124706836333878359247960385 93530127250408769435970289)
              ·
                refine ⟨70147595437806577076977717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93530127250408769435970289 70147595437806577076977717)
                ·
                  refine ⟨6576337072294366600966661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70147595437806577076977717 6576337072294366600966661)
                  ·
                    refine ⟨1233063201055193737681249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576337072294366600966661 1233063201055193737681249)
                    ·
                      rfl

theorem cell22_3602073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_3602073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602073 prefixEnd_3602073 := by exact prefixLift 3602073
  have htrace : WordTrace (prefixWord ++ tailWord_3602073) baseStart_3602073 baseEnd_3602073 := by
    simpa [prefixWord, tailWord_3602073, baseEnd_3602073] using wordTrace_append hprefix tailTrace_3602073
  have hstable : (prefixWord ++ tailWord_3602073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602073).length < 2 ^ (prefixWord ++ tailWord_3602073).sum := by decide
  have hdescent : baseEnd_3602073 < baseStart_3602073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602120 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_3602120 : Nat := 118140960795 + 3602120 * 2 ^ 59
def prefixEnd_3602120 : Nat := 4983230072969 + 3 ^ 40 * 3602120 * 2
def baseEnd_3602120 : Nat := 1233079290115701281756105

theorem tailTrace_3602120 : CollatzResearch.WordTrace tailWord_3602120 prefixEnd_3602120 1233079290115701281756105 := by
  unfold tailWord_3602120
  simp only [CollatzResearch.WordTrace]
  refine ⟨65690054855070953981541907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87586739806761271975389209 65690054855070953981541907)
  ·
    refine ⟨98535082282606430972312861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65690054855070953981541907 98535082282606430972312861)
    ·
      refine ⟨36950655855977411614617323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98535082282606430972312861 36950655855977411614617323)
      ·
        refine ⟨55425983783966117421925985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36950655855977411614617323 55425983783966117421925985)
        ·
          refine ⟨41569487837974588066444489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55425983783966117421925985 41569487837974588066444489)
          ·
            refine ⟨31177115878480941049833367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41569487837974588066444489 31177115878480941049833367)
            ·
              refine ⟨46765673817721411574750051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31177115878480941049833367 46765673817721411574750051)
              ·
                refine ⟨70148510726582117362125077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46765673817721411574750051 70148510726582117362125077)
                ·
                  refine ⟨3288211440308536751349613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70148510726582117362125077 3288211440308536751349613)
                  ·
                    refine ⟨1233079290115701281756105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3288211440308536751349613 1233079290115701281756105)
                    ·
                      rfl

theorem cell22_3602120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3602120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602120 prefixEnd_3602120 := by exact prefixLift 3602120
  have htrace : WordTrace (prefixWord ++ tailWord_3602120) baseStart_3602120 baseEnd_3602120 := by
    simpa [prefixWord, tailWord_3602120, baseEnd_3602120] using wordTrace_append hprefix tailTrace_3602120
  have hstable : (prefixWord ++ tailWord_3602120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602120).length < 2 ^ (prefixWord ++ tailWord_3602120).sum := by decide
  have hdescent : baseEnd_3602120 < baseStart_3602120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602135 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3602135 : Nat := 118140960795 + 3602135 * 2 ^ 59
def prefixEnd_3602135 : Nat := 4983230072969 + 3 ^ 40 * 3602135 * 2
def baseEnd_3602135 : Nat := 1233084424922246242631059

theorem tailTrace_3602135 : CollatzResearch.WordTrace tailWord_3602135 prefixEnd_3602135 1233084424922246242631059 := by
  unfold tailWord_3602135
  simp only [CollatzResearch.WordTrace]
  refine ⟨131380656805087565524879859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87587104536725043683253239 131380656805087565524879859)
  ·
    refine ⟨197070985207631348287319789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131380656805087565524879859 197070985207631348287319789)
    ·
      refine ⟨73901619452861755607744921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197070985207631348287319789 73901619452861755607744921)
      ·
        refine ⟨55426214589646316705808691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73901619452861755607744921 55426214589646316705808691)
        ·
          refine ⟨83139321884469475058713037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55426214589646316705808691 83139321884469475058713037)
          ·
            refine ⟨31177245706676053147017389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83139321884469475058713037 31177245706676053147017389)
            ·
              refine ⟨11691467140003519930131521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31177245706676053147017389 11691467140003519930131521)
              ·
                refine ⟨8768600355002639947598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11691467140003519930131521 8768600355002639947598641)
                ·
                  refine ⟨6576450266251979960698981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768600355002639947598641 6576450266251979960698981)
                  ·
                    refine ⟨1233084424922246242631059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576450266251979960698981 1233084424922246242631059)
                    ·
                      rfl

theorem cell22_3602135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3602135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602135 prefixEnd_3602135 := by exact prefixLift 3602135
  have htrace : WordTrace (prefixWord ++ tailWord_3602135) baseStart_3602135 baseEnd_3602135 := by
    simpa [prefixWord, tailWord_3602135, baseEnd_3602135] using wordTrace_append hprefix tailTrace_3602135
  have hstable : (prefixWord ++ tailWord_3602135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602135).length < 2 ^ (prefixWord ++ tailWord_3602135).sum := by decide
  have hdescent : baseEnd_3602135 < baseStart_3602135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602154 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3602154 : Nat := 118140960795 + 3602154 * 2 ^ 59
def prefixEnd_3602154 : Nat := 4983230072969 + 3 ^ 40 * 3602154 * 2
def baseEnd_3602154 : Nat := 1233090929010536526406001

theorem tailTrace_3602154 : CollatzResearch.WordTrace tailWord_3602154 prefixEnd_3602154 1233090929010536526406001 := by
  unfold tailWord_3602154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32845337448004682942455379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87587566528012487846547677 32845337448004682942455379)
  ·
    refine ⟨49268006172007024413683069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32845337448004682942455379 49268006172007024413683069)
    ·
      refine ⟨18475502314502634155131151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49268006172007024413683069 18475502314502634155131151)
      ·
        refine ⟨27713253471753951232696727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475502314502634155131151 27713253471753951232696727)
        ·
          refine ⟨41569880207630926849045091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27713253471753951232696727 41569880207630926849045091)
          ·
            refine ⟨62354820311446390273567637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41569880207630926849045091 62354820311446390273567637)
            ·
              refine ⟨2922882202099049544073483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62354820311446390273567637 2922882202099049544073483)
              ·
                refine ⟨4384323303148574316110225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922882202099049544073483 4384323303148574316110225)
                ·
                  refine ⟨3288242477361430737082669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384323303148574316110225 3288242477361430737082669)
                  ·
                    refine ⟨1233090929010536526406001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3288242477361430737082669 1233090929010536526406001)
                    ·
                      rfl

theorem cell22_3602154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3602154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602154 prefixEnd_3602154 := by exact prefixLift 3602154
  have htrace : WordTrace (prefixWord ++ tailWord_3602154) baseStart_3602154 baseEnd_3602154 := by
    simpa [prefixWord, tailWord_3602154, baseEnd_3602154] using wordTrace_append hprefix tailTrace_3602154
  have hstable : (prefixWord ++ tailWord_3602154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602154).length < 2 ^ (prefixWord ++ tailWord_3602154).sum := by decide
  have hdescent : baseEnd_3602154 < baseStart_3602154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602212 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3602212 : Nat := 118140960795 + 3602212 * 2 ^ 59
def prefixEnd_3602212 : Nat := 4983230072969 + 3 ^ 40 * 3602212 * 2
def baseEnd_3602212 : Nat := 411036927865281236151941

theorem tailTrace_3602212 : CollatzResearch.WordTrace tailWord_3602212 prefixEnd_3602212 411036927865281236151941 := by
  unfold tailWord_3602212
  simp only [CollatzResearch.WordTrace]
  refine ⟨65691732612904303837716445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87588976817205738450288593 65691732612904303837716445)
  ·
    refine ⟨24634399729839113939143667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65691732612904303837716445 24634399729839113939143667)
    ·
      refine ⟨36951599594758670908715501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634399729839113939143667 36951599594758670908715501)
      ·
        refine ⟨13856849848034501590768313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36951599594758670908715501 13856849848034501590768313)
        ·
          refine ⟨10392637386025876193076235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13856849848034501590768313 10392637386025876193076235)
          ·
            refine ⟨15588956079038814289614353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392637386025876193076235 15588956079038814289614353)
            ·
              refine ⟨11691717059279110717210765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15588956079038814289614353 11691717059279110717210765)
              ·
                refine ⟨4384393897229666518954037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11691717059279110717210765 4384393897229666518954037)
                ·
                  refine ⟨411036927865281236151941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384393897229666518954037 411036927865281236151941)
                  ·
                    rfl

theorem cell22_3602212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3602212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602212 prefixEnd_3602212 := by exact prefixLift 3602212
  have htrace : WordTrace (prefixWord ++ tailWord_3602212) baseStart_3602212 baseEnd_3602212 := by
    simpa [prefixWord, tailWord_3602212, baseEnd_3602212] using wordTrace_append hprefix tailTrace_3602212
  have hstable : (prefixWord ++ tailWord_3602212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602212).length < 2 ^ (prefixWord ++ tailWord_3602212).sum := by decide
  have hdescent : baseEnd_3602212 < baseStart_3602212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602233 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_3602233 : Nat := 118140960795 + 3602233 * 2 ^ 59
def prefixEnd_3602233 : Nat := 4983230072969 + 3 ^ 40 * 3602233 * 2
def baseEnd_3602233 : Nat := 1233117972325006653680759

theorem tailTrace_3602233 : CollatzResearch.WordTrace tailWord_3602233 prefixEnd_3602233 1233117972325006653680759 := by
  unfold tailWord_3602233
  simp only [CollatzResearch.WordTrace]
  refine ⟨131384231158732528261947353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87589487439155018841298235 131384231158732528261947353)
  ·
    refine ⟨98538173369049396196460515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131384231158732528261947353 98538173369049396196460515)
    ·
      refine ⟨147807260053574094294690773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98538173369049396196460515 147807260053574094294690773)
      ·
        refine ⟨3464232657505642835031815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 147807260053574094294690773 3464232657505642835031815)
        ·
          refine ⟨5196348986258464252547723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464232657505642835031815 5196348986258464252547723)
          ·
            refine ⟨7794523479387696378821585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196348986258464252547723 7794523479387696378821585)
            ·
              refine ⟨5845892609540772284116189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794523479387696378821585 5845892609540772284116189)
              ·
                refine ⟨2192209728577789606543571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5845892609540772284116189 2192209728577789606543571)
                ·
                  refine ⟨3288314592866684409815357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192209728577789606543571 3288314592866684409815357)
                  ·
                    refine ⟨1233117972325006653680759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3288314592866684409815357 1233117972325006653680759)
                    ·
                      rfl

theorem cell22_3602233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_3602233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602233 prefixEnd_3602233 := by exact prefixLift 3602233
  have htrace : WordTrace (prefixWord ++ tailWord_3602233) baseStart_3602233 baseEnd_3602233 := by
    simpa [prefixWord, tailWord_3602233, baseEnd_3602233] using wordTrace_append hprefix tailTrace_3602233
  have hstable : (prefixWord ++ tailWord_3602233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602233).length < 2 ^ (prefixWord ++ tailWord_3602233).sum := by decide
  have hdescent : baseEnd_3602233 < baseStart_3602233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602246 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3602246 : Nat := 118140960795 + 3602246 * 2 ^ 59
def prefixEnd_3602246 : Nat := 4983230072969 + 3 ^ 40 * 3602246 * 2
def baseEnd_3602246 : Nat := 411040807496892984368573

theorem tailTrace_3602246 : CollatzResearch.WordTrace tailWord_3602246 prefixEnd_3602246 411040807496892984368573 := by
  unfold tailWord_3602246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105772040865169733817831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87589803538456954321447061 4105772040865169733817831)
  ·
    refine ⟨6158658061297754600726747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105772040865169733817831 6158658061297754600726747)
    ·
      refine ⟨9237987091946631901090121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158658061297754600726747 9237987091946631901090121)
      ·
        refine ⟨6928490318959973925817591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9237987091946631901090121 6928490318959973925817591)
        ·
          refine ⟨10392735478439960888726387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928490318959973925817591 10392735478439960888726387)
          ·
            refine ⟨15589103217659941333089581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392735478439960888726387 15589103217659941333089581)
            ·
              refine ⟨5845913706622477999908593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15589103217659941333089581 5845913706622477999908593)
              ·
                refine ⟨4384435279966858499931445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845913706622477999908593 4384435279966858499931445)
                ·
                  refine ⟨411040807496892984368573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384435279966858499931445 411040807496892984368573)
                  ·
                    rfl

theorem cell22_3602246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3602246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602246 prefixEnd_3602246 := by exact prefixLift 3602246
  have htrace : WordTrace (prefixWord ++ tailWord_3602246) baseStart_3602246 baseEnd_3602246 := by
    simpa [prefixWord, tailWord_3602246, baseEnd_3602246] using wordTrace_append hprefix tailTrace_3602246
  have hstable : (prefixWord ++ tailWord_3602246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602246).length < 2 ^ (prefixWord ++ tailWord_3602246).sum := by decide
  have hdescent : baseEnd_3602246 < baseStart_3602246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602257 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 6]
def baseStart_3602257 : Nat := 118140960795 + 3602257 * 2 ^ 59
def prefixEnd_3602257 : Nat := 4983230072969 + 3 ^ 40 * 3602257 * 2
def baseEnd_3602257 : Nat := 411042062671826197026895

theorem tailTrace_3602257 : CollatzResearch.WordTrace tailWord_3602257 prefixEnd_3602257 411042062671826197026895 := by
  unfold tailWord_3602257
  simp only [CollatzResearch.WordTrace]
  refine ⟨131385106510645580360821025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87590071007097053573880683 131385106510645580360821025)
  ·
    refine ⟨98538829882984185270615769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131385106510645580360821025 98538829882984185270615769)
    ·
      refine ⟨73904122412238138952961827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98538829882984185270615769 73904122412238138952961827)
      ·
        refine ⟨110856183618357208429442741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73904122412238138952961827 110856183618357208429442741)
        ·
          refine ⟨10392767214220988290260257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110856183618357208429442741 10392767214220988290260257)
          ·
            refine ⟨7794575410665741217695193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10392767214220988290260257 7794575410665741217695193)
            ·
              refine ⟨5845931557999305913271395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794575410665741217695193 5845931557999305913271395)
              ·
                refine ⟨8768897336998958869907093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845931557999305913271395 8768897336998958869907093)
                ·
                  refine ⟨411042062671826197026895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8768897336998958869907093 411042062671826197026895)
                  ·
                    rfl

theorem cell22_3602257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_3602257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602257 prefixEnd_3602257 := by exact prefixLift 3602257
  have htrace : WordTrace (prefixWord ++ tailWord_3602257) baseStart_3602257 baseEnd_3602257 := by
    simpa [prefixWord, tailWord_3602257, baseEnd_3602257] using wordTrace_append hprefix tailTrace_3602257
  have hstable : (prefixWord ++ tailWord_3602257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602257).length < 2 ^ (prefixWord ++ tailWord_3602257).sum := by decide
  have hdescent : baseEnd_3602257 < baseStart_3602257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602272 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_3602272 : Nat := 118140960795 + 3602272 * 2 ^ 59
def prefixEnd_3602272 : Nat := 4983230072969 + 3 ^ 40 * 3602272 * 2
def baseEnd_3602272 : Nat := 1233131322822023551955639

theorem tailTrace_3602272 : CollatzResearch.WordTrace tailWord_3602272 prefixEnd_3602272 1233131322822023551955639 := by
  unfold tailWord_3602272
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692826802795618961308535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87590435737060825281744713 65692826802795618961308535)
  ·
    refine ⟨98539240204193428441962803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65692826802795618961308535 98539240204193428441962803)
    ·
      refine ⟨147808860306290142662944205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98539240204193428441962803 147808860306290142662944205)
      ·
        refine ⟨55428322614858803498604077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147808860306290142662944205 55428322614858803498604077)
        ·
          refine ⟨20785620980572051311976529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55428322614858803498604077 20785620980572051311976529)
          ·
            refine ⟨15589215735429038483982397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20785620980572051311976529 15589215735429038483982397)
            ·
              refine ⟨5845955900785889431493399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15589215735429038483982397 5845955900785889431493399)
              ·
                refine ⟨8768933851178834147240099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845955900785889431493399 8768933851178834147240099)
                ·
                  refine ⟨13153400776768251220860149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768933851178834147240099 13153400776768251220860149)
                  ·
                    refine ⟨1233131322822023551955639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13153400776768251220860149 1233131322822023551955639)
                    ·
                      rfl

theorem cell22_3602272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_3602272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602272 prefixEnd_3602272 := by exact prefixLift 3602272
  have htrace : WordTrace (prefixWord ++ tailWord_3602272) baseStart_3602272 baseEnd_3602272 := by
    simpa [prefixWord, tailWord_3602272, baseEnd_3602272] using wordTrace_append hprefix tailTrace_3602272
  have hstable : (prefixWord ++ tailWord_3602272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602272).length < 2 ^ (prefixWord ++ tailWord_3602272).sum := by decide
  have hdescent : baseEnd_3602272 < baseStart_3602272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602315 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_3602315 : Nat := 118140960795 + 3602315 * 2 ^ 59
def prefixEnd_3602315 : Nat := 4983230072969 + 3 ^ 40 * 3602315 * 2
def baseEnd_3602315 : Nat := 1233146042600785773130507

theorem tailTrace_3602315 : CollatzResearch.WordTrace tailWord_3602315 prefixEnd_3602315 1233146042600785773130507 := by
  unfold tailWord_3602315
  simp only [CollatzResearch.WordTrace]
  refine ⟨131387221944435456266432399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87591481296290304177621599 131387221944435456266432399)
  ·
    refine ⟨197080832916653184399648599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131387221944435456266432399 197080832916653184399648599)
    ·
      refine ⟨295621249374979776599472899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197080832916653184399648599 295621249374979776599472899)
      ·
        refine ⟨443431874062469664899209349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295621249374979776599472899 443431874062469664899209349)
        ·
          refine ⟨83143476386713062168601753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443431874062469664899209349 83143476386713062168601753)
          ·
            refine ⟨62357607290034796626451315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83143476386713062168601753 62357607290034796626451315)
            ·
              refine ⟨93536410935052194939676973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62357607290034796626451315 93536410935052194939676973)
              ·
                refine ⟨35076154100644573102378865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93536410935052194939676973 35076154100644573102378865)
                ·
                  refine ⟨26307115575483429826784149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35076154100644573102378865 26307115575483429826784149)
                  ·
                    refine ⟨1233146042600785773130507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26307115575483429826784149 1233146042600785773130507)
                    ·
                      rfl

theorem cell22_3602315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_3602315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602315 prefixEnd_3602315 := by exact prefixLift 3602315
  have htrace : WordTrace (prefixWord ++ tailWord_3602315) baseStart_3602315 baseEnd_3602315 := by
    simpa [prefixWord, tailWord_3602315, baseEnd_3602315] using wordTrace_append hprefix tailTrace_3602315
  have hstable : (prefixWord ++ tailWord_3602315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602315).length < 2 ^ (prefixWord ++ tailWord_3602315).sum := by decide
  have hdescent : baseEnd_3602315 < baseStart_3602315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602345 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_3602345 : Nat := 118140960795 + 3602345 * 2 ^ 59
def prefixEnd_3602345 : Nat := 4983230072969 + 3 ^ 40 * 3602345 * 2
def baseEnd_3602345 : Nat := 1233156312213875694880415

theorem tailTrace_3602345 : CollatzResearch.WordTrace tailWord_3602345 prefixEnd_3602345 1233156312213875694880415 := by
  unfold tailWord_3602345
  simp only [CollatzResearch.WordTrace]
  refine ⟨131388316134326771390024489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87592210756217847593349659 131388316134326771390024489)
  ·
    refine ⟨98541237100745078542518367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131388316134326771390024489 98541237100745078542518367)
    ·
      refine ⟨147811855651117617813777551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98541237100745078542518367 147811855651117617813777551)
      ·
        refine ⟨221717783476676426720666327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147811855651117617813777551 221717783476676426720666327)
        ·
          refine ⟨332576675215014640080999491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221717783476676426720666327 332576675215014640080999491)
          ·
            refine ⟨498865012822521960121499237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332576675215014640080999491 498865012822521960121499237)
            ·
              refine ⟨93537189904222867522781107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498865012822521960121499237 93537189904222867522781107)
              ·
                refine ⟨140305784856334301284171661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93537189904222867522781107 140305784856334301284171661)
                ·
                  refine ⟨52614669321125362981564373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140305784856334301284171661 52614669321125362981564373)
                  ·
                    refine ⟨1233156312213875694880415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52614669321125362981564373 1233156312213875694880415)
                    ·
                      rfl

theorem cell22_3602345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_3602345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602345 prefixEnd_3602345 := by exact prefixLift 3602345
  have htrace : WordTrace (prefixWord ++ tailWord_3602345) baseStart_3602345 baseEnd_3602345 := by
    simpa [prefixWord, tailWord_3602345, baseEnd_3602345] using wordTrace_append hprefix tailTrace_3602345
  have hstable : (prefixWord ++ tailWord_3602345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602345).length < 2 ^ (prefixWord ++ tailWord_3602345).sum := by decide
  have hdescent : baseEnd_3602345 < baseStart_3602345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602392 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_3602392 : Nat := 118140960795 + 3602392 * 2 ^ 59
def prefixEnd_3602392 : Nat := 4983230072969 + 3 ^ 40 * 3602392 * 2
def baseEnd_3602392 : Nat := 411057467091461079651757

theorem tailTrace_3602392 : CollatzResearch.WordTrace tailWord_3602392 prefixEnd_3602392 411057467091461079651757 := by
  unfold tailWord_3602392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65695015182578249208492715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87593353576770998944656953 65695015182578249208492715)
  ·
    refine ⟨98542522773867373812739073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65695015182578249208492715 98542522773867373812739073)
    ·
      refine ⟨73906892080400530359554305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98542522773867373812739073 73906892080400530359554305)
      ·
        refine ⟨55430169060300397769665729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73906892080400530359554305 55430169060300397769665729)
        ·
          refine ⟨41572626795225298327249297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55430169060300397769665729 41572626795225298327249297)
          ·
            refine ⟨31179470096418973745436973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41572626795225298327249297 31179470096418973745436973)
            ·
              refine ⟨11692301286157115154538865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31179470096418973745436973 11692301286157115154538865)
              ·
                refine ⟨8769225964617836365904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11692301286157115154538865 8769225964617836365904149)
                ·
                  refine ⟨411057467091461079651757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8769225964617836365904149 411057467091461079651757)
                  ·
                    rfl

theorem cell22_3602392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_3602392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602392 prefixEnd_3602392 := by exact prefixLift 3602392
  have htrace : WordTrace (prefixWord ++ tailWord_3602392) baseStart_3602392 baseEnd_3602392 := by
    simpa [prefixWord, tailWord_3602392, baseEnd_3602392] using wordTrace_append hprefix tailTrace_3602392
  have hstable : (prefixWord ++ tailWord_3602392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602392).length < 2 ^ (prefixWord ++ tailWord_3602392).sum := by decide
  have hdescent : baseEnd_3602392 < baseStart_3602392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602471 : List Nat := [1, 1, 7, 1, 2, 2, 8]
def baseStart_3602471 : Nat := 118140960795 + 3602471 * 2 ^ 59
def prefixEnd_3602471 : Nat := 4983230072969 + 3 ^ 40 * 3602471 * 2
def baseEnd_3602471 : Nat := 45674053503290865415927

theorem tailTrace_3602471 : CollatzResearch.WordTrace tailWord_3602471 prefixEnd_3602471 45674053503290865415927 := by
  unfold tailWord_3602471
  simp only [CollatzResearch.WordTrace]
  refine ⟨131392911731870294909111267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87595274487913529939407511 131392911731870294909111267)
  ·
    refine ⟨197089367597805442363666901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131392911731870294909111267 197089367597805442363666901)
    ·
      refine ⟨4619282053073565055398443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 197089367597805442363666901 4619282053073565055398443)
      ·
        refine ⟨6928923079610347583097665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619282053073565055398443 6928923079610347583097665)
        ·
          refine ⟨5196692309707760687323249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6928923079610347583097665 5196692309707760687323249)
          ·
            refine ⟨3897519232280820515492437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196692309707760687323249 3897519232280820515492437)
            ·
              refine ⟨45674053503290865415927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3897519232280820515492437 45674053503290865415927)
              ·
                rfl

theorem cell22_3602471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 8].length) (baseStart_3602471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602471 prefixEnd_3602471 := by exact prefixLift 3602471
  have htrace : WordTrace (prefixWord ++ tailWord_3602471) baseStart_3602471 baseEnd_3602471 := by
    simpa [prefixWord, tailWord_3602471, baseEnd_3602471] using wordTrace_append hprefix tailTrace_3602471
  have hstable : (prefixWord ++ tailWord_3602471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602471).length < 2 ^ (prefixWord ++ tailWord_3602471).sum := by decide
  have hdescent : baseEnd_3602471 < baseStart_3602471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602527 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 10]
def baseStart_3602527 : Nat := 118140960795 + 3602527 * 2 ^ 59
def prefixEnd_3602527 : Nat := 4983230072969 + 3 ^ 40 * 3602527 * 2
def baseEnd_3602527 : Nat := 411072871511095962276619

theorem tailTrace_3602527 : CollatzResearch.WordTrace tailWord_3602527 prefixEnd_3602527 411072871511095962276619 := by
  unfold tailWord_3602527
  simp only [CollatzResearch.WordTrace]
  refine ⟨131394954219667416473149835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87596636146444944315433223 131394954219667416473149835)
  ·
    refine ⟨197092431329501124709724753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131394954219667416473149835 197092431329501124709724753)
    ·
      refine ⟨147819323497125843532293565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197092431329501124709724753 147819323497125843532293565)
      ·
        refine ⟨55432246311422191324610087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147819323497125843532293565 55432246311422191324610087)
        ·
          refine ⟨83148369467133286986915131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55432246311422191324610087 83148369467133286986915131)
          ·
            refine ⟨124722554200699930480372697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83148369467133286986915131 124722554200699930480372697)
            ·
              refine ⟨93541915650524947860279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124722554200699930480372697 93541915650524947860279523)
              ·
                refine ⟨140312873475787421790419285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93541915650524947860279523 140312873475787421790419285)
                ·
                  refine ⟨411072871511095962276619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140312873475787421790419285 411072871511095962276619)
                  ·
                    rfl

theorem cell22_3602527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_3602527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602527 prefixEnd_3602527 := by exact prefixLift 3602527
  have htrace : WordTrace (prefixWord ++ tailWord_3602527) baseStart_3602527 baseEnd_3602527 := by
    simpa [prefixWord, tailWord_3602527, baseEnd_3602527] using wordTrace_append hprefix tailTrace_3602527
  have hstable : (prefixWord ++ tailWord_3602527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602527).length < 2 ^ (prefixWord ++ tailWord_3602527).sum := by decide
  have hdescent : baseEnd_3602527 < baseStart_3602527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602561 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 6]
def baseStart_3602561 : Nat := 118140960795 + 3602561 * 2 ^ 59
def prefixEnd_3602561 : Nat := 4983230072969 + 3 ^ 40 * 3602561 * 2
def baseEnd_3602561 : Nat := 411076751142707710493251

theorem tailTrace_3602561 : CollatzResearch.WordTrace tailWord_3602561 prefixEnd_3602561 411076751142707710493251 := by
  unfold tailWord_3602561
  simp only [CollatzResearch.WordTrace]
  refine ⟨131396194301544240279887537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87597462867696160186591691 131396194301544240279887537)
  ·
    refine ⟨98547145726158180209915653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131396194301544240279887537 98547145726158180209915653)
    ·
      refine ⟨18477589823654658789359185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98547145726158180209915653 18477589823654658789359185)
      ·
        refine ⟨13858192367740994092019389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18477589823654658789359185 13858192367740994092019389)
        ·
          refine ⟨5196822137902872784507271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13858192367740994092019389 5196822137902872784507271)
          ·
            refine ⟨7795233206854309176760907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196822137902872784507271 7795233206854309176760907)
            ·
              refine ⟨11692849810281463765141361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795233206854309176760907 11692849810281463765141361)
              ·
                refine ⟨8769637357711097823856021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11692849810281463765141361 8769637357711097823856021)
                ·
                  refine ⟨411076751142707710493251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8769637357711097823856021 411076751142707710493251)
                  ·
                    rfl

theorem cell22_3602561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_3602561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602561 prefixEnd_3602561 := by exact prefixLift 3602561
  have htrace : WordTrace (prefixWord ++ tailWord_3602561) baseStart_3602561 baseEnd_3602561 := by
    simpa [prefixWord, tailWord_3602561, baseEnd_3602561] using wordTrace_append hprefix tailTrace_3602561
  have hstable : (prefixWord ++ tailWord_3602561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602561).length < 2 ^ (prefixWord ++ tailWord_3602561).sum := by decide
  have hdescent : baseEnd_3602561 < baseStart_3602561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602578 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3602578 : Nat := 118140960795 + 3602578 * 2 ^ 59
def prefixEnd_3602578 : Nat := 4983230072969 + 3 ^ 40 * 3602578 * 2
def baseEnd_3602578 : Nat := 411078690958513584601567

theorem tailTrace_3602578 : CollatzResearch.WordTrace tailWord_3602578 prefixEnd_3602578 411078690958513584601567 := by
  unfold tailWord_3602578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32849203585620663045814097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87597876228321768122170925 32849203585620663045814097)
  ·
    refine ⟨24636902689215497284360573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32849203585620663045814097 24636902689215497284360573)
    ·
      refine ⟨9238838508455811481635215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24636902689215497284360573 9238838508455811481635215)
      ·
        refine ⟨13858257762683717222452823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9238838508455811481635215 13858257762683717222452823)
        ·
          refine ⟨20787386644025575833679235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858257762683717222452823 20787386644025575833679235)
          ·
            refine ⟨31181079966038363750518853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20787386644025575833679235 31181079966038363750518853)
            ·
              refine ⟨5846452493632193203222285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31181079966038363750518853 5846452493632193203222285)
              ·
                refine ⟨2192419685112072451208357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5846452493632193203222285 2192419685112072451208357)
                ·
                  refine ⟨411078690958513584601567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192419685112072451208357 411078690958513584601567)
                  ·
                    rfl

theorem cell22_3602578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3602578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602578 prefixEnd_3602578 := by exact prefixLift 3602578
  have htrace : WordTrace (prefixWord ++ tailWord_3602578) baseStart_3602578 baseEnd_3602578 := by
    simpa [prefixWord, tailWord_3602578, baseEnd_3602578] using wordTrace_append hprefix tailTrace_3602578
  have hstable : (prefixWord ++ tailWord_3602578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602578).length < 2 ^ (prefixWord ++ tailWord_3602578).sum := by decide
  have hdescent : baseEnd_3602578 < baseStart_3602578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602580 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3602580 : Nat := 118140960795 + 3602580 * 2 ^ 59
def prefixEnd_3602580 : Nat := 4983230072969 + 3 ^ 40 * 3602580 * 2
def baseEnd_3602580 : Nat := 1233236757516413415254695

theorem tailTrace_3602580 : CollatzResearch.WordTrace tailWord_3602580 prefixEnd_3602580 1233236757516413415254695 := by
  unfold tailWord_3602580
  simp only [CollatzResearch.WordTrace]
  refine ⟨65698443644237703262414597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87597924858983604349886129 65698443644237703262414597)
  ·
    refine ⟨12318458183294569361702737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65698443644237703262414597 12318458183294569361702737)
    ·
      refine ⟨9238843637470927021277053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12318458183294569361702737 9238843637470927021277053)
      ·
        refine ⟨3464566364051597632978895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9238843637470927021277053 3464566364051597632978895)
        ·
          refine ⟨5196849546077396449468343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464566364051597632978895 5196849546077396449468343)
          ·
            refine ⟨7795274319116094674202515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196849546077396449468343 7795274319116094674202515)
            ·
              refine ⟨11692911478674142011303773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795274319116094674202515 11692911478674142011303773)
              ·
                refine ⟨4384841804502803254238915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11692911478674142011303773 4384841804502803254238915)
                ·
                  refine ⟨6577262706754204881358373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384841804502803254238915 6577262706754204881358373)
                  ·
                    refine ⟨1233236757516413415254695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577262706754204881358373 1233236757516413415254695)
                    ·
                      rfl

theorem cell22_3602580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3602580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602580 prefixEnd_3602580 := by exact prefixLift 3602580
  have htrace : WordTrace (prefixWord ++ tailWord_3602580) baseStart_3602580 baseEnd_3602580 := by
    simpa [prefixWord, tailWord_3602580, baseEnd_3602580] using wordTrace_append hprefix tailTrace_3602580
  have hstable : (prefixWord ++ tailWord_3602580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602580).length < 2 ^ (prefixWord ++ tailWord_3602580).sum := by decide
  have hdescent : baseEnd_3602580 < baseStart_3602580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602589 : List Nat := [1, 4, 2, 1, 1, 4, 9]
def baseStart_3602589 : Nat := 118140960795 + 3602589 * 2 ^ 59
def prefixEnd_3602589 : Nat := 4983230072969 + 3 ^ 40 * 3602589 * 2
def baseEnd_3602589 : Nat := 45675549570382977473321

theorem tailTrace_3602589 : CollatzResearch.WordTrace tailWord_3602589 prefixEnd_3602589 45675549570382977473321 := by
  unfold tailWord_3602589
  simp only [CollatzResearch.WordTrace]
  refine ⟨131397215545442801061906821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87598143696961867374604547 131397215545442801061906821)
  ·
    refine ⟨24636977914770525199107529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131397215545442801061906821 24636977914770525199107529)
    ·
      refine ⟨18477733436077893899330647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24636977914770525199107529 18477733436077893899330647)
      ·
        refine ⟨27716600154116840848995971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18477733436077893899330647 27716600154116840848995971)
        ·
          refine ⟨41574900231175261273493957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27716600154116840848995971 41574900231175261273493957)
          ·
            refine ⟨7795293793345361488780117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41574900231175261273493957 7795293793345361488780117)
            ·
              refine ⟨45675549570382977473321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7795293793345361488780117 45675549570382977473321)
              ·
                rfl

theorem cell22_3602589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 9].length) (baseStart_3602589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602589 prefixEnd_3602589 := by exact prefixLift 3602589
  have htrace : WordTrace (prefixWord ++ tailWord_3602589) baseStart_3602589 baseEnd_3602589 := by
    simpa [prefixWord, tailWord_3602589, baseEnd_3602589] using wordTrace_append hprefix tailTrace_3602589
  have hstable : (prefixWord ++ tailWord_3602589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602589).length < 2 ^ (prefixWord ++ tailWord_3602589).sum := by decide
  have hdescent : baseEnd_3602589 < baseStart_3602589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602593 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3602593 : Nat := 118140960795 + 3602593 * 2 ^ 59
def prefixEnd_3602593 : Nat := 4983230072969 + 3 ^ 40 * 3602593 * 2
def baseEnd_3602593 : Nat := 1233241207682085714679655

theorem tailTrace_3602593 : CollatzResearch.WordTrace tailWord_3602593 prefixEnd_3602593 1233241207682085714679655 := by
  unfold tailWord_3602593
  simp only [CollatzResearch.WordTrace]
  refine ⟨131397361437428309745052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87598240958285539830034955 131397361437428309745052433)
  ·
    refine ⟨98548021078071232308789325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131397361437428309745052433 98548021078071232308789325)
    ·
      refine ⟨36955507904276712115795997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98548021078071232308789325 36955507904276712115795997)
      ·
        refine ⟨13858315464103767043423499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36955507904276712115795997 13858315464103767043423499)
        ·
          refine ⟨20787473196155650565135249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858315464103767043423499 20787473196155650565135249)
          ·
            refine ⟨15590604897116737923851437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20787473196155650565135249 15590604897116737923851437)
            ·
              refine ⟨5846476836418776721444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15590604897116737923851437 5846476836418776721444289)
              ·
                refine ⟨4384857627314082541083217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5846476836418776721444289 4384857627314082541083217)
                ·
                  refine ⟨3288643220485561905812413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384857627314082541083217 3288643220485561905812413)
                  ·
                    refine ⟨1233241207682085714679655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3288643220485561905812413 1233241207682085714679655)
                    ·
                      rfl

theorem cell22_3602593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3602593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602593 prefixEnd_3602593 := by exact prefixLift 3602593
  have htrace : WordTrace (prefixWord ++ tailWord_3602593) baseStart_3602593 baseEnd_3602593 := by
    simpa [prefixWord, tailWord_3602593, baseEnd_3602593] using wordTrace_append hprefix tailTrace_3602593
  have hstable : (prefixWord ++ tailWord_3602593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602593).length < 2 ^ (prefixWord ++ tailWord_3602593).sum := by decide
  have hdescent : baseEnd_3602593 < baseStart_3602593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602634 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3602634 : Nat := 118140960795 + 3602634 * 2 ^ 59
def prefixEnd_3602634 : Nat := 4983230072969 + 3 ^ 40 * 3602634 * 2
def baseEnd_3602634 : Nat := 411085080939991758134843

theorem tailTrace_3602634 : CollatzResearch.WordTrace tailWord_3602634 prefixEnd_3602634 411085080939991758134843 := by
  unfold tailWord_3602634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32849714207569943436823739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87599237886853182498196637 32849714207569943436823739)
  ·
    refine ⟨49274571311354915155235609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32849714207569943436823739 49274571311354915155235609)
    ·
      refine ⟨36955928483516186366426707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49274571311354915155235609 36955928483516186366426707)
      ·
        refine ⟨55433892725274279549640061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36955928483516186366426707 55433892725274279549640061)
        ·
          refine ⟨20787709771977854831115023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55433892725274279549640061 20787709771977854831115023)
          ·
            refine ⟨31181564657966782246672535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20787709771977854831115023 31181564657966782246672535)
            ·
              refine ⟨46772346986950173370008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31181564657966782246672535 46772346986950173370008803)
              ·
                refine ⟨70158520480425260055013205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46772346986950173370008803 70158520480425260055013205)
                ·
                  refine ⟨411085080939991758134843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70158520480425260055013205 411085080939991758134843)
                  ·
                    rfl

theorem cell22_3602634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3602634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602634 prefixEnd_3602634 := by exact prefixLift 3602634
  have htrace : WordTrace (prefixWord ++ tailWord_3602634) baseStart_3602634 baseEnd_3602634 := by
    simpa [prefixWord, tailWord_3602634, baseEnd_3602634] using wordTrace_append hprefix tailTrace_3602634
  have hstable : (prefixWord ++ tailWord_3602634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602634).length < 2 ^ (prefixWord ++ tailWord_3602634).sum := by decide
  have hdescent : baseEnd_3602634 < baseStart_3602634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602649 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_3602649 : Nat := 118140960795 + 3602649 * 2 ^ 59
def prefixEnd_3602649 : Nat := 4983230072969 + 3 ^ 40 * 3602649 * 2
def baseEnd_3602649 : Nat := 1233260377626520235279483

theorem tailTrace_3602649 : CollatzResearch.WordTrace tailWord_3602649 prefixEnd_3602649 1233260377626520235279483 := by
  unfold tailWord_3602649
  simp only [CollatzResearch.WordTrace]
  refine ⟨131399403925225431309091001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87599602616816954206060667 131399403925225431309091001)
  ·
    refine ⟨98549552943919073481818251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131399403925225431309091001 98549552943919073481818251)
    ·
      refine ⟨147824329415878610222727377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98549552943919073481818251 147824329415878610222727377)
      ·
        refine ⟨110868247061908957667045533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147824329415878610222727377 110868247061908957667045533)
        ·
          refine ⟨41575592648215859125142075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110868247061908957667045533 41575592648215859125142075)
          ·
            refine ⟨62363388972323788687713113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41575592648215859125142075 62363388972323788687713113)
            ·
              refine ⟨46772541729242841515784835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62363388972323788687713113 46772541729242841515784835)
              ·
                refine ⟨70158812593864262273677253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46772541729242841515784835 70158812593864262273677253)
                ·
                  refine ⟨13154777361349549176314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70158812593864262273677253 13154777361349549176314485)
                  ·
                    refine ⟨1233260377626520235279483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154777361349549176314485 1233260377626520235279483)
                    ·
                      rfl

theorem cell22_3602649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_3602649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602649 prefixEnd_3602649 := by exact prefixLift 3602649
  have htrace : WordTrace (prefixWord ++ tailWord_3602649) baseStart_3602649 baseEnd_3602649 := by
    simpa [prefixWord, tailWord_3602649, baseEnd_3602649] using wordTrace_append hprefix tailTrace_3602649
  have hstable : (prefixWord ++ tailWord_3602649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602649).length < 2 ^ (prefixWord ++ tailWord_3602649).sum := by decide
  have hdescent : baseEnd_3602649 < baseStart_3602649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602681 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_3602681 : Nat := 118140960795 + 3602681 * 2 ^ 59
def prefixEnd_3602681 : Nat := 4983230072969 + 3 ^ 40 * 3602681 * 2
def baseEnd_3602681 : Nat := 1233271331880482818479385

theorem tailTrace_3602681 : CollatzResearch.WordTrace tailWord_3602681 prefixEnd_3602681 1233271331880482818479385 := by
  unfold tailWord_3602681
  simp only [CollatzResearch.WordTrace]
  refine ⟨131400571061109500774255897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87600380707406333849503931 131400571061109500774255897)
  ·
    refine ⟨98550428295832125580691923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131400571061109500774255897 98550428295832125580691923)
    ·
      refine ⟨147825642443748188371037885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98550428295832125580691923 147825642443748188371037885)
      ·
        refine ⟨55434615916405570639139207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147825642443748188371037885 55434615916405570639139207)
        ·
          refine ⟨83151923874608355958708811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55434615916405570639139207 83151923874608355958708811)
          ·
            refine ⟨124727885811912533938063217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83151923874608355958708811 124727885811912533938063217)
            ·
              refine ⟨93545914358934400453547413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124727885811912533938063217 93545914358934400453547413)
              ·
                refine ⟨4384964735575050021260035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93545914358934400453547413 4384964735575050021260035)
                ·
                  refine ⟨6577447103362575031890053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384964735575050021260035 6577447103362575031890053)
                  ·
                    refine ⟨1233271331880482818479385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577447103362575031890053 1233271331880482818479385)
                    ·
                      rfl

theorem cell22_3602681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_3602681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602681 prefixEnd_3602681 := by exact prefixLift 3602681
  have htrace : WordTrace (prefixWord ++ tailWord_3602681) baseStart_3602681 baseEnd_3602681 := by
    simpa [prefixWord, tailWord_3602681, baseEnd_3602681] using wordTrace_append hprefix tailTrace_3602681
  have hstable : (prefixWord ++ tailWord_3602681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602681).length < 2 ^ (prefixWord ++ tailWord_3602681).sum := by decide
  have hdescent : baseEnd_3602681 < baseStart_3602681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602816 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_3602816 : Nat := 118140960795 + 3602816 * 2 ^ 59
def prefixEnd_3602816 : Nat := 4983230072969 + 3 ^ 40 * 3602816 * 2
def baseEnd_3602816 : Nat := 1233317545139387466353971

theorem tailTrace_3602816 : CollatzResearch.WordTrace tailWord_3602816 prefixEnd_3602816 1233317545139387466353971 := by
  unfold tailWord_3602816
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702747457810209415210151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87603663277080279220280201 65702747457810209415210151)
  ·
    refine ⟨98554121186715314122815227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65702747457810209415210151 98554121186715314122815227)
    ·
      refine ⟨147831181780072971184222841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98554121186715314122815227 147831181780072971184222841)
      ·
        refine ⟨110873386335054728388167131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147831181780072971184222841 110873386335054728388167131)
        ·
          refine ⟨166310079502582092582250697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110873386335054728388167131 166310079502582092582250697)
          ·
            refine ⟨124732559626936569436688023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166310079502582092582250697 124732559626936569436688023)
            ·
              refine ⟨187098839440404854155032035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124732559626936569436688023 187098839440404854155032035)
              ·
                refine ⟨280648259160607281232548053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187098839440404854155032035 280648259160607281232548053)
                ·
                  refine ⟨6577693574076733153887845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280648259160607281232548053 6577693574076733153887845)
                  ·
                    refine ⟨1233317545139387466353971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577693574076733153887845 1233317545139387466353971)
                    ·
                      rfl

theorem cell22_3602816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_3602816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602816 prefixEnd_3602816 := by exact prefixLift 3602816
  have htrace : WordTrace (prefixWord ++ tailWord_3602816) baseStart_3602816 baseEnd_3602816 := by
    simpa [prefixWord, tailWord_3602816, baseEnd_3602816] using wordTrace_append hprefix tailTrace_3602816
  have hstable : (prefixWord ++ tailWord_3602816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602816).length < 2 ^ (prefixWord ++ tailWord_3602816).sum := by decide
  have hdescent : baseEnd_3602816 < baseStart_3602816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_3602891 : Nat := 118140960795 + 3602891 * 2 ^ 59
def prefixEnd_3602891 : Nat := 4983230072969 + 3 ^ 40 * 3602891 * 2
def baseEnd_3602891 : Nat := 1233343219172112270728741

theorem tailTrace_3602891 : CollatzResearch.WordTrace tailWord_3602891 prefixEnd_3602891 1233343219172112270728741 := by
  unfold tailWord_3602891
  simp only [CollatzResearch.WordTrace]
  refine ⟨131408230390348706639400527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87605486926899137759600351 131408230390348706639400527)
  ·
    refine ⟨197112345585523059959100791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131408230390348706639400527 197112345585523059959100791)
    ·
      refine ⟨295668518378284589938651187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197112345585523059959100791 295668518378284589938651187)
      ·
        refine ⟨443502777567426884907976781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295668518378284589938651187 443502777567426884907976781)
        ·
          refine ⟨166313541587785081840491293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443502777567426884907976781 166313541587785081840491293)
          ·
            refine ⟨62367578095419405690184235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166313541587785081840491293 62367578095419405690184235)
            ·
              refine ⟨93551367143129108535276353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62367578095419405690184235 93551367143129108535276353)
              ·
                refine ⟨70163525357346831401457265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93551367143129108535276353 70163525357346831401457265)
                ·
                  refine ⟨52622644018010123551092949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70163525357346831401457265 52622644018010123551092949)
                  ·
                    refine ⟨1233343219172112270728741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52622644018010123551092949 1233343219172112270728741)
                    ·
                      rfl

theorem cell22_3602891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_3602891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602891 prefixEnd_3602891 := by exact prefixLift 3602891
  have htrace : WordTrace (prefixWord ++ tailWord_3602891) baseStart_3602891 baseEnd_3602891 := by
    simpa [prefixWord, tailWord_3602891, baseEnd_3602891] using wordTrace_append hprefix tailTrace_3602891
  have hstable : (prefixWord ++ tailWord_3602891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602891).length < 2 ^ (prefixWord ++ tailWord_3602891).sum := by decide
  have hdescent : baseEnd_3602891 < baseStart_3602891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602938 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3602938 : Nat := 118140960795 + 3602938 * 2 ^ 59
def prefixEnd_3602938 : Nat := 4983230072969 + 3 ^ 40 * 3602938 * 2
def baseEnd_3602938 : Nat := 411119769410873271601199

theorem tailTrace_3602938 : CollatzResearch.WordTrace tailWord_3602938 prefixEnd_3602938 411119769410873271601199 := by
  unfold tailWord_3602938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852486155294608416590367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87606629747452289110907645 32852486155294608416590367)
  ·
    refine ⟨49278729232941912624885551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32852486155294608416590367 49278729232941912624885551)
    ·
      refine ⟨73918093849412868937328327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49278729232941912624885551 73918093849412868937328327)
      ·
        refine ⟨110877140774119303405992491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73918093849412868937328327 110877140774119303405992491)
        ·
          refine ⟨166315711161178955108988737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110877140774119303405992491 166315711161178955108988737)
          ·
            refine ⟨124736783370884216331741553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166315711161178955108988737 124736783370884216331741553)
            ·
              refine ⟨93552587528163162248806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124736783370884216331741553 93552587528163162248806165)
              ·
                refine ⟨4385277540382648230412789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93552587528163162248806165 4385277540382648230412789)
                ·
                  refine ⟨411119769410873271601199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385277540382648230412789 411119769410873271601199)
                  ·
                    rfl

theorem cell22_3602938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3602938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602938 prefixEnd_3602938 := by exact prefixLift 3602938
  have htrace : WordTrace (prefixWord ++ tailWord_3602938) baseStart_3602938 baseEnd_3602938 := by
    simpa [prefixWord, tailWord_3602938, baseEnd_3602938] using wordTrace_append hprefix tailTrace_3602938
  have hstable : (prefixWord ++ tailWord_3602938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602938).length < 2 ^ (prefixWord ++ tailWord_3602938).sum := by decide
  have hdescent : baseEnd_3602938 < baseStart_3602938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602976 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_3602976 : Nat := 118140960795 + 3602976 * 2 ^ 59
def prefixEnd_3602976 : Nat := 4983230072969 + 3 ^ 40 * 3602976 * 2
def baseEnd_3602976 : Nat := 1233372316409200382353481

theorem tailTrace_3602976 : CollatzResearch.WordTrace tailWord_3602976 prefixEnd_3602976 1233372316409200382353481 := by
  unfold tailWord_3602976
  simp only [CollatzResearch.WordTrace]
  refine ⟨65705665297520383078122391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87607553730027177437496521 65705665297520383078122391)
  ·
    refine ⟨98558497946280574617183587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65705665297520383078122391 98558497946280574617183587)
    ·
      refine ⟨147837746919420861925775381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98558497946280574617183587 147837746919420861925775381)
      ·
        refine ⟨6929894386847852902770721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147837746919420861925775381 6929894386847852902770721)
        ·
          refine ⟨5197420790135889677078041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929894386847852902770721 5197420790135889677078041)
          ·
            refine ⟨3898065592601917257808531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197420790135889677078041 3898065592601917257808531)
            ·
              refine ⟨5847098388902875886712797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898065592601917257808531 5847098388902875886712797)
              ·
                refine ⟨2192661895838578457517299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5847098388902875886712797 2192661895838578457517299)
                ·
                  refine ⟨3288992843757867686275949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192661895838578457517299 3288992843757867686275949)
                  ·
                    refine ⟨1233372316409200382353481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3288992843757867686275949 1233372316409200382353481)
                    ·
                      rfl

theorem cell22_3602976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_3602976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3602976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3602976 prefixEnd_3602976 := by exact prefixLift 3602976
  have htrace : WordTrace (prefixWord ++ tailWord_3602976) baseStart_3602976 baseEnd_3602976 := by
    simpa [prefixWord, tailWord_3602976, baseEnd_3602976] using wordTrace_append hprefix tailTrace_3602976
  have hstable : (prefixWord ++ tailWord_3602976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602976).length < 2 ^ (prefixWord ++ tailWord_3602976).sum := by decide
  have hdescent : baseEnd_3602976 < baseStart_3602976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603006 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3603006 : Nat := 118140960795 + 3603006 * 2 ^ 59
def prefixEnd_3603006 : Nat := 4983230072969 + 3 ^ 40 * 3603006 * 2
def baseEnd_3603006 : Nat := 411127528674096768034463

theorem tailTrace_3603006 : CollatzResearch.WordTrace tailWord_3603006 prefixEnd_3603006 411127528674096768034463 := by
  unfold tailWord_3603006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426553098116510159979609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87608283189954720853224581 16426553098116510159979609)
  ·
    refine ⟨12319914823587382619984707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16426553098116510159979609 12319914823587382619984707)
    ·
      refine ⟨18479872235381073929977061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319914823587382619984707 18479872235381073929977061)
      ·
        refine ⟨3464976044133951361870699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18479872235381073929977061 3464976044133951361870699)
        ·
          refine ⟨5197464066200927042806049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464976044133951361870699 5197464066200927042806049)
          ·
            refine ⟨3898098049650695282104537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197464066200927042806049 3898098049650695282104537)
            ·
              refine ⟨2923573537238021461578403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3898098049650695282104537 2923573537238021461578403)
              ·
                refine ⟨4385360305857032192367605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923573537238021461578403 4385360305857032192367605)
                ·
                  refine ⟨411127528674096768034463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385360305857032192367605 411127528674096768034463)
                  ·
                    rfl

theorem cell22_3603006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3603006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603006 prefixEnd_3603006 := by exact prefixLift 3603006
  have htrace : WordTrace (prefixWord ++ tailWord_3603006) baseStart_3603006 baseEnd_3603006 := by
    simpa [prefixWord, tailWord_3603006, baseEnd_3603006] using wordTrace_append hprefix tailTrace_3603006
  have hstable : (prefixWord ++ tailWord_3603006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603006).length < 2 ^ (prefixWord ++ tailWord_3603006).sum := by decide
  have hdescent : baseEnd_3603006 < baseStart_3603006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603045 : List Nat := [1, 3, 1, 3, 5, 9]
def baseStart_3603045 : Nat := 118140960795 + 3603045 * 2 ^ 59
def prefixEnd_3603045 : Nat := 4983230072969 + 3 ^ 40 * 3603045 * 2
def baseEnd_3603045 : Nat := 15227110327398854350349

theorem tailTrace_3603045 : CollatzResearch.WordTrace tailWord_3603045 prefixEnd_3603045 15227110327398854350349 := by
  unfold tailWord_3603045
  simp only [CollatzResearch.WordTrace]
  refine ⟨131413847231790790940506589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87609231487860527293671059 131413847231790790940506589)
  ·
    refine ⟨49280192711921546602689971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131413847231790790940506589 49280192711921546602689971)
    ·
      refine ⟨73920289067882319904034957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49280192711921546602689971 73920289067882319904034957)
      ·
        refine ⟨27720108400455869964013109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73920289067882319904034957 27720108400455869964013109)
        ·
          refine ⟨2598760162542737809126229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27720108400455869964013109 2598760162542737809126229)
          ·
            refine ⟨15227110327398854350349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2598760162542737809126229 15227110327398854350349)
            ·
              rfl

theorem cell22_3603045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 9].length) (baseStart_3603045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603045 prefixEnd_3603045 := by exact prefixLift 3603045
  have htrace : WordTrace (prefixWord ++ tailWord_3603045) baseStart_3603045 baseEnd_3603045 := by
    simpa [prefixWord, tailWord_3603045, baseEnd_3603045] using wordTrace_append hprefix tailTrace_3603045
  have hstable : (prefixWord ++ tailWord_3603045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603045).length < 2 ^ (prefixWord ++ tailWord_3603045).sum := by decide
  have hdescent : baseEnd_3603045 < baseStart_3603045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603077 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_3603077 : Nat := 118140960795 + 3603077 * 2 ^ 59
def prefixEnd_3603077 : Nat := 4983230072969 + 3 ^ 40 * 3603077 * 2
def baseEnd_3603077 : Nat := 1233406890773269785578171

theorem tailTrace_3603077 : CollatzResearch.WordTrace tailWord_3603077 prefixEnd_3603077 1233406890773269785578171 := by
  unfold tailWord_3603077
  simp only [CollatzResearch.WordTrace]
  refine ⟨131415014367674860405671485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87610009578449906937114323 131415014367674860405671485)
  ·
    refine ⟨49280630387878072652126807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131415014367674860405671485 49280630387878072652126807)
    ·
      refine ⟨73920945581817108978190211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49280630387878072652126807 73920945581817108978190211)
      ·
        refine ⟨110881418372725663467285317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73920945581817108978190211 110881418372725663467285317)
        ·
          refine ⟨20790265944886061900115997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110881418372725663467285317 20790265944886061900115997)
          ·
            refine ⟨7796349729332273212543499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20790265944886061900115997 7796349729332273212543499)
            ·
              refine ⟨11694524593998409818815249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796349729332273212543499 11694524593998409818815249)
              ·
                refine ⟨8770893445498807364111437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11694524593998409818815249 8770893445498807364111437)
                ·
                  refine ⟨3289085042062052761541789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8770893445498807364111437 3289085042062052761541789)
                  ·
                    refine ⟨1233406890773269785578171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289085042062052761541789 1233406890773269785578171)
                    ·
                      rfl

theorem cell22_3603077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_3603077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603077 prefixEnd_3603077 := by exact prefixLift 3603077
  have htrace : WordTrace (prefixWord ++ tailWord_3603077) baseStart_3603077 baseEnd_3603077 := by
    simpa [prefixWord, tailWord_3603077, baseEnd_3603077] using wordTrace_append hprefix tailTrace_3603077
  have hstable : (prefixWord ++ tailWord_3603077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603077).length < 2 ^ (prefixWord ++ tailWord_3603077).sum := by decide
  have hdescent : baseEnd_3603077 < baseStart_3603077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603111 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3603111 : Nat := 118140960795 + 3603111 * 2 ^ 59
def prefixEnd_3603111 : Nat := 4983230072969 + 3 ^ 40 * 3603111 * 2
def baseEnd_3603111 : Nat := 1233418529668105030228067

theorem tailTrace_3603111 : CollatzResearch.WordTrace tailWord_3603111 prefixEnd_3603111 1233418529668105030228067 := by
  unfold tailWord_3603111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131416254449551684212409187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87610836299701122808272791 131416254449551684212409187)
  ·
    refine ⟨197124381674327526318613781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131416254449551684212409187 197124381674327526318613781)
    ·
      refine ⟨9240205390984102796185021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197124381674327526318613781 9240205390984102796185021)
      ·
        refine ⟨3465077021619038548569383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9240205390984102796185021 3465077021619038548569383)
        ·
          refine ⟨5197615532428557822854075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465077021619038548569383 5197615532428557822854075)
          ·
            refine ⟨7796423298642836734281113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197615532428557822854075 7796423298642836734281113)
            ·
              refine ⟨5847317473982127550710835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796423298642836734281113 5847317473982127550710835)
              ·
                refine ⟨8770976210973191326066253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847317473982127550710835 8770976210973191326066253)
                ·
                  refine ⟨3289116079114946747274845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8770976210973191326066253 3289116079114946747274845)
                  ·
                    refine ⟨1233418529668105030228067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289116079114946747274845 1233418529668105030228067)
                    ·
                      rfl

theorem cell22_3603111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3603111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603111 prefixEnd_3603111 := by exact prefixLift 3603111
  have htrace : WordTrace (prefixWord ++ tailWord_3603111) baseStart_3603111 baseEnd_3603111 := by
    simpa [prefixWord, tailWord_3603111, baseEnd_3603111] using wordTrace_append hprefix tailTrace_3603111
  have hstable : (prefixWord ++ tailWord_3603111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603111).length < 2 ^ (prefixWord ++ tailWord_3603111).sum := by decide
  have hdescent : baseEnd_3603111 < baseStart_3603111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603135 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 6]
def baseStart_3603135 : Nat := 118140960795 + 3603135 * 2 ^ 59
def prefixEnd_3603135 : Nat := 4983230072969 + 3 ^ 40 * 3603135 * 2
def baseEnd_3603135 : Nat := 411142248452858989209331

theorem tailTrace_3603135 : CollatzResearch.WordTrace tailWord_3603135 prefixEnd_3603135 411142248452858989209331 := by
  unfold tailWord_3603135
  simp only [CollatzResearch.WordTrace]
  refine ⟨131417129801464736311282859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87611419867643157540855239 131417129801464736311282859)
  ·
    refine ⟨197125694702197104466924289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131417129801464736311282859 197125694702197104466924289)
    ·
      refine ⟨147844271026647828350193217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197125694702197104466924289 147844271026647828350193217)
      ·
        refine ⟨110883203269985871262644913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147844271026647828350193217 110883203269985871262644913)
        ·
          refine ⟨83162402452489403446983685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110883203269985871262644913 83162402452489403446983685)
          ·
            refine ⟨15592950459841763146309441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83162402452489403446983685 15592950459841763146309441)
            ·
              refine ⟨11694712844881322359732081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15592950459841763146309441 11694712844881322359732081)
              ·
                refine ⟨8771034633660991769799061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11694712844881322359732081 8771034633660991769799061)
                ·
                  refine ⟨411142248452858989209331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8771034633660991769799061 411142248452858989209331)
                  ·
                    rfl

theorem cell22_3603135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_3603135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603135 prefixEnd_3603135 := by exact prefixLift 3603135
  have htrace : WordTrace (prefixWord ++ tailWord_3603135) baseStart_3603135 baseEnd_3603135 := by
    simpa [prefixWord, tailWord_3603135, baseEnd_3603135] using wordTrace_append hprefix tailTrace_3603135
  have hstable : (prefixWord ++ tailWord_3603135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603135).length < 2 ^ (prefixWord ++ tailWord_3603135).sum := by decide
  have hdescent : baseEnd_3603135 < baseStart_3603135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603167 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 4, 3]
def baseStart_3603167 : Nat := 118140960795 + 3603167 * 2 ^ 59
def prefixEnd_3603167 : Nat := 4983230072969 + 3 ^ 40 * 3603167 * 2
def baseEnd_3603167 : Nat := 1233437699612539550827895

theorem tailTrace_3603167 : CollatzResearch.WordTrace tailWord_3603167 prefixEnd_3603167 1233437699612539550827895 := by
  unfold tailWord_3603167
  simp only [CollatzResearch.WordTrace]
  refine ⟨131418296937348805776447755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87612197958232537184298503 131418296937348805776447755)
  ·
    refine ⟨197127445406023208664671633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131418296937348805776447755 197127445406023208664671633)
    ·
      refine ⟨147845584054517406498503725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197127445406023208664671633 147845584054517406498503725)
      ·
        refine ⟨55442094020444027436938897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147845584054517406498503725 55442094020444027436938897)
        ·
          refine ⟨41581570515333020577704173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55442094020444027436938897 41581570515333020577704173)
          ·
            refine ⟨15593088943249882716639065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41581570515333020577704173 15593088943249882716639065)
            ·
              refine ⟨11694816707437412037479299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593088943249882716639065 11694816707437412037479299)
              ·
                refine ⟨17542225061156118056218949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694816707437412037479299 17542225061156118056218949)
                ·
                  refine ⟨3289167198966772135541053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17542225061156118056218949 3289167198966772135541053)
                  ·
                    refine ⟨1233437699612539550827895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289167198966772135541053 1233437699612539550827895)
                    ·
                      rfl

theorem cell22_3603167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_3603167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603167 prefixEnd_3603167 := by exact prefixLift 3603167
  have htrace : WordTrace (prefixWord ++ tailWord_3603167) baseStart_3603167 baseEnd_3603167 := by
    simpa [prefixWord, tailWord_3603167, baseEnd_3603167] using wordTrace_append hprefix tailTrace_3603167
  have hstable : (prefixWord ++ tailWord_3603167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603167).length < 2 ^ (prefixWord ++ tailWord_3603167).sum := by decide
  have hdescent : baseEnd_3603167 < baseStart_3603167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603218 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3603218 : Nat := 118140960795 + 3603218 * 2 ^ 59
def prefixEnd_3603218 : Nat := 4983230072969 + 3 ^ 40 * 3603218 * 2
def baseEnd_3603218 : Nat := 1233455157954792417802739

theorem tailTrace_3603218 : CollatzResearch.WordTrace tailWord_3603218 prefixEnd_3603218 1233455157954792417802739 := by
  unfold tailWord_3603218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855039265041010371638577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87613438040109360991036205 32855039265041010371638577)
  ·
    refine ⟨24641279448780757778728933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32855039265041010371638577 24641279448780757778728933)
    ·
      refine ⟨4620239896646392083511675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24641279448780757778728933 4620239896646392083511675)
      ·
        refine ⟨6930359844969588125267513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620239896646392083511675 6930359844969588125267513)
        ·
          refine ⟨5197769883727191093950635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6930359844969588125267513 5197769883727191093950635)
          ·
            refine ⟨7796654825590786640925953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197769883727191093950635 7796654825590786640925953)
            ·
              refine ⟨5847491119193089980694465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796654825590786640925953 5847491119193089980694465)
              ·
                refine ⟨4385618339394817485520849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847491119193089980694465 4385618339394817485520849)
                ·
                  refine ⟨3289213754546113114140637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4385618339394817485520849 3289213754546113114140637)
                  ·
                    refine ⟨1233455157954792417802739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289213754546113114140637 1233455157954792417802739)
                    ·
                      rfl

theorem cell22_3603218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3603218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603218 prefixEnd_3603218 := by exact prefixLift 3603218
  have htrace : WordTrace (prefixWord ++ tailWord_3603218) baseStart_3603218 baseEnd_3603218 := by
    simpa [prefixWord, tailWord_3603218, baseEnd_3603218] using wordTrace_append hprefix tailTrace_3603218
  have hstable : (prefixWord ++ tailWord_3603218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603218).length < 2 ^ (prefixWord ++ tailWord_3603218).sum := by decide
  have hdescent : baseEnd_3603218 < baseStart_3603218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603246 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3603246 : Nat := 118140960795 + 3603246 * 2 ^ 59
def prefixEnd_3603246 : Nat := 4983230072969 + 3 ^ 40 * 3603246 * 2
def baseEnd_3603246 : Nat := 1233464742927009678102653

theorem tailTrace_3603246 : CollatzResearch.WordTrace tailWord_3603246 prefixEnd_3603246 1233464742927009678102653 := by
  unfold tailWord_3603246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16427647288007825283571699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87614118869375068179049061 16427647288007825283571699)
  ·
    refine ⟨24641470932011737925357549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16427647288007825283571699 24641470932011737925357549)
    ·
      refine ⟨9240551599504401722009081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24641470932011737925357549 9240551599504401722009081)
      ·
        refine ⟨6930413699628301291506811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9240551599504401722009081 6930413699628301291506811)
        ·
          refine ⟨10395620549442451937260217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930413699628301291506811 10395620549442451937260217)
          ·
            refine ⟨7796715412081838952945163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10395620549442451937260217 7796715412081838952945163)
            ·
              refine ⟨11695073118122758429417745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796715412081838952945163 11695073118122758429417745)
              ·
                refine ⟨8771304838592068822063309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11695073118122758429417745 8771304838592068822063309)
                ·
                  refine ⟨3289239314472025808273741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8771304838592068822063309 3289239314472025808273741)
                  ·
                    refine ⟨1233464742927009678102653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289239314472025808273741 1233464742927009678102653)
                    ·
                      rfl

theorem cell22_3603246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3603246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603246 prefixEnd_3603246 := by exact prefixLift 3603246
  have htrace : WordTrace (prefixWord ++ tailWord_3603246) baseStart_3603246 baseEnd_3603246 := by
    simpa [prefixWord, tailWord_3603246, baseEnd_3603246] using wordTrace_append hprefix tailTrace_3603246
  have hstable : (prefixWord ++ tailWord_3603246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603246).length < 2 ^ (prefixWord ++ tailWord_3603246).sum := by decide
  have hdescent : baseEnd_3603246 < baseStart_3603246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603287 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 6]
def baseStart_3603287 : Nat := 118140960795 + 3603287 * 2 ^ 59
def prefixEnd_3603287 : Nat := 4983230072969 + 3 ^ 40 * 3603287 * 2
def baseEnd_3603287 : Nat := 411159592688299745942509

theorem tailTrace_3603287 : CollatzResearch.WordTrace tailWord_3603287 prefixEnd_3603287 411159592688299745942509 := by
  unfold tailWord_3603287
  simp only [CollatzResearch.WordTrace]
  refine ⟨131422673696914066270816115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87615115797942710847210743 131422673696914066270816115)
  ·
    refine ⟨197134010545371099406224173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131422673696914066270816115 197134010545371099406224173)
    ·
      refine ⟨73925253954514162277334065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197134010545371099406224173 73925253954514162277334065)
      ·
        refine ⟨55443940465885621708000549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73925253954514162277334065 55443940465885621708000549)
        ·
          refine ⟨10395738837353554070250103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55443940465885621708000549 10395738837353554070250103)
          ·
            refine ⟨15593608256030331105375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395738837353554070250103 15593608256030331105375155)
            ·
              refine ⟨23390412384045496658062733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15593608256030331105375155 23390412384045496658062733)
              ·
                refine ⟨8771404644017061246773525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23390412384045496658062733 8771404644017061246773525)
                ·
                  refine ⟨411159592688299745942509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8771404644017061246773525 411159592688299745942509)
                  ·
                    rfl

theorem cell22_3603287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_3603287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603287 prefixEnd_3603287 := by exact prefixLift 3603287
  have htrace : WordTrace (prefixWord ++ tailWord_3603287) baseStart_3603287 baseEnd_3603287 := by
    simpa [prefixWord, tailWord_3603287, baseEnd_3603287] using wordTrace_append hprefix tailTrace_3603287
  have hstable : (prefixWord ++ tailWord_3603287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603287).length < 2 ^ (prefixWord ++ tailWord_3603287).sum := by decide
  have hdescent : baseEnd_3603287 < baseStart_3603287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603321 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 4]
def baseStart_3603321 : Nat := 118140960795 + 3603321 * 2 ^ 59
def prefixEnd_3603321 : Nat := 4983230072969 + 3 ^ 40 * 3603321 * 2
def baseEnd_3603321 : Nat := 411163472319911494159141

theorem tailTrace_3603321 : CollatzResearch.WordTrace tailWord_3603321 prefixEnd_3603321 411163472319911494159141 := by
  unfold tailWord_3603321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131423913778790890077553817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87615942519193926718369211 131423913778790890077553817)
  ·
    refine ⟨98567935334093167558165363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131423913778790890077553817 98567935334093167558165363)
    ·
      refine ⟨147851903001139751337248045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98567935334093167558165363 147851903001139751337248045)
      ·
        refine ⟨55444463625427406751468017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147851903001139751337248045 55444463625427406751468017)
        ·
          refine ⟨41583347719070555063601013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55444463625427406751468017 41583347719070555063601013)
          ·
            refine ⟨3898438848662864537212595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41583347719070555063601013 3898438848662864537212595)
            ·
              refine ⟨5847658272994296805818893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898438848662864537212595 5847658272994296805818893)
              ·
                refine ⟨2192871852372861302182085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5847658272994296805818893 2192871852372861302182085)
                ·
                  refine ⟨411163472319911494159141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192871852372861302182085 411163472319911494159141)
                  ·
                    rfl

theorem cell22_3603321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_3603321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603321 prefixEnd_3603321 := by exact prefixLift 3603321
  have htrace : WordTrace (prefixWord ++ tailWord_3603321) baseStart_3603321 baseEnd_3603321 := by
    simpa [prefixWord, tailWord_3603321, baseEnd_3603321] using wordTrace_append hprefix tailTrace_3603321
  have hstable : (prefixWord ++ tailWord_3603321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603321).length < 2 ^ (prefixWord ++ tailWord_3603321).sum := by decide
  have hdescent : baseEnd_3603321 < baseStart_3603321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603338 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_3603338 : Nat := 118140960795 + 3603338 * 2 ^ 59
def prefixEnd_3603338 : Nat := 4983230072969 + 3 ^ 40 * 3603338 * 2
def baseEnd_3603338 : Nat := 411165412135717368267457

theorem tailTrace_3603338 : CollatzResearch.WordTrace tailWord_3603338 prefixEnd_3603338 411165412135717368267457 := by
  unfold tailWord_3603338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32856133454932325495230667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87616355879819534653948445 32856133454932325495230667)
  ·
    refine ⟨49284200182398488242846001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32856133454932325495230667 49284200182398488242846001)
    ·
      refine ⟨36963150136798866182134501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49284200182398488242846001 36963150136798866182134501)
      ·
        refine ⟨6930590650649787409150219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36963150136798866182134501 6930590650649787409150219)
        ·
          refine ⟨10395885975974681113725329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930590650649787409150219 10395885975974681113725329)
          ·
            refine ⟨7796914481981010835293997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10395885975974681113725329 7796914481981010835293997)
            ·
              refine ⟨2923842930742879063235249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7796914481981010835293997 2923842930742879063235249)
              ·
                refine ⟨2192882198057159297426437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923842930742879063235249 2192882198057159297426437)
                ·
                  refine ⟨411165412135717368267457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192882198057159297426437 411165412135717368267457)
                  ·
                    rfl

theorem cell22_3603338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_3603338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603338 prefixEnd_3603338 := by exact prefixLift 3603338
  have htrace : WordTrace (prefixWord ++ tailWord_3603338) baseStart_3603338 baseEnd_3603338 := by
    simpa [prefixWord, tailWord_3603338, baseEnd_3603338] using wordTrace_append hprefix tailTrace_3603338
  have hstable : (prefixWord ++ tailWord_3603338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603338).length < 2 ^ (prefixWord ++ tailWord_3603338).sum := by decide
  have hdescent : baseEnd_3603338 < baseStart_3603338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603364 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3603364 : Nat := 118140960795 + 3603364 * 2 ^ 59
def prefixEnd_3603364 : Nat := 4983230072969 + 3 ^ 40 * 3603364 * 2
def baseEnd_3603364 : Nat := 1233505136738496703652291

theorem tailTrace_3603364 : CollatzResearch.WordTrace tailWord_3603364 prefixEnd_3603364 1233505136738496703652291 := by
  unfold tailWord_3603364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65712741058817554210684573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87616988078423405614246097 65712741058817554210684573)
  ·
    refine ⟨24642277897056582829006715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65712741058817554210684573 24642277897056582829006715)
    ·
      refine ⟨36963416845584874243510073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24642277897056582829006715 36963416845584874243510073)
      ·
        refine ⟨27722562634188655682632555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36963416845584874243510073 27722562634188655682632555)
        ·
          refine ⟨41583843951282983523948833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27722562634188655682632555 41583843951282983523948833)
          ·
            refine ⟨31187882963462237642961625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41583843951282983523948833 31187882963462237642961625)
            ·
              refine ⟨23390912222596678232221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31187882963462237642961625 23390912222596678232221219)
              ·
                refine ⟨35086368333895017348331829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23390912222596678232221219 35086368333895017348331829)
                ·
                  refine ⟨3289347031302657876406109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35086368333895017348331829 3289347031302657876406109)
                  ·
                    refine ⟨1233505136738496703652291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289347031302657876406109 1233505136738496703652291)
                    ·
                      rfl

theorem cell22_3603364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3603364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603364 prefixEnd_3603364 := by exact prefixLift 3603364
  have htrace : WordTrace (prefixWord ++ tailWord_3603364) baseStart_3603364 baseEnd_3603364 := by
    simpa [prefixWord, tailWord_3603364, baseEnd_3603364] using wordTrace_append hprefix tailTrace_3603364
  have hstable : (prefixWord ++ tailWord_3603364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603364).length < 2 ^ (prefixWord ++ tailWord_3603364).sum := by decide
  have hdescent : baseEnd_3603364 < baseStart_3603364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603441 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3603441 : Nat := 118140960795 + 3603441 * 2 ^ 59
def prefixEnd_3603441 : Nat := 4983230072969 + 3 ^ 40 * 3603441 * 2
def baseEnd_3603441 : Nat := 1233531495412094169477055

theorem tailTrace_3603441 : CollatzResearch.WordTrace tailWord_3603441 prefixEnd_3603441 1233531495412094169477055 := by
  unfold tailWord_3603441
  simp only [CollatzResearch.WordTrace]
  refine ⟨131428290538356150571922177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87618860358904100381281451 131428290538356150571922177)
  ·
    refine ⟨98571217903767112928941633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131428290538356150571922177 98571217903767112928941633)
    ·
      refine ⟨73928413427825334696706225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98571217903767112928941633 73928413427825334696706225)
      ·
        refine ⟨55446310070869001022529669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73928413427825334696706225 55446310070869001022529669)
        ·
          refine ⟨10396183138287937691724313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55446310070869001022529669 10396183138287937691724313)
          ·
            refine ⟨7797137353715953268793235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10396183138287937691724313 7797137353715953268793235)
            ·
              refine ⟨11695706030573929903189853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797137353715953268793235 11695706030573929903189853)
              ·
                refine ⟨4385889761465223713696195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11695706030573929903189853 4385889761465223713696195)
                ·
                  refine ⟨6578834642197835570544293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385889761465223713696195 6578834642197835570544293)
                  ·
                    refine ⟨1233531495412094169477055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6578834642197835570544293 1233531495412094169477055)
                    ·
                      rfl

theorem cell22_3603441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3603441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603441 prefixEnd_3603441 := by exact prefixLift 3603441
  have htrace : WordTrace (prefixWord ++ tailWord_3603441) baseStart_3603441 baseEnd_3603441 := by
    simpa [prefixWord, tailWord_3603441, baseEnd_3603441] using wordTrace_append hprefix tailTrace_3603441
  have hstable : (prefixWord ++ tailWord_3603441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603441).length < 2 ^ (prefixWord ++ tailWord_3603441).sum := by decide
  have hdescent : baseEnd_3603441 < baseStart_3603441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603445 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 5]
def baseStart_3603445 : Nat := 118140960795 + 3603445 * 2 ^ 59
def prefixEnd_3603445 : Nat := 4983230072969 + 3 ^ 40 * 3603445 * 2
def baseEnd_3603445 : Nat := 411177621564613164125681

theorem tailTrace_3603445 : CollatzResearch.WordTrace tailWord_3603445 prefixEnd_3603445 411177621564613164125681 := by
  unfold tailWord_3603445
  simp only [CollatzResearch.WordTrace]
  refine ⟨131428436430341659255067789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87618957620227772836711859 131428436430341659255067789)
  ·
    refine ⟨49285663661378122220650421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131428436430341659255067789 49285663661378122220650421)
    ·
      refine ⟨4620530968254198958185977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49285663661378122220650421 4620530968254198958185977)
      ·
        refine ⟨3465398226190649218639483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4620530968254198958185977 3465398226190649218639483)
        ·
          refine ⟨5198097339285973827959225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465398226190649218639483 5198097339285973827959225)
          ·
            refine ⟨3898573004464480370969419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198097339285973827959225 3898573004464480370969419)
            ·
              refine ⟨5847859506696720556454129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898573004464480370969419 5847859506696720556454129)
              ·
                refine ⟨4385894630022540417340597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847859506696720556454129 4385894630022540417340597)
                ·
                  refine ⟨411177621564613164125681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385894630022540417340597 411177621564613164125681)
                  ·
                    rfl

theorem cell22_3603445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_3603445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603445 prefixEnd_3603445 := by exact prefixLift 3603445
  have htrace : WordTrace (prefixWord ++ tailWord_3603445) baseStart_3603445 baseEnd_3603445 := by
    simpa [prefixWord, tailWord_3603445, baseEnd_3603445] using wordTrace_append hprefix tailTrace_3603445
  have hstable : (prefixWord ++ tailWord_3603445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603445).length < 2 ^ (prefixWord ++ tailWord_3603445).sum := by decide
  have hdescent : baseEnd_3603445 < baseStart_3603445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603608 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_3603608 : Nat := 118140960795 + 3603608 * 2 ^ 59
def prefixEnd_3603608 : Nat := 4983230072969 + 3 ^ 40 * 3603608 * 2
def baseEnd_3603608 : Nat := 411196220974987133517181

theorem tailTrace_3603608 : CollatzResearch.WordTrace tailWord_3603608 prefixEnd_3603608 411196220974987133517181 := by
  unfold tailWord_3603608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65717190764375569046625739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87622921019167425395500985 65717190764375569046625739)
  ·
    refine ⟨98575786146563353569938609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65717190764375569046625739 98575786146563353569938609)
    ·
      refine ⟨73931839609922515177453957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98575786146563353569938609 73931839609922515177453957)
      ·
        refine ⟨13862219926860471595772617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73931839609922515177453957 13862219926860471595772617)
        ·
          refine ⟨10396664945145353696829463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13862219926860471595772617 10396664945145353696829463)
          ·
            refine ⟨15594997417718030545244195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396664945145353696829463 15594997417718030545244195)
            ·
              refine ⟨23392496126577045817866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15594997417718030545244195 23392496126577045817866293)
              ·
                refine ⟨2193046511866598045424965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23392496126577045817866293 2193046511866598045424965)
                ·
                  refine ⟨411196220974987133517181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193046511866598045424965 411196220974987133517181)
                  ·
                    rfl

theorem cell22_3603608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_3603608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603608 prefixEnd_3603608 := by exact prefixLift 3603608
  have htrace : WordTrace (prefixWord ++ tailWord_3603608) baseStart_3603608 baseEnd_3603608 := by
    simpa [prefixWord, tailWord_3603608, baseEnd_3603608] using wordTrace_append hprefix tailTrace_3603608
  have hstable : (prefixWord ++ tailWord_3603608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603608).length < 2 ^ (prefixWord ++ tailWord_3603608).sum := by decide
  have hdescent : baseEnd_3603608 < baseStart_3603608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603610 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_3603610 : Nat := 118140960795 + 3603610 * 2 ^ 59
def prefixEnd_3603610 : Nat := 4983230072969 + 3 ^ 40 * 3603610 * 2
def baseEnd_3603610 : Nat := 1233589347565834062001537

theorem tailTrace_3603610 : CollatzResearch.WordTrace tailWord_3603610 prefixEnd_3603610 1233589347565834062001537 := by
  unfold tailWord_3603610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32858613618685973108706071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87622969649829261623216189 32858613618685973108706071)
  ·
    refine ⟨49287920428028959663059107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32858613618685973108706071 49287920428028959663059107)
    ·
      refine ⟨73931880642043439494588661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49287920428028959663059107 73931880642043439494588661)
      ·
        refine ⟨6931113810191572452617687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73931880642043439494588661 6931113810191572452617687)
        ·
          refine ⟨10396670715287358678926531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6931113810191572452617687 10396670715287358678926531)
          ·
            refine ⟨15595006072931038018389797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396670715287358678926531 15595006072931038018389797)
            ·
              refine ⟨2924063638674569628448087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15595006072931038018389797 2924063638674569628448087)
              ·
                refine ⟨4386095458011854442672131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924063638674569628448087 4386095458011854442672131)
                ·
                  refine ⟨6579143187017781664008197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386095458011854442672131 6579143187017781664008197)
                  ·
                    refine ⟨1233589347565834062001537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6579143187017781664008197 1233589347565834062001537)
                    ·
                      rfl

theorem cell22_3603610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_3603610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603610 prefixEnd_3603610 := by exact prefixLift 3603610
  have htrace : WordTrace (prefixWord ++ tailWord_3603610) baseStart_3603610 baseEnd_3603610 := by
    simpa [prefixWord, tailWord_3603610, baseEnd_3603610] using wordTrace_append hprefix tailTrace_3603610
  have hstable : (prefixWord ++ tailWord_3603610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603610).length < 2 ^ (prefixWord ++ tailWord_3603610).sum := by decide
  have hdescent : baseEnd_3603610 < baseStart_3603610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603651 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 5, 3]
def baseStart_3603651 : Nat := 118140960795 + 3603651 * 2 ^ 59
def prefixEnd_3603651 : Nat := 4983230072969 + 3 ^ 40 * 3603651 * 2
def baseEnd_3603651 : Nat := 1233603382703723621726411

theorem tailTrace_3603651 : CollatzResearch.WordTrace tailWord_3603651 prefixEnd_3603651 1233603382703723621726411 := by
  unfold tailWord_3603651
  simp only [CollatzResearch.WordTrace]
  refine ⟨131435949867595356437066807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87623966578396904291377871 131435949867595356437066807)
  ·
    refine ⟨197153924801393034655600211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131435949867595356437066807 197153924801393034655600211)
    ·
      refine ⟨295730887202089551983400317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197153924801393034655600211 295730887202089551983400317)
      ·
        refine ⟨110899082700783581993775119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295730887202089551983400317 110899082700783581993775119)
        ·
          refine ⟨166348624051175372990662679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110899082700783581993775119 166348624051175372990662679)
          ·
            refine ⟨249522936076763059485994019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166348624051175372990662679 249522936076763059485994019)
            ·
              refine ⟨374284404115144589228991029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249522936076763059485994019 374284404115144589228991029)
              ·
                refine ⟨35089162885794805240217909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374284404115144589228991029 35089162885794805240217909)
                ·
                  refine ⟨3289609020543262991270429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35089162885794805240217909 3289609020543262991270429)
                  ·
                    refine ⟨1233603382703723621726411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289609020543262991270429 1233603382703723621726411)
                    ·
                      rfl

theorem cell22_3603651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].length) (baseStart_3603651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603651 prefixEnd_3603651 := by exact prefixLift 3603651
  have htrace : WordTrace (prefixWord ++ tailWord_3603651) baseStart_3603651 baseEnd_3603651 := by
    simpa [prefixWord, tailWord_3603651, baseEnd_3603651] using wordTrace_append hprefix tailTrace_3603651
  have hstable : (prefixWord ++ tailWord_3603651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603651).length < 2 ^ (prefixWord ++ tailWord_3603651).sum := by decide
  have hdescent : baseEnd_3603651 < baseStart_3603651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603670 : List Nat := [5, 2, 1, 2, 2, 2, 8]
def baseStart_3603670 : Nat := 118140960795 + 3603670 * 2 ^ 59
def prefixEnd_3603670 : Nat := 4983230072969 + 3 ^ 40 * 3603670 * 2
def baseEnd_3603670 : Nat := 45689255066370885388939

theorem tailTrace_3603670 : CollatzResearch.WordTrace tailWord_3603670 prefixEnd_3603670 45689255066370885388939 := by
  unfold tailWord_3603670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214790178407907667625529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87624428569684348454672309 8214790178407907667625529)
  ·
    refine ⟨6161092633805930750719147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8214790178407907667625529 6161092633805930750719147)
    ·
      refine ⟨9241638950708896126078721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6161092633805930750719147 9241638950708896126078721)
      ·
        refine ⟨6931229213031672094559041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241638950708896126078721 6931229213031672094559041)
        ·
          refine ⟨5198421909773754070919281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931229213031672094559041 5198421909773754070919281)
          ·
            refine ⟨3898816432330315553189461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198421909773754070919281 3898816432330315553189461)
            ·
              refine ⟨45689255066370885388939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3898816432330315553189461 45689255066370885388939)
              ·
                rfl

theorem cell22_3603670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 8].length) (baseStart_3603670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603670 prefixEnd_3603670 := by exact prefixLift 3603670
  have htrace : WordTrace (prefixWord ++ tailWord_3603670) baseStart_3603670 baseEnd_3603670 := by
    simpa [prefixWord, tailWord_3603670, baseEnd_3603670] using wordTrace_append hprefix tailTrace_3603670
  have hstable : (prefixWord ++ tailWord_3603670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603670).length < 2 ^ (prefixWord ++ tailWord_3603670).sum := by decide
  have hdescent : baseEnd_3603670 < baseStart_3603670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603681 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 7]
def baseStart_3603681 : Nat := 118140960795 + 3603681 * 2 ^ 59
def prefixEnd_3603681 : Nat := 4983230072969 + 3 ^ 40 * 3603681 * 2
def baseEnd_3603681 : Nat := 411204550772271181158773

theorem tailTrace_3603681 : CollatzResearch.WordTrace tailWord_3603681 prefixEnd_3603681 411204550772271181158773 := by
  unfold tailWord_3603681
  simp only [CollatzResearch.WordTrace]
  refine ⟨131437044057486671560658897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87624696038324447707105931 131437044057486671560658897)
  ·
    refine ⟨98577783043115003670494173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131437044057486671560658897 98577783043115003670494173)
    ·
      refine ⟨36966668641168126376435315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98577783043115003670494173 36966668641168126376435315)
      ·
        refine ⟨55450002961752189564652973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36966668641168126376435315 55450002961752189564652973)
        ·
          refine ⟨20793751110657071086744865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55450002961752189564652973 20793751110657071086744865)
          ·
            refine ⟨15595313332992803315058649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20793751110657071086744865 15595313332992803315058649)
            ·
              refine ⟨11696484999744602486293987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15595313332992803315058649 11696484999744602486293987)
              ·
                refine ⟨17544727499616903729440981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11696484999744602486293987 17544727499616903729440981)
                ·
                  refine ⟨411204550772271181158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17544727499616903729440981 411204550772271181158773)
                  ·
                    rfl

theorem cell22_3603681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_3603681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603681 prefixEnd_3603681 := by exact prefixLift 3603681
  have htrace : WordTrace (prefixWord ++ tailWord_3603681) baseStart_3603681 baseEnd_3603681 := by
    simpa [prefixWord, tailWord_3603681, baseEnd_3603681] using wordTrace_append hprefix tailTrace_3603681
  have hstable : (prefixWord ++ tailWord_3603681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603681).length < 2 ^ (prefixWord ++ tailWord_3603681).sum := by decide
  have hdescent : baseEnd_3603681 < baseStart_3603681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603756 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3603756 : Nat := 118140960795 + 3603756 * 2 ^ 59
def prefixEnd_3603756 : Nat := 4983230072969 + 3 ^ 40 * 3603756 * 2
def baseEnd_3603756 : Nat := 1233639326349538347851089

theorem tailTrace_3603756 : CollatzResearch.WordTrace tailWord_3603756 prefixEnd_3603756 1233639326349538347851089 := by
  unfold tailWord_3603756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65719889766107479684819561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87626519688143306246426081 65719889766107479684819561)
  ·
    refine ⟨49289917324580609763614671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65719889766107479684819561 49289917324580609763614671)
    ·
      refine ⟨73934875986870914645422007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49289917324580609763614671 73934875986870914645422007)
      ·
        refine ⟨110902313980306371968133011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73934875986870914645422007 110902313980306371968133011)
        ·
          refine ⟨166353470970459557952199517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110902313980306371968133011 166353470970459557952199517)
          ·
            refine ⟨62382551613922334232074819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166353470970459557952199517 62382551613922334232074819)
            ·
              refine ⟨93573827420883501348112229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62382551613922334232074819 93573827420883501348112229)
              ·
                refine ⟨17545092641415656502771043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93573827420883501348112229 17545092641415656502771043)
                ·
                  refine ⟨26317638962123484754156565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17545092641415656502771043 26317638962123484754156565)
                  ·
                    refine ⟨1233639326349538347851089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26317638962123484754156565 1233639326349538347851089)
                    ·
                      rfl

theorem cell22_3603756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3603756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603756 prefixEnd_3603756 := by exact prefixLift 3603756
  have htrace : WordTrace (prefixWord ++ tailWord_3603756) baseStart_3603756 baseEnd_3603756 := by
    simpa [prefixWord, tailWord_3603756, baseEnd_3603756] using wordTrace_append hprefix tailTrace_3603756
  have hstable : (prefixWord ++ tailWord_3603756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603756).length < 2 ^ (prefixWord ++ tailWord_3603756).sum := by decide
  have hdescent : baseEnd_3603756 < baseStart_3603756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603777 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 4]
def baseStart_3603777 : Nat := 118140960795 + 3603777 * 2 ^ 59
def prefixEnd_3603777 : Nat := 4983230072969 + 3 ^ 40 * 3603777 * 2
def baseEnd_3603777 : Nat := 411215505026233764358675

theorem tailTrace_3603777 : CollatzResearch.WordTrace tailWord_3603777 prefixEnd_3603777 411215505026233764358675 := by
  unfold tailWord_3603777
  simp only [CollatzResearch.WordTrace]
  refine ⟨131440545465138879956153585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87627030310092586637435723 131440545465138879956153585)
  ·
    refine ⟨98580409098854159967115189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131440545465138879956153585 98580409098854159967115189)
    ·
      refine ⟨9241913353017577496917049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98580409098854159967115189 9241913353017577496917049)
      ·
        refine ⟨6931435014763183122687787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241913353017577496917049 6931435014763183122687787)
        ·
          refine ⟨10397152522144774684031681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6931435014763183122687787 10397152522144774684031681)
          ·
            refine ⟨7797864391608581013023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10397152522144774684031681 7797864391608581013023761)
            ·
              refine ⟨5848398293706435759767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797864391608581013023761 5848398293706435759767821)
              ·
                refine ⟨2193149360139913409912933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5848398293706435759767821 2193149360139913409912933)
                ·
                  refine ⟨411215505026233764358675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193149360139913409912933 411215505026233764358675)
                  ·
                    rfl

theorem cell22_3603777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_3603777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603777 prefixEnd_3603777 := by exact prefixLift 3603777
  have htrace : WordTrace (prefixWord ++ tailWord_3603777) baseStart_3603777 baseEnd_3603777 := by
    simpa [prefixWord, tailWord_3603777, baseEnd_3603777] using wordTrace_append hprefix tailTrace_3603777
  have hstable : (prefixWord ++ tailWord_3603777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603777).length < 2 ^ (prefixWord ++ tailWord_3603777).sum := by decide
  have hdescent : baseEnd_3603777 < baseStart_3603777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3603786 : Nat := 118140960795 + 3603786 * 2 ^ 59
def prefixEnd_3603786 : Nat := 4983230072969 + 3 ^ 40 * 3603786 * 2
def baseEnd_3603786 : Nat := 1233649595962628269600997

theorem tailTrace_3603786 : CollatzResearch.WordTrace tailWord_3603786 prefixEnd_3603786 1233649595962628269600997 := by
  unfold tailWord_3603786
  simp only [CollatzResearch.WordTrace]
  refine ⟨32860218430526568623307803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87627249148070849662154141 32860218430526568623307803)
  ·
    refine ⟨49290327645789852934961705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32860218430526568623307803 49290327645789852934961705)
    ·
      refine ⟨36967745734342389701221279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49290327645789852934961705 36967745734342389701221279)
      ·
        refine ⟨55451618601513584551831919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36967745734342389701221279 55451618601513584551831919)
        ·
          refine ⟨83177427902270376827747879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55451618601513584551831919 83177427902270376827747879)
          ·
            refine ⟨124766141853405565241621819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83177427902270376827747879 124766141853405565241621819)
            ·
              refine ⟨187149212780108347862432729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124766141853405565241621819 187149212780108347862432729)
              ·
                refine ⟨140361909585081260896824547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187149212780108347862432729 140361909585081260896824547)
                ·
                  refine ⟨210542864377621891345236821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140361909585081260896824547 210542864377621891345236821)
                  ·
                    refine ⟨1233649595962628269600997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210542864377621891345236821 1233649595962628269600997)
                    ·
                      rfl

theorem cell22_3603786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3603786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603786 prefixEnd_3603786 := by exact prefixLift 3603786
  have htrace : WordTrace (prefixWord ++ tailWord_3603786) baseStart_3603786 baseEnd_3603786 := by
    simpa [prefixWord, tailWord_3603786, baseEnd_3603786] using wordTrace_append hprefix tailTrace_3603786
  have hstable : (prefixWord ++ tailWord_3603786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603786).length < 2 ^ (prefixWord ++ tailWord_3603786).sum := by decide
  have hdescent : baseEnd_3603786 < baseStart_3603786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603801 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_3603801 : Nat := 118140960795 + 3603801 * 2 ^ 59
def prefixEnd_3603801 : Nat := 4983230072969 + 3 ^ 40 * 3603801 * 2
def baseEnd_3603801 : Nat := 1233654730769173230475951

theorem tailTrace_3603801 : CollatzResearch.WordTrace tailWord_3603801 prefixEnd_3603801 1233654730769173230475951 := by
  unfold tailWord_3603801
  simp only [CollatzResearch.WordTrace]
  refine ⟨131441420817051932055027257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87627613878034621370018171 131441420817051932055027257)
  ·
    refine ⟨98581065612788949041270443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131441420817051932055027257 98581065612788949041270443)
    ·
      refine ⟨147871598419183423561905665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98581065612788949041270443 147871598419183423561905665)
      ·
        refine ⟨110903698814387567671429249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147871598419183423561905665 110903698814387567671429249)
        ·
          refine ⟨83177774110790675753571937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110903698814387567671429249 83177774110790675753571937)
          ·
            refine ⟨62383330583093006815178953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83177774110790675753571937 62383330583093006815178953)
            ·
              refine ⟨46787497937319755111384215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62383330583093006815178953 46787497937319755111384215)
              ·
                refine ⟨70181246905979632667076323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46787497937319755111384215 70181246905979632667076323)
                ·
                  refine ⟨105271870358969449000614485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70181246905979632667076323 105271870358969449000614485)
                  ·
                    refine ⟨1233654730769173230475951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105271870358969449000614485 1233654730769173230475951)
                    ·
                      rfl

theorem cell22_3603801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_3603801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603801 prefixEnd_3603801 := by exact prefixLift 3603801
  have htrace : WordTrace (prefixWord ++ tailWord_3603801) baseStart_3603801 baseEnd_3603801 := by
    simpa [prefixWord, tailWord_3603801, baseEnd_3603801] using wordTrace_append hprefix tailTrace_3603801
  have hstable : (prefixWord ++ tailWord_3603801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603801).length < 2 ^ (prefixWord ++ tailWord_3603801).sum := by decide
  have hdescent : baseEnd_3603801 < baseStart_3603801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603820 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_3603820 : Nat := 118140960795 + 3603820 * 2 ^ 59
def prefixEnd_3603820 : Nat := 4983230072969 + 3 ^ 40 * 3603820 * 2
def baseEnd_3603820 : Nat := 1233661234857463514250893

theorem tailTrace_3603820 : CollatzResearch.WordTrace tailWord_3603820 prefixEnd_3603820 1233661234857463514250893 := by
  unfold tailWord_3603820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65721056901991549149984457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87628075869322065533312609 65721056901991549149984457)
  ·
    refine ⟨49290792676493661862488343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65721056901991549149984457 49290792676493661862488343)
    ·
      refine ⟨73936189014740492793732515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49290792676493661862488343 73936189014740492793732515)
      ·
        refine ⟨110904283522110739190598773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73936189014740492793732515 110904283522110739190598773)
        ·
          refine ⟨10397276580197881799118635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110904283522110739190598773 10397276580197881799118635)
          ·
            refine ⟨15595914870296822698677953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10397276580197881799118635 15595914870296822698677953)
            ·
              refine ⟨11696936152722617024008465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15595914870296822698677953 11696936152722617024008465)
              ·
                refine ⟨8772702114541962768006349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11696936152722617024008465 8772702114541962768006349)
                ·
                  refine ⟨3289763292953236038002381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8772702114541962768006349 3289763292953236038002381)
                  ·
                    refine ⟨1233661234857463514250893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289763292953236038002381 1233661234857463514250893)
                    ·
                      rfl

theorem cell22_3603820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_3603820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603820 prefixEnd_3603820 := by exact prefixLift 3603820
  have htrace : WordTrace (prefixWord ++ tailWord_3603820) baseStart_3603820 baseEnd_3603820 := by
    simpa [prefixWord, tailWord_3603820, baseEnd_3603820] using wordTrace_append hprefix tailTrace_3603820
  have hstable : (prefixWord ++ tailWord_3603820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603820).length < 2 ^ (prefixWord ++ tailWord_3603820).sum := by decide
  have hdescent : baseEnd_3603820 < baseStart_3603820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603854 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3603854 : Nat := 118140960795 + 3603854 * 2 ^ 59
def prefixEnd_3603854 : Nat := 4983230072969 + 3 ^ 40 * 3603854 * 2
def baseEnd_3603854 : Nat := 1233672873752298758900789

theorem tailTrace_3603854 : CollatzResearch.WordTrace tailWord_3603854 prefixEnd_3603854 1233672873752298758900789 := by
  unfold tailWord_3603854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430419235732490263338327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87628902590573281404471077 16430419235732490263338327)
  ·
    refine ⟨24645628853598735395007491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16430419235732490263338327 24645628853598735395007491)
    ·
      refine ⟨36968443280398103092511237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24645628853598735395007491 36968443280398103092511237)
      ·
        refine ⟨6931583115074644329845857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36968443280398103092511237 6931583115074644329845857)
        ·
          refine ⟨5198687336305983247384393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931583115074644329845857 5198687336305983247384393)
          ·
            refine ⟨3899015502229487435538295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198687336305983247384393 3899015502229487435538295)
            ·
              refine ⟨5848523253344231153307443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899015502229487435538295 5848523253344231153307443)
              ·
                refine ⟨8772784880016346729961165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848523253344231153307443 8772784880016346729961165)
                ·
                  refine ⟨3289794330006130023735437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8772784880016346729961165 3289794330006130023735437)
                  ·
                    refine ⟨1233672873752298758900789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289794330006130023735437 1233672873752298758900789)
                    ·
                      rfl

theorem cell22_3603854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3603854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603854 prefixEnd_3603854 := by exact prefixLift 3603854
  have htrace : WordTrace (prefixWord ++ tailWord_3603854) baseStart_3603854 baseEnd_3603854 := by
    simpa [prefixWord, tailWord_3603854, baseEnd_3603854] using wordTrace_append hprefix tailTrace_3603854
  have hstable : (prefixWord ++ tailWord_3603854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603854).length < 2 ^ (prefixWord ++ tailWord_3603854).sum := by decide
  have hdescent : baseEnd_3603854 < baseStart_3603854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603863 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3603863 : Nat := 118140960795 + 3603863 * 2 ^ 59
def prefixEnd_3603863 : Nat := 4983230072969 + 3 ^ 40 * 3603863 * 2
def baseEnd_3603863 : Nat := 1233675954636225735425761

theorem tailTrace_3603863 : CollatzResearch.WordTrace tailWord_3603863 prefixEnd_3603863 1233675954636225735425761 := by
  unfold tailWord_3603863
  simp only [CollatzResearch.WordTrace]
  refine ⟨131443682142827316643784243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87629121428551544429189495 131443682142827316643784243)
  ·
    refine ⟨197165523214240974965676365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131443682142827316643784243 197165523214240974965676365)
    ·
      refine ⟨73937071205340365612128637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197165523214240974965676365 73937071205340365612128637)
      ·
        refine ⟨27726401702002637104548239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73937071205340365612128637 27726401702002637104548239)
        ·
          refine ⟨41589602553003955656822359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27726401702002637104548239 41589602553003955656822359)
          ·
            refine ⟨62384403829505933485233539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41589602553003955656822359 62384403829505933485233539)
            ·
              refine ⟨93576605744258900227850309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62384403829505933485233539 93576605744258900227850309)
              ·
                refine ⟨17545613577048543792721933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93576605744258900227850309 17545613577048543792721933)
                ·
                  refine ⟨6579605091393203922270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17545613577048543792721933 6579605091393203922270725)
                  ·
                    refine ⟨1233675954636225735425761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6579605091393203922270725 1233675954636225735425761)
                    ·
                      rfl

theorem cell22_3603863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3603863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603863 prefixEnd_3603863 := by exact prefixLift 3603863
  have htrace : WordTrace (prefixWord ++ tailWord_3603863) baseStart_3603863 baseEnd_3603863 := by
    simpa [prefixWord, tailWord_3603863, baseEnd_3603863] using wordTrace_append hprefix tailTrace_3603863
  have hstable : (prefixWord ++ tailWord_3603863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603863).length < 2 ^ (prefixWord ++ tailWord_3603863).sum := by decide
  have hdescent : baseEnd_3603863 < baseStart_3603863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603895 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 4]
def baseStart_3603895 : Nat := 118140960795 + 3603895 * 2 ^ 59
def prefixEnd_3603895 : Nat := 4983230072969 + 3 ^ 40 * 3603895 * 2
def baseEnd_3603895 : Nat := 411228969630062772875221

theorem tailTrace_3603895 : CollatzResearch.WordTrace tailWord_3603895 prefixEnd_3603895 411228969630062772875221 := by
  unfold tailWord_3603895
  simp only [CollatzResearch.WordTrace]
  refine ⟨131444849278711386108949139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87629899519140924072632759 131444849278711386108949139)
  ·
    refine ⟨197167273918067079163423709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131444849278711386108949139 197167273918067079163423709)
    ·
      refine ⟨73937727719275154686283891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197167273918067079163423709 73937727719275154686283891)
      ·
        refine ⟨110906591578912732029425837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73937727719275154686283891 110906591578912732029425837)
        ·
          refine ⟨41589971842092274511034689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110906591578912732029425837 41589971842092274511034689)
          ·
            refine ⟨31192478881569205883276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41589971842092274511034689 31192478881569205883276017)
            ·
              refine ⟨23394359161176904412457013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31192478881569205883276017 23394359161176904412457013)
              ·
                refine ⟨2193221171360334788667845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23394359161176904412457013 2193221171360334788667845)
                ·
                  refine ⟨411228969630062772875221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193221171360334788667845 411228969630062772875221)
                  ·
                    rfl

theorem cell22_3603895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 4].length) (baseStart_3603895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603895 prefixEnd_3603895 := by exact prefixLift 3603895
  have htrace : WordTrace (prefixWord ++ tailWord_3603895) baseStart_3603895 baseEnd_3603895 := by
    simpa [prefixWord, tailWord_3603895, baseEnd_3603895] using wordTrace_append hprefix tailTrace_3603895
  have hstable : (prefixWord ++ tailWord_3603895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603895).length < 2 ^ (prefixWord ++ tailWord_3603895).sum := by decide
  have hdescent : baseEnd_3603895 < baseStart_3603895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603983 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3603983 : Nat := 118140960795 + 3603983 * 2 ^ 59
def prefixEnd_3603983 : Nat := 4983230072969 + 3 ^ 40 * 3603983 * 2
def baseEnd_3603983 : Nat := 1233717033088585422425393

theorem tailTrace_3603983 : CollatzResearch.WordTrace tailWord_3603983 prefixEnd_3603983 1233717033088585422425393 := by
  unfold tailWord_3603983
  simp only [CollatzResearch.WordTrace]
  refine ⟨131448058902392577138152603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87632039268261718092101735 131448058902392577138152603)
  ·
    refine ⟨197172088353588865707228905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131448058902392577138152603 197172088353588865707228905)
    ·
      refine ⟨147879066265191649280421679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197172088353588865707228905 147879066265191649280421679)
      ·
        refine ⟨221818599397787473920632519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147879066265191649280421679 221818599397787473920632519)
        ·
          refine ⟨332727899096681210880948779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221818599397787473920632519 332727899096681210880948779)
          ·
            refine ⟨499091848645021816321423169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332727899096681210880948779 499091848645021816321423169)
            ·
              refine ⟨374318886483766362241067377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499091848645021816321423169 374318886483766362241067377)
              ·
                refine ⟨280739164862824771680800533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374318886483766362241067377 280739164862824771680800533)
                ·
                  refine ⟨13159648352944911172537525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280739164862824771680800533 13159648352944911172537525)
                  ·
                    refine ⟨1233717033088585422425393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13159648352944911172537525 1233717033088585422425393)
                    ·
                      rfl

theorem cell22_3603983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3603983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3603983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3603983 prefixEnd_3603983 := by exact prefixLift 3603983
  have htrace : WordTrace (prefixWord ++ tailWord_3603983) baseStart_3603983 baseEnd_3603983 := by
    simpa [prefixWord, tailWord_3603983, baseEnd_3603983] using wordTrace_append hprefix tailTrace_3603983
  have hstable : (prefixWord ++ tailWord_3603983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603983).length < 2 ^ (prefixWord ++ tailWord_3603983).sum := by decide
  have hdescent : baseEnd_3603983 < baseStart_3603983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604107 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 3, 3]
def baseStart_3604107 : Nat := 118140960795 + 3604107 * 2 ^ 59
def prefixEnd_3604107 : Nat := 4983230072969 + 3 ^ 40 * 3604107 * 2
def baseEnd_3604107 : Nat := 1233759480822690432325013

theorem tailTrace_3604107 : CollatzResearch.WordTrace tailWord_3604107 prefixEnd_3604107 1233759480822690432325013 := by
  unfold tailWord_3604107
  simp only [CollatzResearch.WordTrace]
  refine ⟨131452581553943346315666575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87635054369295564210444383 131452581553943346315666575)
  ·
    refine ⟨197178872330915019473499863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131452581553943346315666575 197178872330915019473499863)
    ·
      refine ⟨295768308496372529210249795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197178872330915019473499863 295768308496372529210249795)
      ·
        refine ⟨443652462744558793815374693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295768308496372529210249795 443652462744558793815374693)
        ·
          refine ⟨83184836764604773840382755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443652462744558793815374693 83184836764604773840382755)
          ·
            refine ⟨124777255146907160760574133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83184836764604773840382755 124777255146907160760574133)
            ·
              refine ⟨11697867670022546321303825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124777255146907160760574133 11697867670022546321303825)
              ·
                refine ⟨8773400752516909740977869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11697867670022546321303825 8773400752516909740977869)
                ·
                  refine ⟨3290025282193841152866701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8773400752516909740977869 3290025282193841152866701)
                  ·
                    refine ⟨1233759480822690432325013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290025282193841152866701 1233759480822690432325013)
                    ·
                      rfl

theorem cell22_3604107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].length) (baseStart_3604107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604107 prefixEnd_3604107 := by exact prefixLift 3604107
  have htrace : WordTrace (prefixWord ++ tailWord_3604107) baseStart_3604107 baseEnd_3604107 := by
    simpa [prefixWord, tailWord_3604107, baseEnd_3604107] using wordTrace_append hprefix tailTrace_3604107
  have hstable : (prefixWord ++ tailWord_3604107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604107).length < 2 ^ (prefixWord ++ tailWord_3604107).sum := by decide
  have hdescent : baseEnd_3604107 < baseStart_3604107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604130 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3604130 : Nat := 118140960795 + 3604130 * 2 ^ 59
def prefixEnd_3604130 : Nat := 4983230072969 + 3 ^ 40 * 3604130 * 2
def baseEnd_3604130 : Nat := 1233767354192726038999943

theorem tailTrace_3604130 : CollatzResearch.WordTrace tailWord_3604130 prefixEnd_3604130 1233767354192726038999943 := by
  unfold tailWord_3604130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32863355108215005310938461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87635613621906680829169229 32863355108215005310938461)
  ·
    refine ⟨12323758165580626991601923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32863355108215005310938461 12323758165580626991601923)
    ·
      refine ⟨18485637248370940487402885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12323758165580626991601923 18485637248370940487402885)
      ·
        refine ⟨3466056984069551341388041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18485637248370940487402885 3466056984069551341388041)
        ·
          refine ⟨2599542738052163506041031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3466056984069551341388041 2599542738052163506041031)
          ·
            refine ⟨3899314107078245259061547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599542738052163506041031 3899314107078245259061547)
            ·
              refine ⟨5848971160617367888592321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899314107078245259061547 5848971160617367888592321)
              ·
                refine ⟨4386728370463025916444241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848971160617367888592321 4386728370463025916444241)
                ·
                  refine ⟨3290046277847269437333181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386728370463025916444241 3290046277847269437333181)
                  ·
                    refine ⟨1233767354192726038999943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290046277847269437333181 1233767354192726038999943)
                    ·
                      rfl

theorem cell22_3604130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3604130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604130 prefixEnd_3604130 := by exact prefixLift 3604130
  have htrace : WordTrace (prefixWord ++ tailWord_3604130) baseStart_3604130 baseEnd_3604130 := by
    simpa [prefixWord, tailWord_3604130, baseEnd_3604130] using wordTrace_append hprefix tailTrace_3604130
  have hstable : (prefixWord ++ tailWord_3604130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604130).length < 2 ^ (prefixWord ++ tailWord_3604130).sum := by decide
  have hdescent : baseEnd_3604130 < baseStart_3604130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604141 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3604141 : Nat := 118140960795 + 3604141 * 2 ^ 59
def prefixEnd_3604141 : Nat := 4983230072969 + 3 ^ 40 * 3604141 * 2
def baseEnd_3604141 : Nat := 1233771119717525676974909

theorem tailTrace_3604141 : CollatzResearch.WordTrace tailWord_3604141 prefixEnd_3604141 1233771119717525676974909 := by
  unfold tailWord_3604141
  simp only [CollatzResearch.WordTrace]
  refine ⟨131453821635820170122404277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87635881090546780081602851 131453821635820170122404277)
  ·
    refine ⟨12323795778358140948975401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131453821635820170122404277 12323795778358140948975401)
    ·
      refine ⟨9242846833768605711731551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12323795778358140948975401 9242846833768605711731551)
      ·
        refine ⟨13864270250652908567597327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9242846833768605711731551 13864270250652908567597327)
        ·
          refine ⟨20796405375979362851395991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13864270250652908567597327 20796405375979362851395991)
          ·
            refine ⟨31194608063969044277093987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20796405375979362851395991 31194608063969044277093987)
            ·
              refine ⟨46791912095953566415640981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31194608063969044277093987 46791912095953566415640981)
              ·
                refine ⟨2193370879497823425733171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46791912095953566415640981 2193370879497823425733171)
                ·
                  refine ⟨3290056319246735138599757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193370879497823425733171 3290056319246735138599757)
                  ·
                    refine ⟨1233771119717525676974909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290056319246735138599757 1233771119717525676974909)
                    ·
                      rfl

theorem cell22_3604141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3604141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604141 prefixEnd_3604141 := by exact prefixLift 3604141
  have htrace : WordTrace (prefixWord ++ tailWord_3604141) baseStart_3604141 baseEnd_3604141 := by
    simpa [prefixWord, tailWord_3604141, baseEnd_3604141] using wordTrace_append hprefix tailTrace_3604141
  have hstable : (prefixWord ++ tailWord_3604141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604141).length < 2 ^ (prefixWord ++ tailWord_3604141).sum := by decide
  have hdescent : baseEnd_3604141 < baseStart_3604141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604154 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_3604154 : Nat := 118140960795 + 3604154 * 2 ^ 59
def prefixEnd_3604154 : Nat := 4983230072969 + 3 ^ 40 * 3604154 * 2
def baseEnd_3604154 : Nat := 411258523294399325466623

theorem tailTrace_3604154 : CollatzResearch.WordTrace tailWord_3604154 prefixEnd_3604154 411258523294399325466623 := by
  unfold tailWord_3604154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32863573946193268335656879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87636197189848715561751677 32863573946193268335656879)
  ·
    refine ⟨49295360919289902503485319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32863573946193268335656879 49295360919289902503485319)
    ·
      refine ⟨73943041378934853755227979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49295360919289902503485319 73943041378934853755227979)
      ·
        refine ⟨110914562068402280632841969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73943041378934853755227979 110914562068402280632841969)
        ·
          refine ⟨83185921551301710474631477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110914562068402280632841969 83185921551301710474631477)
          ·
            refine ⟨7798680145434535356996701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83185921551301710474631477 7798680145434535356996701)
            ·
              refine ⟨2924505054537950758873763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7798680145434535356996701 2924505054537950758873763)
              ·
                refine ⟨4386757581806926138310645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924505054537950758873763 4386757581806926138310645)
                ·
                  refine ⟨411258523294399325466623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4386757581806926138310645 411258523294399325466623)
                  ·
                    rfl

theorem cell22_3604154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_3604154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604154 prefixEnd_3604154 := by exact prefixLift 3604154
  have htrace : WordTrace (prefixWord ++ tailWord_3604154) baseStart_3604154 baseEnd_3604154 := by
    simpa [prefixWord, tailWord_3604154, baseEnd_3604154] using wordTrace_append hprefix tailTrace_3604154
  have hstable : (prefixWord ++ tailWord_3604154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604154).length < 2 ^ (prefixWord ++ tailWord_3604154).sum := by decide
  have hdescent : baseEnd_3604154 < baseStart_3604154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604257 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3604257 : Nat := 118140960795 + 3604257 * 2 ^ 59
def prefixEnd_3604257 : Nat := 4983230072969 + 3 ^ 40 * 3604257 * 2
def baseEnd_3604257 : Nat := 1233810828888140041074553

theorem tailTrace_3604257 : CollatzResearch.WordTrace tailWord_3604257 prefixEnd_3604257 1233810828888140041074553 := by
  unfold tailWord_3604257
  simp only [CollatzResearch.WordTrace]
  refine ⟨131458052503399921933627025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87638701668933281289084683 131458052503399921933627025)
  ·
    refine ⟨98593539377549941450220269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131458052503399921933627025 98593539377549941450220269)
    ·
      refine ⟨36972577266581228043832601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98593539377549941450220269 36972577266581228043832601)
      ·
        refine ⟨27729432949935921032874451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36972577266581228043832601 27729432949935921032874451)
        ·
          refine ⟨41594149424903881549311677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27729432949935921032874451 41594149424903881549311677)
          ·
            refine ⟨15597806034338955580991879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41594149424903881549311677 15597806034338955580991879)
            ·
              refine ⟨23396709051508433371487819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15597806034338955580991879 23396709051508433371487819)
              ·
                refine ⟨35095063577262650057231729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23396709051508433371487819 35095063577262650057231729)
                ·
                  refine ⟨26321297682946987542923797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35095063577262650057231729 26321297682946987542923797)
                  ·
                    refine ⟨1233810828888140041074553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26321297682946987542923797 1233810828888140041074553)
                    ·
                      rfl

theorem cell22_3604257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3604257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604257 prefixEnd_3604257 := by exact prefixLift 3604257
  have htrace : WordTrace (prefixWord ++ tailWord_3604257) baseStart_3604257 baseEnd_3604257 := by
    simpa [prefixWord, tailWord_3604257, baseEnd_3604257] using wordTrace_append hprefix tailTrace_3604257
  have hstable : (prefixWord ++ tailWord_3604257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604257).length < 2 ^ (prefixWord ++ tailWord_3604257).sum := by decide
  have hdescent : baseEnd_3604257 < baseStart_3604257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604276 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3604276 : Nat := 118140960795 + 3604276 * 2 ^ 59
def prefixEnd_3604276 : Nat := 4983230072969 + 3 ^ 40 * 3604276 * 2
def baseEnd_3604276 : Nat := 1233817332976430324849495

theorem tailTrace_3604276 : CollatzResearch.WordTrace tailWord_3604276 prefixEnd_3604276 1233817332976430324849495 := by
  unfold tailWord_3604276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65729372745165544089284341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87639163660220725452379121 65729372745165544089284341)
  ·
    refine ⟨6162128694859269758370407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65729372745165544089284341 6162128694859269758370407)
    ·
      refine ⟨9243193042288904637555611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162128694859269758370407 9243193042288904637555611)
      ·
        refine ⟨13864789563433356956333417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243193042288904637555611 13864789563433356956333417)
        ·
          refine ⟨10398592172575017717250063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13864789563433356956333417 10398592172575017717250063)
          ·
            refine ⟨15597888258862526575875095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10398592172575017717250063 15597888258862526575875095)
            ·
              refine ⟨23396832388293789863812643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15597888258862526575875095 23396832388293789863812643)
              ·
                refine ⟨35095248582440684795718965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23396832388293789863812643 35095248582440684795718965)
                ·
                  refine ⟨3290179554603814199598653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35095248582440684795718965 3290179554603814199598653)
                  ·
                    refine ⟨1233817332976430324849495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290179554603814199598653 1233817332976430324849495)
                    ·
                      rfl

theorem cell22_3604276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3604276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604276 prefixEnd_3604276 := by exact prefixLift 3604276
  have htrace : WordTrace (prefixWord ++ tailWord_3604276) baseStart_3604276 baseEnd_3604276 := by
    simpa [prefixWord, tailWord_3604276, baseEnd_3604276] using wordTrace_append hprefix tailTrace_3604276
  have hstable : (prefixWord ++ tailWord_3604276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604276).length < 2 ^ (prefixWord ++ tailWord_3604276).sum := by decide
  have hdescent : baseEnd_3604276 < baseStart_3604276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604306 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3604306 : Nat := 118140960795 + 3604306 * 2 ^ 59
def prefixEnd_3604306 : Nat := 4983230072969 + 3 ^ 40 * 3604306 * 2
def baseEnd_3604306 : Nat := 411275867529840082199801

theorem tailTrace_3604306 : CollatzResearch.WordTrace tailWord_3604306 prefixEnd_3604306 411275867529840082199801 := by
  unfold tailWord_3604306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32864959920055600825540193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87639893120148268868107181 32864959920055600825540193)
  ·
    refine ⟨24648719940041700619155145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32864959920055600825540193 24648719940041700619155145)
    ·
      refine ⟨18486539955031275464366359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24648719940041700619155145 18486539955031275464366359)
      ·
        refine ⟨27729809932546913196549539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18486539955031275464366359 27729809932546913196549539)
        ·
          refine ⟨41594714898820369794824309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27729809932546913196549539 41594714898820369794824309)
          ·
            refine ⟨3899504521764409668264779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41594714898820369794824309 3899504521764409668264779)
            ·
              refine ⟨5849256782646614502397169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899504521764409668264779 5849256782646614502397169)
              ·
                refine ⟨4386942586984960876797877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5849256782646614502397169 4386942586984960876797877)
                ·
                  refine ⟨411275867529840082199801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4386942586984960876797877 411275867529840082199801)
                  ·
                    rfl

theorem cell22_3604306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3604306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604306 prefixEnd_3604306 := by exact prefixLift 3604306
  have htrace : WordTrace (prefixWord ++ tailWord_3604306) baseStart_3604306 baseEnd_3604306 := by
    simpa [prefixWord, tailWord_3604306, baseEnd_3604306] using wordTrace_append hprefix tailTrace_3604306
  have hstable : (prefixWord ++ tailWord_3604306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604306).length < 2 ^ (prefixWord ++ tailWord_3604306).sum := by decide
  have hdescent : baseEnd_3604306 < baseStart_3604306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604374 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3604374 : Nat := 118140960795 + 3604374 * 2 ^ 59
def prefixEnd_3604374 : Nat := 4983230072969 + 3 ^ 40 * 3604374 * 2
def baseEnd_3604374 : Nat := 411283626793063578633065

theorem tailTrace_3604374 : CollatzResearch.WordTrace tailWord_3604374 prefixEnd_3604374 411283626793063578633065 := by
  unfold tailWord_3604374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216394990248503182227261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87641546562650700610424117 8216394990248503182227261)
  ·
    refine ⟨3081148121343188693335223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8216394990248503182227261 3081148121343188693335223)
    ·
      refine ⟨4621722182014783040002835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081148121343188693335223 4621722182014783040002835)
      ·
        refine ⟨6932583273022174560004253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621722182014783040002835 6932583273022174560004253)
        ·
          refine ⟨2599718727383315460001595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6932583273022174560004253 2599718727383315460001595)
          ·
            refine ⟨3899578091074973190002393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599718727383315460001595 3899578091074973190002393)
            ·
              refine ⟨2924683568306229892501795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899578091074973190002393 2924683568306229892501795)
              ·
                refine ⟨4387025352459344838752693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924683568306229892501795 4387025352459344838752693)
                ·
                  refine ⟨411283626793063578633065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4387025352459344838752693 411283626793063578633065)
                  ·
                    rfl

theorem cell22_3604374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3604374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604374 prefixEnd_3604374 := by exact prefixLift 3604374
  have htrace : WordTrace (prefixWord ++ tailWord_3604374) baseStart_3604374 baseEnd_3604374 := by
    simpa [prefixWord, tailWord_3604374, baseEnd_3604374] using wordTrace_append hprefix tailTrace_3604374
  have hstable : (prefixWord ++ tailWord_3604374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604374).length < 2 ^ (prefixWord ++ tailWord_3604374).sum := by decide
  have hdescent : baseEnd_3604374 < baseStart_3604374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604383 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 2, 3]
def baseStart_3604383 : Nat := 118140960795 + 3604383 * 2 ^ 59
def prefixEnd_3604383 : Nat := 4983230072969 + 3 ^ 40 * 3604383 * 2
def baseEnd_3604383 : Nat := 1233853961263117712424167

theorem tailTrace_3604383 : CollatzResearch.WordTrace tailWord_3604383 prefixEnd_3604383 1233853961263117712424167 := by
  unfold tailWord_3604383
  simp only [CollatzResearch.WordTrace]
  refine ⟨131462648100943445452713803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87641765400628963635142535 131462648100943445452713803)
  ·
    refine ⟨197193972151415168179070705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131462648100943445452713803 197193972151415168179070705)
    ·
      refine ⟨147895479113561376134303029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197193972151415168179070705 147895479113561376134303029)
      ·
        refine ⟨13865201166896379012590909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147895479113561376134303029 13865201166896379012590909)
        ·
          refine ⟨5199450437586142129721591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13865201166896379012590909 5199450437586142129721591)
          ·
            refine ⟨7799175656379213194582387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199450437586142129721591 7799175656379213194582387)
            ·
              refine ⟨11698763484568819791873581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799175656379213194582387 11698763484568819791873581)
              ·
                refine ⟨4387036306713307421952593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11698763484568819791873581 4387036306713307421952593)
                ·
                  refine ⟨3290277230034980566464445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387036306713307421952593 3290277230034980566464445)
                  ·
                    refine ⟨1233853961263117712424167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290277230034980566464445 1233853961263117712424167)
                    ·
                      rfl

theorem cell22_3604383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_3604383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604383 prefixEnd_3604383 := by exact prefixLift 3604383
  have htrace : WordTrace (prefixWord ++ tailWord_3604383) baseStart_3604383 baseEnd_3604383 := by
    simpa [prefixWord, tailWord_3604383, baseEnd_3604383] using wordTrace_append hprefix tailTrace_3604383
  have hstable : (prefixWord ++ tailWord_3604383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604383).length < 2 ^ (prefixWord ++ tailWord_3604383).sum := by decide
  have hdescent : baseEnd_3604383 < baseStart_3604383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604439 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3604439 : Nat := 118140960795 + 3604439 * 2 ^ 59
def prefixEnd_3604439 : Nat := 4983230072969 + 3 ^ 40 * 3604439 * 2
def baseEnd_3604439 : Nat := 1233873131207552233023995

theorem tailTrace_3604439 : CollatzResearch.WordTrace tailWord_3604439 prefixEnd_3604439 1233873131207552233023995 := by
  unfold tailWord_3604439
  simp only [CollatzResearch.WordTrace]
  refine ⟨131464690588740567016752371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87643127059160378011168247 131464690588740567016752371)
  ·
    refine ⟨197197035883110850525128557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131464690588740567016752371 197197035883110850525128557)
    ·
      refine ⟨73948888456166568946923209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197197035883110850525128557 73948888456166568946923209)
      ·
        refine ⟨55461666342124926710192407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73948888456166568946923209 55461666342124926710192407)
        ·
          refine ⟨83192499513187390065288611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55461666342124926710192407 83192499513187390065288611)
          ·
            refine ⟨124788749269781085097932917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83192499513187390065288611 124788749269781085097932917)
            ·
              refine ⟨11698945244041976727931211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124788749269781085097932917 11698945244041976727931211)
              ·
                refine ⟨17548417866062965091896817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698945244041976727931211 17548417866062965091896817)
                ·
                  refine ⟨13161313399547223818922613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17548417866062965091896817 13161313399547223818922613)
                  ·
                    refine ⟨1233873131207552233023995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13161313399547223818922613 1233873131207552233023995)
                    ·
                      rfl

theorem cell22_3604439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3604439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604439 prefixEnd_3604439 := by exact prefixLift 3604439
  have htrace : WordTrace (prefixWord ++ tailWord_3604439) baseStart_3604439 baseEnd_3604439 := by
    simpa [prefixWord, tailWord_3604439, baseEnd_3604439] using wordTrace_append hprefix tailTrace_3604439
  have hstable : (prefixWord ++ tailWord_3604439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604439).length < 2 ^ (prefixWord ++ tailWord_3604439).sum := by decide
  have hdescent : baseEnd_3604439 < baseStart_3604439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604499 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_3604499 : Nat := 118140960795 + 3604499 * 2 ^ 59
def prefixEnd_3604499 : Nat := 4983230072969 + 3 ^ 40 * 3604499 * 2
def baseEnd_3604499 : Nat := 1233893670433732076523811

theorem tailTrace_3604499 : CollatzResearch.WordTrace tailWord_3604499 prefixEnd_3604499 1233893670433732076523811 := by
  unfold tailWord_3604499
  simp only [CollatzResearch.WordTrace]
  refine ⟨131466878968523197263936551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87644585979015464842624367 131466878968523197263936551)
  ·
    refine ⟨197200318452784795895904827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131466878968523197263936551 197200318452784795895904827)
    ·
      refine ⟨295800477679177193843857241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197200318452784795895904827 295800477679177193843857241)
      ·
        refine ⟨221850358259382895382892931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295800477679177193843857241 221850358259382895382892931)
        ·
          refine ⟨332775537389074343074339397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221850358259382895382892931 332775537389074343074339397)
          ·
            refine ⟨62395413260451439326438637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332775537389074343074339397 62395413260451439326438637)
            ·
              refine ⟨23398279972669289747414489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62395413260451439326438637 23398279972669289747414489)
              ·
                refine ⟨17548709979501967310560867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23398279972669289747414489 17548709979501967310560867)
                ·
                  refine ⟨26323064969252950965841301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17548709979501967310560867 26323064969252950965841301)
                  ·
                    refine ⟨1233893670433732076523811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26323064969252950965841301 1233893670433732076523811)
                    ·
                      rfl

theorem cell22_3604499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_3604499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604499 prefixEnd_3604499 := by exact prefixLift 3604499
  have htrace : WordTrace (prefixWord ++ tailWord_3604499) baseStart_3604499 baseEnd_3604499 := by
    simpa [prefixWord, tailWord_3604499, baseEnd_3604499] using wordTrace_append hprefix tailTrace_3604499
  have hstable : (prefixWord ++ tailWord_3604499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604499).length < 2 ^ (prefixWord ++ tailWord_3604499).sum := by decide
  have hdescent : baseEnd_3604499 < baseStart_3604499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604640 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_3604640 : Nat := 118140960795 + 3604640 * 2 ^ 59
def prefixEnd_3604640 : Nat := 4983230072969 + 3 ^ 40 * 3604640 * 2
def baseEnd_3604640 : Nat := 1233941937615254708748379

theorem tailTrace_3604640 : CollatzResearch.WordTrace tailWord_3604640 prefixEnd_3604640 1233941937615254708748379 := by
  unfold tailWord_3604640
  simp only [CollatzResearch.WordTrace]
  refine ⟨65736010830506189172409687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87648014440674918896546249 65736010830506189172409687)
  ·
    refine ⟨98604016245759283758614531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65736010830506189172409687 98604016245759283758614531)
    ·
      refine ⟨147906024368638925637921797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98604016245759283758614531 147906024368638925637921797)
      ·
        refine ⟨27732379569119798557110337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147906024368638925637921797 27732379569119798557110337)
        ·
          refine ⟨20799284676839848917832753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27732379569119798557110337 20799284676839848917832753)
          ·
            refine ⟨15599463507629886688374565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20799284676839848917832753 15599463507629886688374565)
            ·
              refine ⟨2924899407680603754070231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15599463507629886688374565 2924899407680603754070231)
              ·
                refine ⟨4387349111520905631105347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924899407680603754070231 4387349111520905631105347)
                ·
                  refine ⟨6581023667281358446658021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387349111520905631105347 6581023667281358446658021)
                  ·
                    refine ⟨1233941937615254708748379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581023667281358446658021 1233941937615254708748379)
                    ·
                      rfl

theorem cell22_3604640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_3604640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604640 prefixEnd_3604640 := by exact prefixLift 3604640
  have htrace : WordTrace (prefixWord ++ tailWord_3604640) baseStart_3604640 baseEnd_3604640 := by
    simpa [prefixWord, tailWord_3604640, baseEnd_3604640] using wordTrace_append hprefix tailTrace_3604640
  have hstable : (prefixWord ++ tailWord_3604640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604640).length < 2 ^ (prefixWord ++ tailWord_3604640).sum := by decide
  have hdescent : baseEnd_3604640 < baseStart_3604640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604674 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3604674 : Nat := 118140960795 + 3604674 * 2 ^ 59
def prefixEnd_3604674 : Nat := 4983230072969 + 3 ^ 40 * 3604674 * 2
def baseEnd_3604674 : Nat := 1233953576510089953398275

theorem tailTrace_3604674 : CollatzResearch.WordTrace tailWord_3604674 prefixEnd_3604674 1233953576510089953398275 := by
  unfold tailWord_3604674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868315435722300537889269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87648841161926134767704717 32868315435722300537889269)
  ·
    refine ⟨3081404572098965675427119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32868315435722300537889269 3081404572098965675427119)
    ·
      refine ⟨4622106858148448513140679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081404572098965675427119 4622106858148448513140679)
      ·
        refine ⟨6933160287222672769711019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622106858148448513140679 6933160287222672769711019)
        ·
          refine ⟨10399740430834009154566529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933160287222672769711019 10399740430834009154566529)
          ·
            refine ⟨7799805323125506865924897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10399740430834009154566529 7799805323125506865924897)
            ·
              refine ⟨5849853992344130149443673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799805323125506865924897 5849853992344130149443673)
              ·
                refine ⟨4387390494258097612082755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5849853992344130149443673 4387390494258097612082755)
                ·
                  refine ⟨6581085741387146418124133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387390494258097612082755 6581085741387146418124133)
                  ·
                    refine ⟨1233953576510089953398275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581085741387146418124133 1233953576510089953398275)
                    ·
                      rfl

theorem cell22_3604674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3604674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604674 prefixEnd_3604674 := by exact prefixLift 3604674
  have htrace : WordTrace (prefixWord ++ tailWord_3604674) baseStart_3604674 baseEnd_3604674 := by
    simpa [prefixWord, tailWord_3604674, baseEnd_3604674] using wordTrace_append hprefix tailTrace_3604674
  have hstable : (prefixWord ++ tailWord_3604674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604674).length < 2 ^ (prefixWord ++ tailWord_3604674).sum := by decide
  have hdescent : baseEnd_3604674 < baseStart_3604674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
