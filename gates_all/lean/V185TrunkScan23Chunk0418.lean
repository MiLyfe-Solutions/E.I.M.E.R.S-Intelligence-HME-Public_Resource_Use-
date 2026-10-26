import V185TrunkScan23Chunk0417

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2470638 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_2470638 : Nat := 118140960795 + 2470638 * 2 ^ 59
def prefixEnd_2470638 : Nat := 4983230072969 + 3 ^ 40 * 2470638 * 2
def baseEnd_2470638 : Nat := 140958313029223316795861

theorem tailTrace_2470638 : CollatzResearch.WordTrace tailWord_2470638 prefixEnd_2470638 140958313029223316795861 := by
  unfold tailWord_2470638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263946352913494027780571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60074380548871968148163045 11263946352913494027780571)
  ·
    refine ⟨16895919529370241041670857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11263946352913494027780571 16895919529370241041670857)
    ·
      refine ⟨12671939647027680781253143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16895919529370241041670857 12671939647027680781253143)
      ·
        refine ⟨19007909470541521171879715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12671939647027680781253143 19007909470541521171879715)
        ·
          refine ⟨28511864205812281757819573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19007909470541521171879715 28511864205812281757819573)
          ·
            refine ⟨2672987269294901414795585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28511864205812281757819573 2672987269294901414795585)
            ·
              refine ⟨2004740451971176061096689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672987269294901414795585 2004740451971176061096689)
              ·
                refine ⟨1503555338978382045822517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004740451971176061096689 1503555338978382045822517)
                ·
                  refine ⟨140958313029223316795861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503555338978382045822517 140958313029223316795861)
                  ·
                    rfl

theorem cell23_2470638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_2470638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470638 prefixEnd_2470638 := by exact prefixLift 2470638
  have htrace : WordTrace (prefixWord ++ tailWord_2470638) baseStart_2470638 baseEnd_2470638 := by
    simpa [prefixWord, tailWord_2470638, baseEnd_2470638] using wordTrace_append hprefix tailTrace_2470638
  have hstable : (prefixWord ++ tailWord_2470638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470638).length < 2 ^ (prefixWord ++ tailWord_2470638).sum := by decide
  have hdescent : baseEnd_2470638 < baseStart_2470638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470664 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_2470664 : Nat := 118140960795 + 2470664 * 2 ^ 59
def prefixEnd_2470664 : Nat := 4983230072969 + 3 ^ 40 * 2470664 * 2
def baseEnd_2470664 : Nat := 422879389253342249812543

theorem tailTrace_2470664 : CollatzResearch.WordTrace tailWord_2470664 prefixEnd_2470664 422879389253342249812543 := by
  unfold tailWord_2470664
  simp only [CollatzResearch.WordTrace]
  refine ⟨45056259560606879331345523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60075012747475839108460697 45056259560606879331345523)
  ·
    refine ⟨67584389340910318997018285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45056259560606879331345523 67584389340910318997018285)
    ·
      refine ⟨25344146002841369623881857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67584389340910318997018285 25344146002841369623881857)
      ·
        refine ⟨19008109502131027217911393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25344146002841369623881857 19008109502131027217911393)
        ·
          refine ⟨14256082126598270413433545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19008109502131027217911393 14256082126598270413433545)
          ·
            refine ⟨10692061594948702810075159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14256082126598270413433545 10692061594948702810075159)
            ·
              refine ⟨16038092392423054215112739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10692061594948702810075159 16038092392423054215112739)
              ·
                refine ⟨24057138588634581322669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16038092392423054215112739 24057138588634581322669109)
                ·
                  refine ⟨2255356742684491999000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24057138588634581322669109 2255356742684491999000229)
                  ·
                    refine ⟨422879389253342249812543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255356742684491999000229 422879389253342249812543)
                    ·
                      rfl

theorem cell23_2470664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_2470664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470664 prefixEnd_2470664 := by exact prefixLift 2470664
  have htrace : WordTrace (prefixWord ++ tailWord_2470664) baseStart_2470664 baseEnd_2470664 := by
    simpa [prefixWord, tailWord_2470664, baseEnd_2470664] using wordTrace_append hprefix tailTrace_2470664
  have hstable : (prefixWord ++ tailWord_2470664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470664).length < 2 ^ (prefixWord ++ tailWord_2470664).sum := by decide
  have hdescent : baseEnd_2470664 < baseStart_2470664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470677 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 8]
def baseStart_2470677 : Nat := 118140960795 + 2470677 * 2 ^ 59
def prefixEnd_2470677 : Nat := 4983230072969 + 3 ^ 40 * 2470677 * 2
def baseEnd_2470677 : Nat := 140960538112059466508341

theorem tailTrace_2470677 : CollatzResearch.WordTrace tailWord_2470677 prefixEnd_2470677 140960538112059466508341 := by
  unfold tailWord_2470677
  simp only [CollatzResearch.WordTrace]
  refine ⟨90112993270166661882914285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60075328846777774588609523 90112993270166661882914285)
  ·
    refine ⟨33792372476312498206092857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90112993270166661882914285 33792372476312498206092857)
    ·
      refine ⟨25344279357234373654569643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33792372476312498206092857 25344279357234373654569643)
      ·
        refine ⟨38016419035851560481854465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25344279357234373654569643 38016419035851560481854465)
        ·
          refine ⟨28512314276888670361390849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38016419035851560481854465 28512314276888670361390849)
          ·
            refine ⟨21384235707666502771043137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28512314276888670361390849 21384235707666502771043137)
            ·
              refine ⟨16038176780749877078282353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21384235707666502771043137 16038176780749877078282353)
              ·
                refine ⟨12028632585562407808711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16038176780749877078282353 12028632585562407808711765)
                ·
                  refine ⟨140960538112059466508341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12028632585562407808711765 140960538112059466508341)
                  ·
                    rfl

theorem cell23_2470677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_2470677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470677 prefixEnd_2470677 := by exact prefixLift 2470677
  have htrace : WordTrace (prefixWord ++ tailWord_2470677) baseStart_2470677 baseEnd_2470677 := by
    simpa [prefixWord, tailWord_2470677, baseEnd_2470677] using wordTrace_append hprefix tailTrace_2470677
  have hstable : (prefixWord ++ tailWord_2470677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470677).length < 2 ^ (prefixWord ++ tailWord_2470677).sum := by decide
  have hdescent : baseEnd_2470677 < baseStart_2470677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470748 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2470748 : Nat := 118140960795 + 2470748 * 2 ^ 59
def prefixEnd_2470748 : Nat := 4983230072969 + 3 ^ 40 * 2470748 * 2
def baseEnd_2470748 : Nat := 1268681300135004420787243

theorem tailTrace_2470748 : CollatzResearch.WordTrace tailWord_2470748 prefixEnd_2470748 1268681300135004420787243 := by
  unfold tailWord_2470748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45057791426454720504374449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60077055235272960672499265 45057791426454720504374449)
  ·
    refine ⟨33793343569841040378280837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45057791426454720504374449 33793343569841040378280837)
    ·
      refine ⟨6336251919345195070927657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33793343569841040378280837 6336251919345195070927657)
      ·
        refine ⟨4752188939508896303195743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6336251919345195070927657 4752188939508896303195743)
        ·
          refine ⟨7128283409263344454793615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752188939508896303195743 7128283409263344454793615)
          ·
            refine ⟨10692425113895016682190423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7128283409263344454793615 10692425113895016682190423)
            ·
              refine ⟨16038637670842525023285635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10692425113895016682190423 16038637670842525023285635)
              ·
                refine ⟨24057956506263787534928453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16038637670842525023285635 24057956506263787534928453)
                ·
                  refine ⟨4510866844924460162799085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24057956506263787534928453 4510866844924460162799085)
                  ·
                    refine ⟨1691575066846672561049657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4510866844924460162799085 1691575066846672561049657)
                    ·
                      refine ⟨1268681300135004420787243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691575066846672561049657 1268681300135004420787243)
                      ·
                        rfl

theorem cell23_2470748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2470748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470748 prefixEnd_2470748 := by exact prefixLift 2470748
  have htrace : WordTrace (prefixWord ++ tailWord_2470748) baseStart_2470748 baseEnd_2470748 := by
    simpa [prefixWord, tailWord_2470748, baseEnd_2470748] using wordTrace_append hprefix tailTrace_2470748
  have hstable : (prefixWord ++ tailWord_2470748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470748).length < 2 ^ (prefixWord ++ tailWord_2470748).sum := by decide
  have hdescent : baseEnd_2470748 < baseStart_2470748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470764 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2470764 : Nat := 118140960795 + 2470764 * 2 ^ 59
def prefixEnd_2470764 : Nat := 4983230072969 + 3 ^ 40 * 2470764 * 2
def baseEnd_2470764 : Nat := 1268689515825476358187169

theorem tailTrace_2470764 : CollatzResearch.WordTrace tailWord_2470764 prefixEnd_2470764 1268689515825476358187169 := by
  unfold tailWord_2470764
  simp only [CollatzResearch.WordTrace]
  refine ⟨45058083210425737870665673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60077444280567650494220897 45058083210425737870665673)
  ·
    refine ⟨33793562407819303402999255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45058083210425737870665673 33793562407819303402999255)
    ·
      refine ⟨50690343611728955104498883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33793562407819303402999255 50690343611728955104498883)
      ·
        refine ⟨76035515417593432656748325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50690343611728955104498883 76035515417593432656748325)
        ·
          refine ⟨14256659140798768623140311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76035515417593432656748325 14256659140798768623140311)
          ·
            refine ⟨21384988711198152934710467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14256659140798768623140311 21384988711198152934710467)
            ·
              refine ⟨32077483066797229402065701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21384988711198152934710467 32077483066797229402065701)
              ·
                refine ⟨6014528075024480512887319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32077483066797229402065701 6014528075024480512887319)
                ·
                  refine ⟨9021792112536720769330979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6014528075024480512887319 9021792112536720769330979)
                  ·
                    refine ⟨13532688168805081153996469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9021792112536720769330979 13532688168805081153996469)
                    ·
                      refine ⟨1268689515825476358187169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13532688168805081153996469 1268689515825476358187169)
                      ·
                        rfl

theorem cell23_2470764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2470764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470764 prefixEnd_2470764 := by exact prefixLift 2470764
  have htrace : WordTrace (prefixWord ++ tailWord_2470764) baseStart_2470764 baseEnd_2470764 := by
    simpa [prefixWord, tailWord_2470764, baseEnd_2470764] using wordTrace_append hprefix tailTrace_2470764
  have hstable : (prefixWord ++ tailWord_2470764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470764).length < 2 ^ (prefixWord ++ tailWord_2470764).sum := by decide
  have hdescent : baseEnd_2470764 < baseStart_2470764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470782 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2470782 : Nat := 118140960795 + 2470782 * 2 ^ 59
def prefixEnd_2470782 : Nat := 4983230072969 + 3 ^ 40 * 2470782 * 2
def baseEnd_2470782 : Nat := 1268698758477257287762087

theorem tailTrace_2470782 : CollatzResearch.WordTrace tailWord_2470782 prefixEnd_2470782 1268698758477257287762087 := by
  unfold tailWord_2470782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11264602866848283101935825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60077881956524176543657733 11264602866848283101935825)
  ·
    refine ⟨8448452150136212326451869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11264602866848283101935825 8448452150136212326451869)
    ·
      refine ⟨3168169556301079622419451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8448452150136212326451869 3168169556301079622419451)
      ·
        refine ⟨4752254334451619433629177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168169556301079622419451 4752254334451619433629177)
        ·
          refine ⟨3564190750838714575221883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4752254334451619433629177 3564190750838714575221883)
          ·
            refine ⟨5346286126258071862832825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564190750838714575221883 5346286126258071862832825)
            ·
              refine ⟨4009714594693553897124619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5346286126258071862832825 4009714594693553897124619)
              ·
                refine ⟨6014571892040330845686929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009714594693553897124619 6014571892040330845686929)
                ·
                  refine ⟨4510928919030248134265197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6014571892040330845686929 4510928919030248134265197)
                  ·
                    refine ⟨1691598344636343050349449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4510928919030248134265197 1691598344636343050349449)
                    ·
                      refine ⟨1268698758477257287762087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691598344636343050349449 1268698758477257287762087)
                      ·
                        rfl

theorem cell23_2470782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2470782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470782 prefixEnd_2470782 := by exact prefixLift 2470782
  have htrace : WordTrace (prefixWord ++ tailWord_2470782) baseStart_2470782 baseEnd_2470782 := by
    simpa [prefixWord, tailWord_2470782, baseEnd_2470782] using wordTrace_append hprefix tailTrace_2470782
  have hstable : (prefixWord ++ tailWord_2470782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470782).length < 2 ^ (prefixWord ++ tailWord_2470782).sum := by decide
  have hdescent : baseEnd_2470782 < baseStart_2470782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470791 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2470791 : Nat := 118140960795 + 2470791 * 2 ^ 59
def prefixEnd_2470791 : Nat := 4983230072969 + 3 ^ 40 * 2470791 * 2
def baseEnd_2470791 : Nat := 1268703379803147752549545

theorem tailTrace_2470791 : CollatzResearch.WordTrace tailWord_2470791 prefixEnd_2470791 1268703379803147752549545 := by
  unfold tailWord_2470791
  simp only [CollatzResearch.WordTrace]
  refine ⟨90117151191753659352564227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60078100794502439568376151 90117151191753659352564227)
  ·
    refine ⟨135175726787630489028846341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90117151191753659352564227 135175726787630489028846341)
    ·
      refine ⟨25345448772680716692908689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135175726787630489028846341 25345448772680716692908689)
      ·
        refine ⟨19009086579510537519681517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25345448772680716692908689 19009086579510537519681517)
        ·
          refine ⟨7128407467316451569880569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19009086579510537519681517 7128407467316451569880569)
          ·
            refine ⟨5346305600487338677410427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7128407467316451569880569 5346305600487338677410427)
            ·
              refine ⟨8019458400731008016115641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346305600487338677410427 8019458400731008016115641)
              ·
                refine ⟨6014593800548256012086731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8019458400731008016115641 6014593800548256012086731)
                ·
                  refine ⟨9021890700822384018130097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6014593800548256012086731 9021890700822384018130097)
                  ·
                    refine ⟨6766418025616788013597573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9021890700822384018130097 6766418025616788013597573)
                    ·
                      refine ⟨1268703379803147752549545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6766418025616788013597573 1268703379803147752549545)
                      ·
                        rfl

theorem cell23_2470791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2470791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470791 prefixEnd_2470791 := by exact prefixLift 2470791
  have htrace : WordTrace (prefixWord ++ tailWord_2470791) baseStart_2470791 baseEnd_2470791 := by
    simpa [prefixWord, tailWord_2470791, baseEnd_2470791] using wordTrace_append hprefix tailTrace_2470791
  have hstable : (prefixWord ++ tailWord_2470791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470791).length < 2 ^ (prefixWord ++ tailWord_2470791).sum := by decide
  have hdescent : baseEnd_2470791 < baseStart_2470791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470806 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2470806 : Nat := 118140960795 + 2470806 * 2 ^ 59
def prefixEnd_2470806 : Nat := 4983230072969 + 3 ^ 40 * 2470806 * 2
def baseEnd_2470806 : Nat := 1268711082012965193861977

theorem tailTrace_2470806 : CollatzResearch.WordTrace tailWord_2470806 prefixEnd_2470806 1268711082012965193861977 := by
  unfold tailWord_2470806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632356142918707307147517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60078465524466211276240181 5632356142918707307147517)
  ·
    refine ⟨2112133553594515240180319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5632356142918707307147517 2112133553594515240180319)
    ·
      refine ⟨3168200330391772860270479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112133553594515240180319 3168200330391772860270479)
      ·
        refine ⟨4752300495587659290405719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168200330391772860270479 4752300495587659290405719)
        ·
          refine ⟨7128450743381488935608579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752300495587659290405719 7128450743381488935608579)
          ·
            refine ⟨10692676115072233403412869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7128450743381488935608579 10692676115072233403412869)
            ·
              refine ⟨2004876771576043763139913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10692676115072233403412869 2004876771576043763139913)
              ·
                refine ⟨1503657578682032822354935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004876771576043763139913 1503657578682032822354935)
                ·
                  refine ⟨2255486368023049233532403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503657578682032822354935 2255486368023049233532403)
                  ·
                    refine ⟨3383229552034573850298605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255486368023049233532403 3383229552034573850298605)
                    ·
                      refine ⟨1268711082012965193861977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3383229552034573850298605 1268711082012965193861977)
                      ·
                        rfl

theorem cell23_2470806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2470806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470806 prefixEnd_2470806 := by exact prefixLift 2470806
  have htrace : WordTrace (prefixWord ++ tailWord_2470806) baseStart_2470806 baseEnd_2470806 := by
    simpa [prefixWord, tailWord_2470806, baseEnd_2470806] using wordTrace_append hprefix tailTrace_2470806
  have hstable : (prefixWord ++ tailWord_2470806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470806).length < 2 ^ (prefixWord ++ tailWord_2470806).sum := by decide
  have hdescent : baseEnd_2470806 < baseStart_2470806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470855 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_2470855 : Nat := 118140960795 + 2470855 * 2 ^ 59
def prefixEnd_2470855 : Nat := 4983230072969 + 3 ^ 40 * 2470855 * 2
def baseEnd_2470855 : Nat := 1268736242565035502149251

theorem tailTrace_2470855 : CollatzResearch.WordTrace tailWord_2470855 prefixEnd_2470855 1268736242565035502149251 := by
  unfold tailWord_2470855
  simp only [CollatzResearch.WordTrace]
  refine ⟨90119485463521798282894019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60079656975681198855262679 90119485463521798282894019)
  ·
    refine ⟨135179228195282697424341029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90119485463521798282894019 135179228195282697424341029)
    ·
      refine ⟨25346105286615505767063943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135179228195282697424341029 25346105286615505767063943)
      ·
        refine ⟨38019157929923258650595915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25346105286615505767063943 38019157929923258650595915)
        ·
          refine ⟨57028736894884887975893873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38019157929923258650595915 57028736894884887975893873)
          ·
            refine ⟨42771552671163665981920405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57028736894884887975893873 42771552671163665981920405)
            ·
              refine ⟨2004916531460796842902519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42771552671163665981920405 2004916531460796842902519)
              ·
                refine ⟨3007374797191195264353779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004916531460796842902519 3007374797191195264353779)
                ·
                  refine ⟨4511062195786792896530669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007374797191195264353779 4511062195786792896530669)
                  ·
                    refine ⟨1691648323420047336199001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4511062195786792896530669 1691648323420047336199001)
                    ·
                      refine ⟨1268736242565035502149251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691648323420047336199001 1268736242565035502149251)
                      ·
                        rfl

theorem cell23_2470855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_2470855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470855 prefixEnd_2470855 := by exact prefixLift 2470855
  have htrace : WordTrace (prefixWord ++ tailWord_2470855) baseStart_2470855 baseEnd_2470855 := by
    simpa [prefixWord, tailWord_2470855, baseEnd_2470855] using wordTrace_append hprefix tailTrace_2470855
  have hstable : (prefixWord ++ tailWord_2470855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470855).length < 2 ^ (prefixWord ++ tailWord_2470855).sum := by decide
  have hdescent : baseEnd_2470855 < baseStart_2470855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470908 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 5]
def baseStart_2470908 : Nat := 118140960795 + 2470908 * 2 ^ 59
def prefixEnd_2470908 : Nat := 4983230072969 + 3 ^ 40 * 2470908 * 2
def baseEnd_2470908 : Nat := 140973717448858199420723

theorem tailTrace_2470908 : CollatzResearch.WordTrace tailWord_2470908 prefixEnd_2470908 140973717448858199420723 := by
  unfold tailWord_2470908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45060709266164894167286689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60080945688219858889715585 45060709266164894167286689)
  ·
    refine ⟨33795531949623670625465017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45060709266164894167286689 33795531949623670625465017)
    ·
      refine ⟨25346648962217752969098763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33795531949623670625465017 25346648962217752969098763)
      ·
        refine ⟨38019973443326629453648145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25346648962217752969098763 38019973443326629453648145)
        ·
          refine ⟨28514980082494972090236109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38019973443326629453648145 28514980082494972090236109)
          ·
            refine ⟨10693117530935614533838541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28514980082494972090236109 10693117530935614533838541)
            ·
              refine ⟨4009919074100855450189453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10693117530935614533838541 4009919074100855450189453)
              ·
                refine ⟨1503719652787820793821045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4009919074100855450189453 1503719652787820793821045)
                ·
                  refine ⟨140973717448858199420723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503719652787820793821045 140973717448858199420723)
                  ·
                    rfl

theorem cell23_2470908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_2470908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470908 prefixEnd_2470908 := by exact prefixLift 2470908
  have htrace : WordTrace (prefixWord ++ tailWord_2470908) baseStart_2470908 baseEnd_2470908 := by
    simpa [prefixWord, tailWord_2470908, baseEnd_2470908] using wordTrace_append hprefix tailTrace_2470908
  have hstable : (prefixWord ++ tailWord_2470908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470908).length < 2 ^ (prefixWord ++ tailWord_2470908).sum := by decide
  have hdescent : baseEnd_2470908 < baseStart_2470908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470911 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 7, 2]
def baseStart_2470911 : Nat := 118140960795 + 2470911 * 2 ^ 59
def prefixEnd_2470911 : Nat := 4983230072969 + 3 ^ 40 * 2470911 * 2
def baseEnd_2470911 : Nat := 1268764997481687283048993

theorem tailTrace_2470911 : CollatzResearch.WordTrace tailWord_2470911 prefixEnd_2470911 1268764997481687283048993 := by
  unfold tailWord_2470911
  simp only [CollatzResearch.WordTrace]
  refine ⟨90121527951318919846932587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60081018634212613231288391 90121527951318919846932587)
  ·
    refine ⟨135182291926978379770398881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90121527951318919846932587 135182291926978379770398881)
    ·
      refine ⟨101386718945233784827799161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135182291926978379770398881 101386718945233784827799161)
      ·
        refine ⟨76040039208925338620849371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101386718945233784827799161 76040039208925338620849371)
        ·
          refine ⟨114060058813388007931274057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76040039208925338620849371 114060058813388007931274057)
          ·
            refine ⟨85545044110041005948455543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114060058813388007931274057 85545044110041005948455543)
            ·
              refine ⟨128317566165061508922683315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85545044110041005948455543 128317566165061508922683315)
              ·
                refine ⟨192476349247592263384024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128317566165061508922683315 192476349247592263384024973)
                ·
                  refine ⟨72178630967847098769009365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192476349247592263384024973 72178630967847098769009365)
                  ·
                    refine ⟨1691686663308916377398657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72178630967847098769009365 1691686663308916377398657)
                    ·
                      refine ⟨1268764997481687283048993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691686663308916377398657 1268764997481687283048993)
                      ·
                        rfl

theorem cell23_2470911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_2470911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470911 prefixEnd_2470911 := by exact prefixLift 2470911
  have htrace : WordTrace (prefixWord ++ tailWord_2470911) baseStart_2470911 baseEnd_2470911 := by
    simpa [prefixWord, tailWord_2470911, baseEnd_2470911] using wordTrace_append hprefix tailTrace_2470911
  have hstable : (prefixWord ++ tailWord_2470911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470911).length < 2 ^ (prefixWord ++ tailWord_2470911).sum := by decide
  have hdescent : baseEnd_2470911 < baseStart_2470911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470981 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 6]
def baseStart_2470981 : Nat := 118140960795 + 2470981 * 2 ^ 59
def prefixEnd_2470981 : Nat := 4983230072969 + 3 ^ 40 * 2470981 * 2
def baseEnd_2470981 : Nat := 140977882347500223241519

theorem tailTrace_2470981 : CollatzResearch.WordTrace tailWord_2470981 prefixEnd_2470981 140977882347500223241519 := by
  unfold tailWord_2470981
  simp only [CollatzResearch.WordTrace]
  refine ⟨90124081061065321801980797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60082720707376881201320531 90124081061065321801980797)
  ·
    refine ⟨33796530397899495675742799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90124081061065321801980797 33796530397899495675742799)
    ·
      refine ⟨50694795596849243513614199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33796530397899495675742799 50694795596849243513614199)
      ·
        refine ⟨76042193395273865270421299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50694795596849243513614199 76042193395273865270421299)
        ·
          refine ⟨114063290092910797905631949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76042193395273865270421299 114063290092910797905631949)
          ·
            refine ⟨42773733784841549214611981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114063290092910797905631949 42773733784841549214611981)
            ·
              refine ⟨16040150169315580955479493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42773733784841549214611981 16040150169315580955479493)
              ·
                refine ⟨3007528156746671429152405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16040150169315580955479493 3007528156746671429152405)
                ·
                  refine ⟨140977882347500223241519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3007528156746671429152405 140977882347500223241519)
                  ·
                    rfl

theorem cell23_2470981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_2470981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470981 prefixEnd_2470981 := by exact prefixLift 2470981
  have htrace : WordTrace (prefixWord ++ tailWord_2470981) baseStart_2470981 baseEnd_2470981 := by
    simpa [prefixWord, tailWord_2470981, baseEnd_2470981] using wordTrace_append hprefix tailTrace_2470981
  have hstable : (prefixWord ++ tailWord_2470981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470981).length < 2 ^ (prefixWord ++ tailWord_2470981).sum := by decide
  have hdescent : baseEnd_2470981 < baseStart_2470981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471082 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2471082 : Nat := 118140960795 + 2471082 * 2 ^ 59
def prefixEnd_2471082 : Nat := 4983230072969 + 3 ^ 40 * 2471082 * 2
def baseEnd_2471082 : Nat := 1268852802673606114010707

theorem tailTrace_2471082 : CollatzResearch.WordTrace tailWord_2471082 prefixEnd_2471082 1268852802673606114010707 := by
  unfold tailWord_2471082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22531941208424854012851875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60085176555799610700938333 22531941208424854012851875)
  ·
    refine ⟨33797911812637281019277813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22531941208424854012851875 33797911812637281019277813)
    ·
      refine ⟨3168554232434745095557295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33797911812637281019277813 3168554232434745095557295)
      ·
        refine ⟨4752831348652117643335943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168554232434745095557295 4752831348652117643335943)
        ·
          refine ⟨7129247022978176465003915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752831348652117643335943 7129247022978176465003915)
          ·
            refine ⟨10693870534467264697505873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129247022978176465003915 10693870534467264697505873)
            ·
              refine ⟨8020402900850448523129405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10693870534467264697505873 8020402900850448523129405)
              ·
                refine ⟨3007651087818918196173527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8020402900850448523129405 3007651087818918196173527)
                ·
                  refine ⟨4511476631728377294260291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007651087818918196173527 4511476631728377294260291)
                  ·
                    refine ⟨6767214947592565941390437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511476631728377294260291 6767214947592565941390437)
                    ·
                      refine ⟨1268852802673606114010707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6767214947592565941390437 1268852802673606114010707)
                      ·
                        rfl

theorem cell23_2471082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2471082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471082 prefixEnd_2471082 := by exact prefixLift 2471082
  have htrace : WordTrace (prefixWord ++ tailWord_2471082) baseStart_2471082 baseEnd_2471082 := by
    simpa [prefixWord, tailWord_2471082, baseEnd_2471082] using wordTrace_append hprefix tailTrace_2471082
  have hstable : (prefixWord ++ tailWord_2471082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471082).length < 2 ^ (prefixWord ++ tailWord_2471082).sum := by decide
  have hdescent : baseEnd_2471082 < baseStart_2471082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471105 : List Nat := [1, 2, 6, 1, 1, 2, 2, 8]
def baseStart_2471105 : Nat := 118140960795 + 2471105 * 2 ^ 59
def prefixEnd_2471105 : Nat := 4983230072969 + 3 ^ 40 * 2471105 * 2
def baseEnd_2471105 : Nat := 46994985656617019408263

theorem tailTrace_2471105 : CollatzResearch.WordTrace tailWord_2471105 prefixEnd_2471105 46994985656617019408263 := by
  unfold tailWord_2471105
  simp only [CollatzResearch.WordTrace]
  refine ⟨90128603712616090979494769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60085735808410727319663179 90128603712616090979494769)
  ·
    refine ⟨67596452784462068234621077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90128603712616090979494769 67596452784462068234621077)
    ·
      refine ⟨3168583724271659448497863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67596452784462068234621077 3168583724271659448497863)
      ·
        refine ⟨4752875586407489172746795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168583724271659448497863 4752875586407489172746795)
        ·
          refine ⟨7129313379611233759120193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752875586407489172746795 7129313379611233759120193)
          ·
            refine ⟨5346985034708425319340145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7129313379611233759120193 5346985034708425319340145)
            ·
              refine ⟨4010238776031318989505109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5346985034708425319340145 4010238776031318989505109)
              ·
                refine ⟨46994985656617019408263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4010238776031318989505109 46994985656617019408263)
                ·
                  rfl

theorem cell23_2471105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 8].length) (baseStart_2471105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471105 prefixEnd_2471105 := by exact prefixLift 2471105
  have htrace : WordTrace (prefixWord ++ tailWord_2471105) baseStart_2471105 baseEnd_2471105 := by
    simpa [prefixWord, tailWord_2471105, baseEnd_2471105] using wordTrace_append hprefix tailTrace_2471105
  have hstable : (prefixWord ++ tailWord_2471105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471105).length < 2 ^ (prefixWord ++ tailWord_2471105).sum := by decide
  have hdescent : baseEnd_2471105 < baseStart_2471105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471121 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_2471121 : Nat := 118140960795 + 2471121 * 2 ^ 59
def prefixEnd_2471121 : Nat := 4983230072969 + 3 ^ 40 * 2471121 * 2
def baseEnd_2471121 : Nat := 1268872828419131461423027

theorem tailTrace_2471121 : CollatzResearch.WordTrace tailWord_2471121 prefixEnd_2471121 1268872828419131461423027 := by
  unfold tailWord_2471121
  simp only [CollatzResearch.WordTrace]
  refine ⟨90129187280558125712077217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60086124853705417141384811 90129187280558125712077217)
  ·
    refine ⟨67596890460418594284057913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90129187280558125712077217 67596890460418594284057913)
    ·
      refine ⟨50697667845313945713043435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67596890460418594284057913 50697667845313945713043435)
      ·
        refine ⟨76046501767970918569565153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50697667845313945713043435 76046501767970918569565153)
        ·
          refine ⟨57034876325978188927173865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76046501767970918569565153 57034876325978188927173865)
          ·
            refine ⟨42776157244483641695380399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57034876325978188927173865 42776157244483641695380399)
            ·
              refine ⟨64164235866725462543070599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42776157244483641695380399 64164235866725462543070599)
              ·
                refine ⟨96246353800088193814605899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64164235866725462543070599 96246353800088193814605899)
                ·
                  refine ⟨144369530700132290721908849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96246353800088193814605899 144369530700132290721908849)
                  ·
                    refine ⟨108277148025099218041431637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144369530700132290721908849 108277148025099218041431637)
                    ·
                      refine ⟨1268872828419131461423027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 108277148025099218041431637 1268872828419131461423027)
                      ·
                        rfl

theorem cell23_2471121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_2471121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471121 prefixEnd_2471121 := by exact prefixLift 2471121
  have htrace : WordTrace (prefixWord ++ tailWord_2471121) baseStart_2471121 baseEnd_2471121 := by
    simpa [prefixWord, tailWord_2471121, baseEnd_2471121] using wordTrace_append hprefix tailTrace_2471121
  have hstable : (prefixWord ++ tailWord_2471121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471121).length < 2 ^ (prefixWord ++ tailWord_2471121).sum := by decide
  have hdescent : baseEnd_2471121 < baseStart_2471121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471149 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2471149 : Nat := 118140960795 + 2471149 * 2 ^ 59
def prefixEnd_2471149 : Nat := 4983230072969 + 3 ^ 40 * 2471149 * 2
def baseEnd_2471149 : Nat := 1268887205877457351872899

theorem tailTrace_2471149 : CollatzResearch.WordTrace tailWord_2471149 prefixEnd_2471149 1268887205877457351872899 := by
  unfold tailWord_2471149
  simp only [CollatzResearch.WordTrace]
  refine ⟨90130208524456686494096501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60086805682971124329397667 90130208524456686494096501)
  ·
    refine ⟨8449707049167814358821547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90130208524456686494096501 8449707049167814358821547)
    ·
      refine ⟨12674560573751721538232321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8449707049167814358821547 12674560573751721538232321)
      ·
        refine ⟨9505920430313791153674241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12674560573751721538232321 9505920430313791153674241)
        ·
          refine ⟨7129440322735343365255681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9505920430313791153674241 7129440322735343365255681)
          ·
            refine ⟨5347080242051507523941761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7129440322735343365255681 5347080242051507523941761)
            ·
              refine ⟨4010310181538630642956321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347080242051507523941761 4010310181538630642956321)
              ·
                refine ⟨3007732636153972982217241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4010310181538630642956321 3007732636153972982217241)
                ·
                  refine ⟨2255799477115479736662931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007732636153972982217241 2255799477115479736662931)
                  ·
                    refine ⟨3383699215673219604994397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255799477115479736662931 3383699215673219604994397)
                    ·
                      refine ⟨1268887205877457351872899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3383699215673219604994397 1268887205877457351872899)
                      ·
                        rfl

theorem cell23_2471149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2471149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471149 prefixEnd_2471149 := by exact prefixLift 2471149
  have htrace : WordTrace (prefixWord ++ tailWord_2471149) baseStart_2471149 baseEnd_2471149 := by
    simpa [prefixWord, tailWord_2471149, baseEnd_2471149] using wordTrace_append hprefix tailTrace_2471149
  have hstable : (prefixWord ++ tailWord_2471149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471149).length < 2 ^ (prefixWord ++ tailWord_2471149).sum := by decide
  have hdescent : baseEnd_2471149 < baseStart_2471149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471156 : List Nat := [2, 6, 1, 2, 2, 1, 1, 8]
def baseStart_2471156 : Nat := 118140960795 + 2471156 * 2 ^ 59
def prefixEnd_2471156 : Nat := 4983230072969 + 3 ^ 40 * 2471156 * 2
def baseEnd_2471156 : Nat := 46995955564519956462421

theorem tailTrace_2471156 : CollatzResearch.WordTrace tailWord_2471156 prefixEnd_2471156 46995955564519956462421 := by
  unfold tailWord_2471156
  simp only [CollatzResearch.WordTrace]
  refine ⟨45065231917715663344800661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60086975890287551126400881 45065231917715663344800661)
  ·
    refine ⟨2112432746142921719287531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45065231917715663344800661 2112432746142921719287531)
    ·
      refine ⟨3168649119214382578931297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112432746142921719287531 3168649119214382578931297)
      ·
        refine ⟨2376486839410786934198473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3168649119214382578931297 2376486839410786934198473)
        ·
          refine ⟨1782365129558090200648855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2376486839410786934198473 1782365129558090200648855)
          ·
            refine ⟨2673547694337135300973283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782365129558090200648855 2673547694337135300973283)
            ·
              refine ⟨4010321541505702951459925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673547694337135300973283 4010321541505702951459925)
              ·
                refine ⟨46995955564519956462421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4010321541505702951459925 46995955564519956462421)
                ·
                  rfl

theorem cell23_2471156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 8].length) (baseStart_2471156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471156 prefixEnd_2471156 := by exact prefixLift 2471156
  have htrace : WordTrace (prefixWord ++ tailWord_2471156) baseStart_2471156 baseEnd_2471156 := by
    simpa [prefixWord, tailWord_2471156, baseEnd_2471156] using wordTrace_append hprefix tailTrace_2471156
  have hstable : (prefixWord ++ tailWord_2471156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471156).length < 2 ^ (prefixWord ++ tailWord_2471156).sum := by decide
  have hdescent : baseEnd_2471156 < baseStart_2471156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471172 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2471172 : Nat := 118140960795 + 2471172 * 2 ^ 59
def prefixEnd_2471172 : Nat := 4983230072969 + 3 ^ 40 * 2471172 * 2
def baseEnd_2471172 : Nat := 1268899015932510761885293

theorem tailTrace_2471172 : CollatzResearch.WordTrace tailWord_2471172 prefixEnd_2471172 1268899015932510761885293 := by
  unfold tailWord_2471172
  simp only [CollatzResearch.WordTrace]
  refine ⟨45065523701686680711091885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60087364935582240948122513 45065523701686680711091885)
  ·
    refine ⟨16899571388132505266659457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45065523701686680711091885 16899571388132505266659457)
    ·
      refine ⟨12674678541099378949994593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16899571388132505266659457 12674678541099378949994593)
      ·
        refine ⟨9506008905824534212495945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12674678541099378949994593 9506008905824534212495945)
        ·
          refine ⟨7129506679368400659371959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9506008905824534212495945 7129506679368400659371959)
          ·
            refine ⟨10694260019052600989057939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129506679368400659371959 10694260019052600989057939)
            ·
              refine ⟨16041390028578901483586909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10694260019052600989057939 16041390028578901483586909)
              ·
                refine ⟨6015521260717088056345091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16041390028578901483586909 6015521260717088056345091)
                ·
                  refine ⟨9023281891075632084517637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015521260717088056345091 9023281891075632084517637)
                  ·
                    refine ⟨1691865354576681015847057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9023281891075632084517637 1691865354576681015847057)
                    ·
                      refine ⟨1268899015932510761885293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691865354576681015847057 1268899015932510761885293)
                      ·
                        rfl

theorem cell23_2471172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2471172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471172 prefixEnd_2471172 := by exact prefixLift 2471172
  have htrace : WordTrace (prefixWord ++ tailWord_2471172) baseStart_2471172 baseEnd_2471172 := by
    simpa [prefixWord, tailWord_2471172, baseEnd_2471172] using wordTrace_append hprefix tailTrace_2471172
  have hstable : (prefixWord ++ tailWord_2471172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471172).length < 2 ^ (prefixWord ++ tailWord_2471172).sum := by decide
  have hdescent : baseEnd_2471172 < baseStart_2471172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471205 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_2471205 : Nat := 118140960795 + 2471205 * 2 ^ 59
def prefixEnd_2471205 : Nat := 4983230072969 + 3 ^ 40 * 2471205 * 2
def baseEnd_2471205 : Nat := 1268915960794109132772641

theorem tailTrace_2471205 : CollatzResearch.WordTrace tailWord_2471205 prefixEnd_2471205 1268915960794109132772641 := by
  unfold tailWord_2471205
  simp only [CollatzResearch.WordTrace]
  refine ⟨90132251012253808058135069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60088167341502538705423379 90132251012253808058135069)
  ·
    refine ⟨33799594129595178021800651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90132251012253808058135069 33799594129595178021800651)
    ·
      refine ⟨50699391194392767032700977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33799594129595178021800651 50699391194392767032700977)
      ·
        refine ⟨38024543395794575274525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50699391194392767032700977 38024543395794575274525733)
        ·
          refine ⟨7129601886711482863973575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38024543395794575274525733 7129601886711482863973575)
          ·
            refine ⟨10694402830067224295960363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129601886711482863973575 10694402830067224295960363)
            ·
              refine ⟨16041604245100836443940545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10694402830067224295960363 16041604245100836443940545)
              ·
                refine ⟨12031203183825627332955409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16041604245100836443940545 12031203183825627332955409)
                ·
                  refine ⟨9023402387869220499716557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12031203183825627332955409 9023402387869220499716557)
                  ·
                    refine ⟨3383775895450957687393709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9023402387869220499716557 3383775895450957687393709)
                    ·
                      refine ⟨1268915960794109132772641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3383775895450957687393709 1268915960794109132772641)
                      ·
                        rfl

theorem cell23_2471205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_2471205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471205 prefixEnd_2471205 := by exact prefixLift 2471205
  have htrace : WordTrace (prefixWord ++ tailWord_2471205) baseStart_2471205 baseEnd_2471205 := by
    simpa [prefixWord, tailWord_2471205, baseEnd_2471205] using wordTrace_append hprefix tailTrace_2471205
  have hstable : (prefixWord ++ tailWord_2471205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471205).length < 2 ^ (prefixWord ++ tailWord_2471205).sum := by decide
  have hdescent : baseEnd_2471205 < baseStart_2471205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471258 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2471258 : Nat := 118140960795 + 2471258 * 2 ^ 59
def prefixEnd_2471258 : Nat := 4983230072969 + 3 ^ 40 * 2471258 * 2
def baseEnd_2471258 : Nat := 1268943175268797425409897

theorem tailTrace_2471258 : CollatzResearch.WordTrace tailWord_2471258 prefixEnd_2471258 1268943175268797425409897 := by
  unfold tailWord_2471258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22533546020265449527453607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60089456054041198739876285 22533546020265449527453607)
  ·
    refine ⟨33800319030398174291180411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22533546020265449527453607 33800319030398174291180411)
    ·
      refine ⟨50700478545597261436770617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33800319030398174291180411 50700478545597261436770617)
      ·
        refine ⟨38025358909197946077577963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50700478545597261436770617 38025358909197946077577963)
        ·
          refine ⟨57038038363796919116366945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38025358909197946077577963 57038038363796919116366945)
          ·
            refine ⟨42778528772847689337275209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57038038363796919116366945 42778528772847689337275209)
            ·
              refine ⟨32083896579635767002956407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42778528772847689337275209 32083896579635767002956407)
              ·
                refine ⟨48125844869453650504434611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32083896579635767002956407 48125844869453650504434611)
                ·
                  refine ⟨72188767304180475756651917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48125844869453650504434611 72188767304180475756651917)
                  ·
                    refine ⟨27070787739067678408744469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72188767304180475756651917 27070787739067678408744469)
                    ·
                      refine ⟨1268943175268797425409897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27070787739067678408744469 1268943175268797425409897)
                      ·
                        rfl

theorem cell23_2471258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2471258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471258 prefixEnd_2471258 := by exact prefixLift 2471258
  have htrace : WordTrace (prefixWord ++ tailWord_2471258) baseStart_2471258 baseEnd_2471258 := by
    simpa [prefixWord, tailWord_2471258, baseEnd_2471258] using wordTrace_append hprefix tailTrace_2471258
  have hstable : (prefixWord ++ tailWord_2471258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471258).length < 2 ^ (prefixWord ++ tailWord_2471258).sum := by decide
  have hdescent : baseEnd_2471258 < baseStart_2471258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471386 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_2471386 : Nat := 118140960795 + 2471386 * 2 ^ 59
def prefixEnd_2471386 : Nat := 4983230072969 + 3 ^ 40 * 2471386 * 2
def baseEnd_2471386 : Nat := 1269008900792572924609309

theorem tailTrace_2471386 : CollatzResearch.WordTrace tailWord_2471386 prefixEnd_2471386 1269008900792572924609309 := by
  unfold tailWord_2471386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22534713156149518992618503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60092568416398717313649341 22534713156149518992618503)
  ·
    refine ⟨33802069734224278488927755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22534713156149518992618503 33802069734224278488927755)
    ·
      refine ⟨50703104601336417733391633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33802069734224278488927755 50703104601336417733391633)
      ·
        refine ⟨38027328451002313300043725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50703104601336417733391633 38027328451002313300043725)
        ·
          refine ⟨14260248169125867487516397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38027328451002313300043725 14260248169125867487516397)
          ·
            refine ⟨5347593063422200307818649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14260248169125867487516397 5347593063422200307818649)
            ·
              refine ⟨4010694797566650230863987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347593063422200307818649 4010694797566650230863987)
              ·
                refine ⟨6016042196349975346295981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010694797566650230863987 6016042196349975346295981)
                ·
                  refine ⟨2256015823631240754860993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6016042196349975346295981 2256015823631240754860993)
                  ·
                    refine ⟨1692011867723430566145745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256015823631240754860993 1692011867723430566145745)
                    ·
                      refine ⟨1269008900792572924609309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692011867723430566145745 1269008900792572924609309)
                      ·
                        rfl

theorem cell23_2471386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_2471386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471386 prefixEnd_2471386 := by exact prefixLift 2471386
  have htrace : WordTrace (prefixWord ++ tailWord_2471386) baseStart_2471386 baseEnd_2471386 := by
    simpa [prefixWord, tailWord_2471386, baseEnd_2471386] using wordTrace_append hprefix tailTrace_2471386
  have hstable : (prefixWord ++ tailWord_2471386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471386).length < 2 ^ (prefixWord ++ tailWord_2471386).sum := by decide
  have hdescent : baseEnd_2471386 < baseStart_2471386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471399 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2471399 : Nat := 118140960795 + 2471399 * 2 ^ 59
def prefixEnd_2471399 : Nat := 4983230072969 + 3 ^ 40 * 2471399 * 2
def baseEnd_2471399 : Nat := 1269015576041081373746749

theorem tailTrace_2471399 : CollatzResearch.WordTrace tailWord_2471399 prefixEnd_2471399 1269015576041081373746749 := by
  unfold tailWord_2471399
  simp only [CollatzResearch.WordTrace]
  refine ⟨90139326773550979190697251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60092884515700652793798167 90139326773550979190697251)
  ·
    refine ⟨135208990160326468786045877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90139326773550979190697251 135208990160326468786045877)
    ·
      refine ⟨12675842827530606448691801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135208990160326468786045877 12675842827530606448691801)
      ·
        refine ⟨9506882120647954836518851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12675842827530606448691801 9506882120647954836518851)
        ·
          refine ⟨14260323180971932254778277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9506882120647954836518851 14260323180971932254778277)
          ·
            refine ⟨2673810596432237297770927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14260323180971932254778277 2673810596432237297770927)
            ·
              refine ⟨4010715894648355946656391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673810596432237297770927 4010715894648355946656391)
              ·
                refine ⟨6016073841972533919984587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010715894648355946656391 6016073841972533919984587)
                ·
                  refine ⟨9024110762958800879976881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016073841972533919984587 9024110762958800879976881)
                  ·
                    refine ⟨6768083072219100659982661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9024110762958800879976881 6768083072219100659982661)
                    ·
                      refine ⟨1269015576041081373746749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6768083072219100659982661 1269015576041081373746749)
                      ·
                        rfl

theorem cell23_2471399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2471399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471399 prefixEnd_2471399 := by exact prefixLift 2471399
  have htrace : WordTrace (prefixWord ++ tailWord_2471399) baseStart_2471399 baseEnd_2471399 := by
    simpa [prefixWord, tailWord_2471399, baseEnd_2471399] using wordTrace_append hprefix tailTrace_2471399
  have hstable : (prefixWord ++ tailWord_2471399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471399).length < 2 ^ (prefixWord ++ tailWord_2471399).sum := by decide
  have hdescent : baseEnd_2471399 < baseStart_2471399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471437 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2471437 : Nat := 118140960795 + 2471437 * 2 ^ 59
def prefixEnd_2471437 : Nat := 4983230072969 + 3 ^ 40 * 2471437 * 2
def baseEnd_2471437 : Nat := 1269035088305952225071575

theorem tailTrace_2471437 : CollatzResearch.WordTrace tailWord_2471437 prefixEnd_2471437 1269035088305952225071575 := by
  unfold tailWord_2471437
  simp only [CollatzResearch.WordTrace]
  refine ⟨90140712747413311680580565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60093808498275541120387043 90140712747413311680580565)
  ·
    refine ⟨2112672955017499492513607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90140712747413311680580565 2112672955017499492513607)
    ·
      refine ⟨3169009432526249238770411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112672955017499492513607 3169009432526249238770411)
      ·
        refine ⟨4753514148789373858155617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169009432526249238770411 4753514148789373858155617)
        ·
          refine ⟨3565135611592030393616713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4753514148789373858155617 3565135611592030393616713)
          ·
            refine ⟨2673851708694022795212535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565135611592030393616713 2673851708694022795212535)
            ·
              refine ⟨4010777563041034192818803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673851708694022795212535 4010777563041034192818803)
              ·
                refine ⟨6016166344561551289228205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010777563041034192818803 6016166344561551289228205)
                ·
                  refine ⟨2256062379210581733460577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6016166344561551289228205 2256062379210581733460577)
                  ·
                    refine ⟨1692046784407936300095433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256062379210581733460577 1692046784407936300095433)
                    ·
                      refine ⟨1269035088305952225071575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692046784407936300095433 1269035088305952225071575)
                      ·
                        rfl

theorem cell23_2471437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2471437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471437 prefixEnd_2471437 := by exact prefixLift 2471437
  have htrace : WordTrace (prefixWord ++ tailWord_2471437) baseStart_2471437 baseEnd_2471437 := by
    simpa [prefixWord, tailWord_2471437, baseEnd_2471437] using wordTrace_append hprefix tailTrace_2471437
  have hstable : (prefixWord ++ tailWord_2471437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471437).length < 2 ^ (prefixWord ++ tailWord_2471437).sum := by decide
  have hdescent : baseEnd_2471437 < baseStart_2471437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471559 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 3, 4]
def baseStart_2471559 : Nat := 118140960795 + 2471559 * 2 ^ 59
def prefixEnd_2471559 : Nat := 4983230072969 + 3 ^ 40 * 2471559 * 2
def baseEnd_2471559 : Nat := 423032577648600249248671

theorem tailTrace_2471559 : CollatzResearch.WordTrace tailWord_2471559 prefixEnd_2471559 423032577648600249248671 := by
  unfold tailWord_2471559
  simp only [CollatzResearch.WordTrace]
  refine ⟨90145162452971326516521731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60096774968647551011014487 90145162452971326516521731)
  ·
    refine ⟨135217743679456989774782597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90145162452971326516521731 135217743679456989774782597)
    ·
      refine ⟨25353326939898185582771737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135217743679456989774782597 25353326939898185582771737)
      ·
        refine ⟨19014995204923639187078803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25353326939898185582771737 19014995204923639187078803)
        ·
          refine ⟨28522492807385458780618205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19014995204923639187078803 28522492807385458780618205)
          ·
            refine ⟨10695934802769547042731827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28522492807385458780618205 10695934802769547042731827)
            ·
              refine ⟨16043902204154320564097741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10695934802769547042731827 16043902204154320564097741)
              ·
                refine ⟨6016463326557870211536653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16043902204154320564097741 6016463326557870211536653)
                ·
                  refine ⟨2256173747459201329326245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6016463326557870211536653 2256173747459201329326245)
                  ·
                    refine ⟨423032577648600249248671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256173747459201329326245 423032577648600249248671)
                    ·
                      rfl

theorem cell23_2471559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_2471559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471559 prefixEnd_2471559 := by exact prefixLift 2471559
  have htrace : WordTrace (prefixWord ++ tailWord_2471559) baseStart_2471559 baseEnd_2471559 := by
    simpa [prefixWord, tailWord_2471559, baseEnd_2471559] using wordTrace_append hprefix tailTrace_2471559
  have hstable : (prefixWord ++ tailWord_2471559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471559).length < 2 ^ (prefixWord ++ tailWord_2471559).sum := by decide
  have hdescent : baseEnd_2471559 < baseStart_2471559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471566 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2471566 : Nat := 118140960795 + 2471566 * 2 ^ 59
def prefixEnd_2471566 : Nat := 4983230072969 + 3 ^ 40 * 2471566 * 2
def baseEnd_2471566 : Nat := 1269101327310382220358481

theorem tailTrace_2471566 : CollatzResearch.WordTrace tailWord_2471566 prefixEnd_2471566 1269101327310382220358481 := by
  unfold tailWord_2471566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268177220493245839003319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60096945175963977808017701 11268177220493245839003319)
  ·
    refine ⟨16902265830739868758504979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11268177220493245839003319 16902265830739868758504979)
    ·
      refine ⟨25353398746109803137757469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16902265830739868758504979 25353398746109803137757469)
      ·
        refine ⟨9507524529791176176659051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25353398746109803137757469 9507524529791176176659051)
        ·
          refine ⟨14261286794686764264988577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9507524529791176176659051 14261286794686764264988577)
          ·
            refine ⟨10695965096015073198741433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261286794686764264988577 10695965096015073198741433)
            ·
              refine ⟨8021973822011304899056075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10695965096015073198741433 8021973822011304899056075)
              ·
                refine ⟨12032960733016957348584113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021973822011304899056075 12032960733016957348584113)
                ·
                  refine ⟨9024720549762718011438085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12032960733016957348584113 9024720549762718011438085)
                  ·
                    refine ⟨1692135103080509627144641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9024720549762718011438085 1692135103080509627144641)
                    ·
                      refine ⟨1269101327310382220358481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692135103080509627144641 1269101327310382220358481)
                      ·
                        rfl

theorem cell23_2471566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2471566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471566 prefixEnd_2471566 := by exact prefixLift 2471566
  have htrace : WordTrace (prefixWord ++ tailWord_2471566) baseStart_2471566 baseEnd_2471566 := by
    simpa [prefixWord, tailWord_2471566, baseEnd_2471566] using wordTrace_append hprefix tailTrace_2471566
  have hstable : (prefixWord ++ tailWord_2471566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471566).length < 2 ^ (prefixWord ++ tailWord_2471566).sum := by decide
  have hdescent : baseEnd_2471566 < baseStart_2471566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471606 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2471606 : Nat := 118140960795 + 2471606 * 2 ^ 59
def prefixEnd_2471606 : Nat := 4983230072969 + 3 ^ 40 * 2471606 * 2
def baseEnd_2471606 : Nat := 141013540726284673762033

theorem tailTrace_2471606 : CollatzResearch.WordTrace tailWord_2471606 prefixEnd_2471606 141013540726284673762033 := by
  unfold tailWord_2471606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634179792737565846467667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60097917789200702362321781 5634179792737565846467667)
  ·
    refine ⟨8451269689106348769701501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634179792737565846467667 8451269689106348769701501)
    ·
      refine ⟨3169226133414880788638063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8451269689106348769701501 3169226133414880788638063)
      ·
        refine ⟨4753839200122321182957095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169226133414880788638063 4753839200122321182957095)
        ·
          refine ⟨7130758800183481774435643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753839200122321182957095 7130758800183481774435643)
          ·
            refine ⟨10696138200275222661653465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7130758800183481774435643 10696138200275222661653465)
            ·
              refine ⟨8022103650206416996240099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696138200275222661653465 8022103650206416996240099)
              ·
                refine ⟨12033155475309625494360149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022103650206416996240099 12033155475309625494360149)
                ·
                  refine ⟨141013540726284673762033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12033155475309625494360149 141013540726284673762033)
                  ·
                    rfl

theorem cell23_2471606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2471606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471606 prefixEnd_2471606 := by exact prefixLift 2471606
  have htrace : WordTrace (prefixWord ++ tailWord_2471606) baseStart_2471606 baseEnd_2471606 := by
    simpa [prefixWord, tailWord_2471606, baseEnd_2471606] using wordTrace_append hprefix tailTrace_2471606
  have hstable : (prefixWord ++ tailWord_2471606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471606).length < 2 ^ (prefixWord ++ tailWord_2471606).sum := by decide
  have hdescent : baseEnd_2471606 < baseStart_2471606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471636 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2471636 : Nat := 118140960795 + 2471636 * 2 ^ 59
def prefixEnd_2471636 : Nat := 4983230072969 + 3 ^ 40 * 2471636 * 2
def baseEnd_2471636 : Nat := 423045756985398982161053

theorem tailTrace_2471636 : CollatzResearch.WordTrace tailWord_2471636 prefixEnd_2471636 423045756985398982161053 := by
  unfold tailWord_2471636
  simp only [CollatzResearch.WordTrace]
  refine ⟨45073985436846184333537381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60098647249128245778049841 45073985436846184333537381)
  ·
    refine ⟨8451372269408659562538259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45073985436846184333537381 8451372269408659562538259)
    ·
      refine ⟨12677058404112989343807389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451372269408659562538259 12677058404112989343807389)
      ·
        refine ⟨4753896901542371003927771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12677058404112989343807389 4753896901542371003927771)
        ·
          refine ⟨7130845352313556505891657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753896901542371003927771 7130845352313556505891657)
          ·
            refine ⟨5348134014235167379418743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130845352313556505891657 5348134014235167379418743)
            ·
              refine ⟨8022201021352751069128115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348134014235167379418743 8022201021352751069128115)
              ·
                refine ⟨12033301532029126603692173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022201021352751069128115 12033301532029126603692173)
                ·
                  refine ⟨4512488074510922476384565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12033301532029126603692173 4512488074510922476384565)
                  ·
                    refine ⟨423045756985398982161053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4512488074510922476384565 423045756985398982161053)
                    ·
                      rfl

theorem cell23_2471636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2471636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471636 prefixEnd_2471636 := by exact prefixLift 2471636
  have htrace : WordTrace (prefixWord ++ tailWord_2471636) baseStart_2471636 baseEnd_2471636 := by
    simpa [prefixWord, tailWord_2471636, baseEnd_2471636] using wordTrace_append hprefix tailTrace_2471636
  have hstable : (prefixWord ++ tailWord_2471636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471636).length < 2 ^ (prefixWord ++ tailWord_2471636).sum := by decide
  have hdescent : baseEnd_2471636 < baseStart_2471636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471639 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2471639 : Nat := 118140960795 + 2471639 * 2 ^ 59
def prefixEnd_2471639 : Nat := 4983230072969 + 3 ^ 40 * 2471639 * 2
def baseEnd_2471639 : Nat := 1269138811398160434745645

theorem tailTrace_2471639 : CollatzResearch.WordTrace tailWord_2471639 prefixEnd_2471639 1269138811398160434745645 := by
  unfold tailWord_2471639
  simp only [CollatzResearch.WordTrace]
  refine ⟨90148080292681500179433971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60098720195121000119622647 90148080292681500179433971)
  ·
    refine ⟨135222120439022250269150957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90148080292681500179433971 135222120439022250269150957)
    ·
      refine ⟨50708295164633343850931609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135222120439022250269150957 50708295164633343850931609)
      ·
        refine ⟨38031221373475007888198707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50708295164633343850931609 38031221373475007888198707)
        ·
          refine ⟨57046832060212511832298061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38031221373475007888198707 57046832060212511832298061)
          ·
            refine ⟨21392562022579691937111773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57046832060212511832298061 21392562022579691937111773)
            ·
              refine ⟨8022210758467384476416915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21392562022579691937111773 8022210758467384476416915)
              ·
                refine ⟨12033316137701076714625373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022210758467384476416915 12033316137701076714625373)
                ·
                  refine ⟨4512493551637903767984515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12033316137701076714625373 4512493551637903767984515)
                  ·
                    refine ⟨6768740327456855651976773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4512493551637903767984515 6768740327456855651976773)
                    ·
                      refine ⟨1269138811398160434745645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6768740327456855651976773 1269138811398160434745645)
                      ·
                        rfl

theorem cell23_2471639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2471639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471639 prefixEnd_2471639 := by exact prefixLift 2471639
  have htrace : WordTrace (prefixWord ++ tailWord_2471639) baseStart_2471639 baseEnd_2471639 := by
    simpa [prefixWord, tailWord_2471639, baseEnd_2471639] using wordTrace_append hprefix tailTrace_2471639
  have hstable : (prefixWord ++ tailWord_2471639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471639).length < 2 ^ (prefixWord ++ tailWord_2471639).sum := by decide
  have hdescent : baseEnd_2471639 < baseStart_2471639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471659 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5]
def baseStart_2471659 : Nat := 118140960795 + 2471659 * 2 ^ 59
def prefixEnd_2471659 : Nat := 4983230072969 + 3 ^ 40 * 2471659 * 2
def baseEnd_2471659 : Nat := 1269149081011250356495553

theorem tailTrace_2471659 : CollatzResearch.WordTrace tailWord_2471659 prefixEnd_2471659 1269149081011250356495553 := by
  unfold tailWord_2471659
  simp only [CollatzResearch.WordTrace]
  refine ⟨90148809752609043595162031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60099206501739362396774687 90148809752609043595162031)
  ·
    refine ⟨135223214628913565392743047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90148809752609043595162031 135223214628913565392743047)
    ·
      refine ⟨202834821943370348089114571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135223214628913565392743047 202834821943370348089114571)
      ·
        refine ⟨304252232915055522133671857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202834821943370348089114571 304252232915055522133671857)
        ·
          refine ⟨228189174686291641600253893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304252232915055522133671857 228189174686291641600253893)
          ·
            refine ⟨42785470253679682800047605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228189174686291641600253893 42785470253679682800047605)
            ·
              refine ⟨4011137836282470262504463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42785470253679682800047605 4011137836282470262504463)
              ·
                refine ⟨6016706754423705393756695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011137836282470262504463 6016706754423705393756695)
                ·
                  refine ⟨9025060131635558090635043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016706754423705393756695 9025060131635558090635043)
                  ·
                    refine ⟨13537590197453337135952565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9025060131635558090635043 13537590197453337135952565)
                    ·
                      refine ⟨1269149081011250356495553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13537590197453337135952565 1269149081011250356495553)
                      ·
                        rfl

theorem cell23_2471659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].length) (baseStart_2471659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471659 prefixEnd_2471659 := by exact prefixLift 2471659
  have htrace : WordTrace (prefixWord ++ tailWord_2471659) baseStart_2471659 baseEnd_2471659 := by
    simpa [prefixWord, tailWord_2471659, baseEnd_2471659] using wordTrace_append hprefix tailTrace_2471659
  have hstable : (prefixWord ++ tailWord_2471659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471659).length < 2 ^ (prefixWord ++ tailWord_2471659).sum := by decide
  have hdescent : baseEnd_2471659 < baseStart_2471659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2471672 : Nat := 118140960795 + 2471672 * 2 ^ 59
def prefixEnd_2471672 : Nat := 4983230072969 + 3 ^ 40 * 2471672 * 2
def baseEnd_2471672 : Nat := 1269155756259758805632993

theorem tailTrace_2471672 : CollatzResearch.WordTrace tailWord_2471672 prefixEnd_2471672 1269155756259758805632993 := by
  unfold tailWord_2471672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45074641950780973407692635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60099522601041297876923513 45074641950780973407692635)
  ·
    refine ⟨67611962926171460111538953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45074641950780973407692635 67611962926171460111538953)
    ·
      refine ⟨50708972194628595083654215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67611962926171460111538953 50708972194628595083654215)
      ·
        refine ⟨76063458291942892625481323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50708972194628595083654215 76063458291942892625481323)
        ·
          refine ⟨114095187437914338938221985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76063458291942892625481323 114095187437914338938221985)
          ·
            refine ⟨85571390578435754203666489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114095187437914338938221985 85571390578435754203666489)
            ·
              refine ⟨64178542933826815652749867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85571390578435754203666489 64178542933826815652749867)
              ·
                refine ⟨96267814400740223479124801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64178542933826815652749867 96267814400740223479124801)
                ·
                  refine ⟨72200860800555167609343601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96267814400740223479124801 72200860800555167609343601)
                  ·
                    refine ⟨54150645600416375707007701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72200860800555167609343601 54150645600416375707007701)
                    ·
                      refine ⟨1269155756259758805632993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54150645600416375707007701 1269155756259758805632993)
                      ·
                        rfl

theorem cell23_2471672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2471672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471672 prefixEnd_2471672 := by exact prefixLift 2471672
  have htrace : WordTrace (prefixWord ++ tailWord_2471672) baseStart_2471672 baseEnd_2471672 := by
    simpa [prefixWord, tailWord_2471672, baseEnd_2471672] using wordTrace_append hprefix tailTrace_2471672
  have hstable : (prefixWord ++ tailWord_2471672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471672).length < 2 ^ (prefixWord ++ tailWord_2471672).sum := by decide
  have hdescent : baseEnd_2471672 < baseStart_2471672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471706 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2471706 : Nat := 118140960795 + 2471706 * 2 ^ 59
def prefixEnd_2471706 : Nat := 4983230072969 + 3 ^ 40 * 2471706 * 2
def baseEnd_2471706 : Nat := 1269173214602011672607837

theorem tailTrace_2471706 : CollatzResearch.WordTrace tailWord_2471706 prefixEnd_2471706 1269173214602011672607837 := by
  unfold tailWord_2471706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537630995859692655530743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60100349322292513748081981 22537630995859692655530743)
  ·
    refine ⟨33806446493789538983296115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22537630995859692655530743 33806446493789538983296115)
    ·
      refine ⟨50709669740684308474944173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33806446493789538983296115 50709669740684308474944173)
      ·
        refine ⟨19016126152756615678104065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50709669740684308474944173 19016126152756615678104065)
        ·
          refine ⟨14262094614567461758578049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19016126152756615678104065 14262094614567461758578049)
          ·
            refine ⟨10696570960925596318933537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14262094614567461758578049 10696570960925596318933537)
            ·
              refine ⟨8022428220694197239200153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696570960925596318933537 8022428220694197239200153)
              ·
                refine ⟨6016821165520647929400115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8022428220694197239200153 6016821165520647929400115)
                ·
                  refine ⟨9025231748280971894100173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016821165520647929400115 9025231748280971894100173)
                  ·
                    refine ⟨3384461905605364460287565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9025231748280971894100173 3384461905605364460287565)
                    ·
                      refine ⟨1269173214602011672607837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3384461905605364460287565 1269173214602011672607837)
                      ·
                        rfl

theorem cell23_2471706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2471706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471706 prefixEnd_2471706 := by exact prefixLift 2471706
  have htrace : WordTrace (prefixWord ++ tailWord_2471706) baseStart_2471706 baseEnd_2471706 := by
    simpa [prefixWord, tailWord_2471706, baseEnd_2471706] using wordTrace_append hprefix tailTrace_2471706
  have hstable : (prefixWord ++ tailWord_2471706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471706).length < 2 ^ (prefixWord ++ tailWord_2471706).sum := by decide
  have hdescent : baseEnd_2471706 < baseStart_2471706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471749 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_2471749 : Nat := 118140960795 + 2471749 * 2 ^ 59
def prefixEnd_2471749 : Nat := 4983230072969 + 3 ^ 40 * 2471749 * 2
def baseEnd_2471749 : Nat := 1269195294270155004370139

theorem tailTrace_2471749 : CollatzResearch.WordTrace tailWord_2471749 prefixEnd_2471749 1269195294270155004370139 := by
  unfold tailWord_2471749
  simp only [CollatzResearch.WordTrace]
  refine ⟨90152092322282988965938301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60101394881521992643958867 90152092322282988965938301)
  ·
    refine ⟨33807034620856120862226863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90152092322282988965938301 33807034620856120862226863)
    ·
      refine ⟨50710551931284181293340295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33807034620856120862226863 50710551931284181293340295)
      ·
        refine ⟨76065827896926271940010443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50710551931284181293340295 76065827896926271940010443)
        ·
          refine ⟨114098741845389407910015665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76065827896926271940010443 114098741845389407910015665)
          ·
            refine ⟨85574056384042055932511749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114098741845389407910015665 85574056384042055932511749)
            ·
              refine ⟨16045135572007885487345953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85574056384042055932511749 16045135572007885487345953)
              ·
                refine ⟨12033851679005914115509465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16045135572007885487345953 12033851679005914115509465)
                ·
                  refine ⟨9025388759254435586632099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033851679005914115509465 9025388759254435586632099)
                  ·
                    refine ⟨13538083138881653379948149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9025388759254435586632099 13538083138881653379948149)
                    ·
                      refine ⟨1269195294270155004370139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13538083138881653379948149 1269195294270155004370139)
                      ·
                        rfl

theorem cell23_2471749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_2471749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471749 prefixEnd_2471749 := by exact prefixLift 2471749
  have htrace : WordTrace (prefixWord ++ tailWord_2471749) baseStart_2471749 baseEnd_2471749 := by
    simpa [prefixWord, tailWord_2471749, baseEnd_2471749] using wordTrace_append hprefix tailTrace_2471749
  have hstable : (prefixWord ++ tailWord_2471749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471749).length < 2 ^ (prefixWord ++ tailWord_2471749).sum := by decide
  have hdescent : baseEnd_2471749 < baseStart_2471749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471849 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_2471849 : Nat := 118140960795 + 2471849 * 2 ^ 59
def prefixEnd_2471849 : Nat := 4983230072969 + 3 ^ 40 * 2471849 * 2
def baseEnd_2471849 : Nat := 1269246642335604613119679

theorem tailTrace_2471849 : CollatzResearch.WordTrace tailWord_2471849 prefixEnd_2471849 1269246642335604613119679 := by
  unfold tailWord_2471849
  simp only [CollatzResearch.WordTrace]
  refine ⟨90155739621920706044578601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60103826414613804029719067 90155739621920706044578601)
  ·
    refine ⟨67616804716440529533433951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90155739621920706044578601 67616804716440529533433951)
    ·
      refine ⟨101425207074660794300150927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67616804716440529533433951 101425207074660794300150927)
      ·
        refine ⟨152137810611991191450226391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101425207074660794300150927 152137810611991191450226391)
        ·
          refine ⟨228206715917986787175339587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152137810611991191450226391 228206715917986787175339587)
          ·
            refine ⟨342310073876980180763009381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228206715917986787175339587 342310073876980180763009381)
            ·
              refine ⟨64183138851933783893064259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342310073876980180763009381 64183138851933783893064259)
              ·
                refine ⟨96274708277900675839596389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64183138851933783893064259 96274708277900675839596389)
                ·
                  refine ⟨18051507802106376719924323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96274708277900675839596389 18051507802106376719924323)
                  ·
                    refine ⟨27077261703159565079886485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18051507802106376719924323 27077261703159565079886485)
                    ·
                      refine ⟨1269246642335604613119679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27077261703159565079886485 1269246642335604613119679)
                      ·
                        rfl

theorem cell23_2471849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_2471849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471849 prefixEnd_2471849 := by exact prefixLift 2471849
  have htrace : WordTrace (prefixWord ++ tailWord_2471849) baseStart_2471849 baseEnd_2471849 := by
    simpa [prefixWord, tailWord_2471849, baseEnd_2471849] using wordTrace_append hprefix tailTrace_2471849
  have hstable : (prefixWord ++ tailWord_2471849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471849).length < 2 ^ (prefixWord ++ tailWord_2471849).sum := by decide
  have hdescent : baseEnd_2471849 < baseStart_2471849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471870 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2471870 : Nat := 118140960795 + 2471870 * 2 ^ 59
def prefixEnd_2471870 : Nat := 4983230072969 + 3 ^ 40 * 2471870 * 2
def baseEnd_2471870 : Nat := 1269257425429349030957083

theorem tailTrace_2471870 : CollatzResearch.WordTrace tailWord_2471870 prefixEnd_2471870 1269257425429349030957083 := by
  unfold tailWord_2471870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269563194355578328886633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60104337036563084420728709 11269563194355578328886633)
  ·
    refine ⟨8452172395766683746664975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11269563194355578328886633 8452172395766683746664975)
    ·
      refine ⟨12678258593650025619997463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452172395766683746664975 12678258593650025619997463)
      ·
        refine ⟨19017387890475038429996195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678258593650025619997463 19017387890475038429996195)
        ·
          refine ⟨28526081835712557644994293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19017387890475038429996195 28526081835712557644994293)
          ·
            refine ⟨2674320172098052279218215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28526081835712557644994293 2674320172098052279218215)
            ·
              refine ⟨4011480258147078418827323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674320172098052279218215 4011480258147078418827323)
              ·
                refine ⟨6017220387220617628240985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011480258147078418827323 6017220387220617628240985)
                ·
                  refine ⟨4512915290415463221180739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017220387220617628240985 4512915290415463221180739)
                  ·
                    refine ⟨6769372935623194831771109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4512915290415463221180739 6769372935623194831771109)
                    ·
                      refine ⟨1269257425429349030957083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6769372935623194831771109 1269257425429349030957083)
                      ·
                        rfl

theorem cell23_2471870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2471870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471870 prefixEnd_2471870 := by exact prefixLift 2471870
  have htrace : WordTrace (prefixWord ++ tailWord_2471870) baseStart_2471870 baseEnd_2471870 := by
    simpa [prefixWord, tailWord_2471870, baseEnd_2471870] using wordTrace_append hprefix tailTrace_2471870
  have hstable : (prefixWord ++ tailWord_2471870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471870).length < 2 ^ (prefixWord ++ tailWord_2471870).sum := by decide
  have hdescent : baseEnd_2471870 < baseStart_2471870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471880 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 1, 4]
def baseStart_2471880 : Nat := 118140960795 + 2471880 * 2 ^ 59
def prefixEnd_2471880 : Nat := 4983230072969 + 3 ^ 40 * 2471880 * 2
def baseEnd_2471880 : Nat := 423087520078631330610679

theorem tailTrace_2471880 : CollatzResearch.WordTrace tailWord_2471880 prefixEnd_2471880 423087520078631330610679 := by
  unfold tailWord_2471880
  simp only [CollatzResearch.WordTrace]
  refine ⟨45078435142404199169478547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60104580189872265559304729 45078435142404199169478547)
  ·
    refine ⟨67617652713606298754217821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45078435142404199169478547 67617652713606298754217821)
    ·
      refine ⟨25356619767602362032831683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67617652713606298754217821 25356619767602362032831683)
      ·
        refine ⟨38034929651403543049247525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25356619767602362032831683 38034929651403543049247525)
        ·
          refine ⟨7131549309638164321733911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38034929651403543049247525 7131549309638164321733911)
          ·
            refine ⟨10697323964457246482600867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131549309638164321733911 10697323964457246482600867)
            ·
              refine ⟨16045985946685869723901301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10697323964457246482600867 16045985946685869723901301)
              ·
                refine ⟨1504311182501800286615747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16045985946685869723901301 1504311182501800286615747)
                ·
                  refine ⟨2256466773752700429923621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504311182501800286615747 2256466773752700429923621)
                  ·
                    refine ⟨423087520078631330610679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256466773752700429923621 423087520078631330610679)
                    ·
                      rfl

theorem cell23_2471880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_2471880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471880 prefixEnd_2471880 := by exact prefixLift 2471880
  have htrace : WordTrace (prefixWord ++ tailWord_2471880) baseStart_2471880 baseEnd_2471880 := by
    simpa [prefixWord, tailWord_2471880, baseEnd_2471880] using wordTrace_append hprefix tailTrace_2471880
  have hstable : (prefixWord ++ tailWord_2471880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471880).length < 2 ^ (prefixWord ++ tailWord_2471880).sum := by decide
  have hdescent : baseEnd_2471880 < baseStart_2471880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471893 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 6]
def baseStart_2471893 : Nat := 118140960795 + 2471893 * 2 ^ 59
def prefixEnd_2471893 : Nat := 4983230072969 + 3 ^ 40 * 2471893 * 2
def baseEnd_2471893 : Nat := 141029915053822493441053

theorem tailTrace_2471893 : CollatzResearch.WordTrace tailWord_2471893 prefixEnd_2471893 141029915053822493441053 := by
  unfold tailWord_2471893
  simp only [CollatzResearch.WordTrace]
  refine ⟨90157344433761301559180333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60104896289174201039453555 90157344433761301559180333)
  ·
    refine ⟨33809004162660488084692625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90157344433761301559180333 33809004162660488084692625)
    ·
      refine ⟨25356753121995366063519469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33809004162660488084692625 25356753121995366063519469)
      ·
        refine ⟨9508782420748262273819801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25356753121995366063519469 9508782420748262273819801)
        ·
          refine ⟨7131586815561196705364851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9508782420748262273819801 7131586815561196705364851)
          ·
            refine ⟨10697380223341795058047277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131586815561196705364851 10697380223341795058047277)
            ·
              refine ⟨4011517583753173146767729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10697380223341795058047277 4011517583753173146767729)
              ·
                refine ⟨3008638187814879860075797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011517583753173146767729 3008638187814879860075797)
                ·
                  refine ⟨141029915053822493441053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3008638187814879860075797 141029915053822493441053)
                  ·
                    rfl

theorem cell23_2471893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_2471893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471893 prefixEnd_2471893 := by exact prefixLift 2471893
  have htrace : WordTrace (prefixWord ++ tailWord_2471893) baseStart_2471893 baseEnd_2471893 := by
    simpa [prefixWord, tailWord_2471893, baseEnd_2471893] using wordTrace_append hprefix tailTrace_2471893
  have hstable : (prefixWord ++ tailWord_2471893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471893).length < 2 ^ (prefixWord ++ tailWord_2471893).sum := by decide
  have hdescent : baseEnd_2471893 < baseStart_2471893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471970 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2471970 : Nat := 118140960795 + 2471970 * 2 ^ 59
def prefixEnd_2471970 : Nat := 4983230072969 + 3 ^ 40 * 2471970 * 2
def baseEnd_2471970 : Nat := 423102924498266213235541

theorem tailTrace_2471970 : CollatzResearch.WordTrace tailWord_2471970 prefixEnd_2471970 423102924498266213235541 := by
  unfold tailWord_2471970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540038213620585927433341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60106768569654895806488909 22540038213620585927433341)
  ·
    refine ⟨8452514330107719722787503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22540038213620585927433341 8452514330107719722787503)
    ·
      refine ⟨12678771495161579584181255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452514330107719722787503 12678771495161579584181255)
      ·
        refine ⟨19018157242742369376271883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678771495161579584181255 19018157242742369376271883)
        ·
          refine ⟨28527235864113554064407825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19018157242742369376271883 28527235864113554064407825)
          ·
            refine ⟨21395426898085165548305869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28527235864113554064407825 21395426898085165548305869)
            ·
              refine ⟨8023285086781937080614701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21395426898085165548305869 8023285086781937080614701)
              ·
                refine ⟨3008731907543226405230513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8023285086781937080614701 3008731907543226405230513)
                ·
                  refine ⟨2256548930657419803922885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3008731907543226405230513 2256548930657419803922885)
                  ·
                    refine ⟨423102924498266213235541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256548930657419803922885 423102924498266213235541)
                    ·
                      rfl

theorem cell23_2471970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2471970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471970 prefixEnd_2471970 := by exact prefixLift 2471970
  have htrace : WordTrace (prefixWord ++ tailWord_2471970) baseStart_2471970 baseEnd_2471970 := by
    simpa [prefixWord, tailWord_2471970, baseEnd_2471970] using wordTrace_append hprefix tailTrace_2471970
  have hstable : (prefixWord ++ tailWord_2471970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471970).length < 2 ^ (prefixWord ++ tailWord_2471970).sum := by decide
  have hdescent : baseEnd_2471970 < baseStart_2471970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471990 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2471990 : Nat := 118140960795 + 2471990 * 2 ^ 59
def prefixEnd_2471990 : Nat := 4983230072969 + 3 ^ 40 * 2471990 * 2
def baseEnd_2471990 : Nat := 1269319043107888561456531

theorem tailTrace_2471990 : CollatzResearch.WordTrace tailWord_2471990 prefixEnd_2471990 1269319043107888561456531 := by
  unfold tailWord_2471990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635055144650617945341339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60107254876273258083640949 5635055144650617945341339)
  ·
    refine ⟨8452582716975926918012009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635055144650617945341339 8452582716975926918012009)
    ·
      refine ⟨6339437037731945188509007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8452582716975926918012009 6339437037731945188509007)
      ·
        refine ⟨9509155556597917782763511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339437037731945188509007 9509155556597917782763511)
        ·
          refine ⟨14263733334896876674145267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509155556597917782763511 14263733334896876674145267)
          ·
            refine ⟨21395600002345315011217901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263733334896876674145267 21395600002345315011217901)
            ·
              refine ⟨8023350000879493129206713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21395600002345315011217901 8023350000879493129206713)
              ·
                refine ⟨6017512500659619846905035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023350000879493129206713 6017512500659619846905035)
                ·
                  refine ⟨9026268750989429770357553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017512500659619846905035 9026268750989429770357553)
                  ·
                    refine ⟨6769701563242072327768165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9026268750989429770357553 6769701563242072327768165)
                    ·
                      refine ⟨1269319043107888561456531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6769701563242072327768165 1269319043107888561456531)
                      ·
                        rfl

theorem cell23_2471990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2471990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471990 prefixEnd_2471990 := by exact prefixLift 2471990
  have htrace : WordTrace (prefixWord ++ tailWord_2471990) baseStart_2471990 baseEnd_2471990 := by
    simpa [prefixWord, tailWord_2471990, baseEnd_2471990] using wordTrace_append hprefix tailTrace_2471990
  have hstable : (prefixWord ++ tailWord_2471990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471990).length < 2 ^ (prefixWord ++ tailWord_2471990).sum := by decide
  have hdescent : baseEnd_2471990 < baseStart_2471990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471997 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2471997 : Nat := 118140960795 + 2471997 * 2 ^ 59
def prefixEnd_2471997 : Nat := 4983230072969 + 3 ^ 40 * 2471997 * 2
def baseEnd_2471997 : Nat := 1269322637472470034068999

theorem tailTrace_2471997 : CollatzResearch.WordTrace tailWord_2471997 prefixEnd_2471997 1269322637472470034068999 := by
  unfold tailWord_2471997
  simp only [CollatzResearch.WordTrace]
  refine ⟨90161137625384527320966245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60107425083589684880644163 90161137625384527320966245)
  ·
    refine ⟨16905213304759598872681171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90161137625384527320966245 16905213304759598872681171)
    ·
      refine ⟨25357819957139398309021757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905213304759598872681171 25357819957139398309021757)
      ·
        refine ⟨9509182483927274365883159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25357819957139398309021757 9509182483927274365883159)
        ·
          refine ⟨14263773725890911548824739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509182483927274365883159 14263773725890911548824739)
          ·
            refine ⟨21395660588836367323237109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263773725890911548824739 21395660588836367323237109)
            ·
              refine ⟨2005843180203409436553479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21395660588836367323237109 2005843180203409436553479)
              ·
                refine ⟨3008764770305114154830219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005843180203409436553479 3008764770305114154830219)
                ·
                  refine ⟨4513147155457671232245329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008764770305114154830219 4513147155457671232245329)
                  ·
                    refine ⟨3384860366593253424183997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4513147155457671232245329 3384860366593253424183997)
                    ·
                      refine ⟨1269322637472470034068999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3384860366593253424183997 1269322637472470034068999)
                      ·
                        rfl

theorem cell23_2471997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2471997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2471997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2471997 prefixEnd_2471997 := by exact prefixLift 2471997
  have htrace : WordTrace (prefixWord ++ tailWord_2471997) baseStart_2471997 baseEnd_2471997 := by
    simpa [prefixWord, tailWord_2471997, baseEnd_2471997] using wordTrace_append hprefix tailTrace_2471997
  have hstable : (prefixWord ++ tailWord_2471997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471997).length < 2 ^ (prefixWord ++ tailWord_2471997).sum := by decide
  have hdescent : baseEnd_2471997 < baseStart_2471997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472013 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2472013 : Nat := 118140960795 + 2472013 * 2 ^ 59
def prefixEnd_2472013 : Nat := 4983230072969 + 3 ^ 40 * 2472013 * 2
def baseEnd_2472013 : Nat := 423110284387647323822975

theorem tailTrace_2472013 : CollatzResearch.WordTrace tailWord_2472013 prefixEnd_2472013 423110284387647323822975 := by
  unfold tailWord_2472013
  simp only [CollatzResearch.WordTrace]
  refine ⟨90161721193326562053548693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60107814128884374702365795 90161721193326562053548693)
  ·
    refine ⟨4226330680937182596260095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90161721193326562053548693 4226330680937182596260095)
    ·
      refine ⟨6339496021405773894390143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226330680937182596260095 6339496021405773894390143)
      ·
        refine ⟨9509244032108660841585215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339496021405773894390143 9509244032108660841585215)
        ·
          refine ⟨14263866048162991262377823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509244032108660841585215 14263866048162991262377823)
          ·
            refine ⟨21395799072244486893566735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263866048162991262377823 21395799072244486893566735)
            ·
              refine ⟨32093698608366730340350103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21395799072244486893566735 32093698608366730340350103)
              ·
                refine ⟨48140547912550095510525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32093698608366730340350103 48140547912550095510525155)
                ·
                  refine ⟨72210821868825143265787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48140547912550095510525155 72210821868825143265787733)
                  ·
                    refine ⟨423110284387647323822975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72210821868825143265787733 423110284387647323822975)
                    ·
                      rfl

theorem cell23_2472013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2472013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472013 prefixEnd_2472013 := by exact prefixLift 2472013
  have htrace : WordTrace (prefixWord ++ tailWord_2472013) baseStart_2472013 baseEnd_2472013 := by
    simpa [prefixWord, tailWord_2472013, baseEnd_2472013] using wordTrace_append hprefix tailTrace_2472013
  have hstable : (prefixWord ++ tailWord_2472013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472013).length < 2 ^ (prefixWord ++ tailWord_2472013).sum := by decide
  have hdescent : baseEnd_2472013 < baseStart_2472013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472054 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2472054 : Nat := 118140960795 + 2472054 * 2 ^ 59
def prefixEnd_2472054 : Nat := 4983230072969 + 3 ^ 40 * 2472054 * 2
def baseEnd_2472054 : Nat := 1269351905869776311056237

theorem tailTrace_2472054 : CollatzResearch.WordTrace tailWord_2472054 prefixEnd_2472054 1269351905869776311056237 := by
  unfold tailWord_2472054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635201036636126628486951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60108811057452017370527477 5635201036636126628486951)
  ·
    refine ⟨8452801554954189942730427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635201036636126628486951 8452801554954189942730427)
    ·
      refine ⟨12679202332431284914095641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452801554954189942730427 12679202332431284914095641)
      ·
        refine ⟨9509401749323463685571731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12679202332431284914095641 9509401749323463685571731)
        ·
          refine ⟨14264102623985195528357597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509401749323463685571731 14264102623985195528357597)
          ·
            refine ⟨5349038483994448323134099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14264102623985195528357597 5349038483994448323134099)
            ·
              refine ⟨8023557725991672484701149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349038483994448323134099 8023557725991672484701149)
              ·
                refine ⟨3008834147246877181762931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8023557725991672484701149 3008834147246877181762931)
                ·
                  refine ⟨4513251220870315772644397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008834147246877181762931 4513251220870315772644397)
                  ·
                    refine ⟨1692469207826368414741649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4513251220870315772644397 1692469207826368414741649)
                    ·
                      refine ⟨1269351905869776311056237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692469207826368414741649 1269351905869776311056237)
                      ·
                        rfl

theorem cell23_2472054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2472054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472054 prefixEnd_2472054 := by exact prefixLift 2472054
  have htrace : WordTrace (prefixWord ++ tailWord_2472054) baseStart_2472054 baseEnd_2472054 := by
    simpa [prefixWord, tailWord_2472054, baseEnd_2472054] using wordTrace_append hprefix tailTrace_2472054
  have hstable : (prefixWord ++ tailWord_2472054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472054).length < 2 ^ (prefixWord ++ tailWord_2472054).sum := by decide
  have hdescent : baseEnd_2472054 < baseStart_2472054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472056 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 11]
def baseStart_2472056 : Nat := 118140960795 + 2472056 * 2 ^ 59
def prefixEnd_2472056 : Nat := 4983230072969 + 3 ^ 40 * 2472056 * 2
def baseEnd_2472056 : Nat := 141039214759009478136803

theorem tailTrace_2472056 : CollatzResearch.WordTrace tailWord_2472056 prefixEnd_2472056 141039214759009478136803 := by
  unfold tailWord_2472056
  simp only [CollatzResearch.WordTrace]
  refine ⟨45081644766085390198682011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60108859688113853598242681 45081644766085390198682011)
  ·
    refine ⟨67622467149128085298023017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45081644766085390198682011 67622467149128085298023017)
    ·
      refine ⟨50716850361846063973517263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67622467149128085298023017 50716850361846063973517263)
      ·
        refine ⟨76075275542769095960275895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50716850361846063973517263 76075275542769095960275895)
        ·
          refine ⟨114112913314153643940413843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76075275542769095960275895 114112913314153643940413843)
          ·
            refine ⟨171169369971230465910620765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114112913314153643940413843 171169369971230465910620765)
            ·
              refine ⟨64188513739211424716482787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171169369971230465910620765 64188513739211424716482787)
              ·
                refine ⟨96282770608817137074724181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64188513739211424716482787 96282770608817137074724181)
                ·
                  refine ⟨141039214759009478136803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 96282770608817137074724181 141039214759009478136803)
                  ·
                    rfl

theorem cell23_2472056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_2472056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472056 prefixEnd_2472056 := by exact prefixLift 2472056
  have htrace : WordTrace (prefixWord ++ tailWord_2472056) baseStart_2472056 baseEnd_2472056 := by
    simpa [prefixWord, tailWord_2472056, baseEnd_2472056] using wordTrace_append hprefix tailTrace_2472056
  have hstable : (prefixWord ++ tailWord_2472056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472056).length < 2 ^ (prefixWord ++ tailWord_2472056).sum := by decide
  have hdescent : baseEnd_2472056 < baseStart_2472056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472067 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 4, 2, 2]
def baseStart_2472067 : Nat := 118140960795 + 2472067 * 2 ^ 59
def prefixEnd_2472067 : Nat := 4983230072969 + 3 ^ 40 * 2472067 * 2
def baseEnd_2472067 : Nat := 1269358581118284760193677

theorem tailTrace_2472067 : CollatzResearch.WordTrace tailWord_2472067 prefixEnd_2472067 1269358581118284760193677 := by
  unfold tailWord_2472067
  simp only [CollatzResearch.WordTrace]
  refine ⟨90163690735130929276014455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60109127156753952850676303 90163690735130929276014455)
  ·
    refine ⟨135245536102696393914021683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90163690735130929276014455 135245536102696393914021683)
    ·
      refine ⟨202868304154044590871032525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135245536102696393914021683 202868304154044590871032525)
      ·
        refine ⟨76075614057766721576637197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202868304154044590871032525 76075614057766721576637197)
        ·
          refine ⟨28528355271662520591238949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76075614057766721576637197 28528355271662520591238949)
          ·
            refine ⟨5349066613436722610857303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28528355271662520591238949 5349066613436722610857303)
            ·
              refine ⟨8023599920155083916285955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349066613436722610857303 8023599920155083916285955)
              ·
                refine ⟨12035399880232625874428933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023599920155083916285955 12035399880232625874428933)
                ·
                  refine ⟨2256637477543617351455425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12035399880232625874428933 2256637477543617351455425)
                  ·
                    refine ⟨1692478108157713013591569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256637477543617351455425 1692478108157713013591569)
                    ·
                      refine ⟨1269358581118284760193677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692478108157713013591569 1269358581118284760193677)
                      ·
                        rfl

theorem cell23_2472067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_2472067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472067 prefixEnd_2472067 := by exact prefixLift 2472067
  have htrace : WordTrace (prefixWord ++ tailWord_2472067) baseStart_2472067 baseEnd_2472067 := by
    simpa [prefixWord, tailWord_2472067, baseEnd_2472067] using wordTrace_append hprefix tailTrace_2472067
  have hstable : (prefixWord ++ tailWord_2472067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472067).length < 2 ^ (prefixWord ++ tailWord_2472067).sum := by decide
  have hdescent : baseEnd_2472067 < baseStart_2472067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472073 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 7]
def baseStart_2472073 : Nat := 118140960795 + 2472073 * 2 ^ 59
def prefixEnd_2472073 : Nat := 4983230072969 + 3 ^ 40 * 2472073 * 2
def baseEnd_2472073 : Nat := 141040184666912415190961

theorem tailTrace_2472073 : CollatzResearch.WordTrace tailWord_2472073 prefixEnd_2472073 141040184666912415190961 := by
  unfold tailWord_2472073
  simp only [CollatzResearch.WordTrace]
  refine ⟨90163909573109192300732873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60109273048739461533821915 90163909573109192300732873)
  ·
    refine ⟨67622932179831894225549655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90163909573109192300732873 67622932179831894225549655)
    ·
      refine ⟨101434398269747841338324483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67622932179831894225549655 101434398269747841338324483)
      ·
        refine ⟨152151597404621762007486725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101434398269747841338324483 152151597404621762007486725)
        ·
          refine ⟨28528424513366580376403761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152151597404621762007486725 28528424513366580376403761)
          ·
            refine ⟨21396318385024935282302821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28528424513366580376403761 21396318385024935282302821)
            ·
              refine ⟨4011809697192175365431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21396318385024935282302821 4011809697192175365431779)
              ·
                refine ⟨6017714545788263048147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011809697192175365431779 6017714545788263048147669)
                ·
                  refine ⟨141040184666912415190961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6017714545788263048147669 141040184666912415190961)
                  ·
                    rfl

theorem cell23_2472073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_2472073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472073 prefixEnd_2472073 := by exact prefixLift 2472073
  have htrace : WordTrace (prefixWord ++ tailWord_2472073) baseStart_2472073 baseEnd_2472073 := by
    simpa [prefixWord, tailWord_2472073, baseEnd_2472073] using wordTrace_append hprefix tailTrace_2472073
  have hstable : (prefixWord ++ tailWord_2472073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472073).length < 2 ^ (prefixWord ++ tailWord_2472073).sum := by decide
  have hdescent : baseEnd_2472073 < baseStart_2472073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472124 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 5]
def baseStart_2472124 : Nat := 118140960795 + 2472124 * 2 ^ 59
def prefixEnd_2472124 : Nat := 4983230072969 + 3 ^ 40 * 2472124 * 2
def baseEnd_2472124 : Nat := 141043094390621226353435

theorem tailTrace_2472124 : CollatzResearch.WordTrace tailWord_2472124 prefixEnd_2472124 141043094390621226353435 := by
  unfold tailWord_2472124
  simp only [CollatzResearch.WordTrace]
  refine ⟨45082884847962214005419713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60110513130616285340559617 45082884847962214005419713)
  ·
    refine ⟨33812163635971660504064785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45082884847962214005419713 33812163635971660504064785)
    ·
      refine ⟨25359122726978745378048589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33812163635971660504064785 25359122726978745378048589)
      ·
        refine ⟨9509671022617029516768221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25359122726978745378048589 9509671022617029516768221)
        ·
          refine ⟨3566126633481386068788083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9509671022617029516768221 3566126633481386068788083)
          ·
            refine ⟨5349189950222079103182125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566126633481386068788083 5349189950222079103182125)
            ·
              refine ⟨2005946231333279663693297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5349189950222079103182125 2005946231333279663693297)
              ·
                refine ⟨1504459673499959747769973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005946231333279663693297 1504459673499959747769973)
                ·
                  refine ⟨141043094390621226353435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1504459673499959747769973 141043094390621226353435)
                  ·
                    rfl

theorem cell23_2472124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_2472124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472124 prefixEnd_2472124 := by exact prefixLift 2472124
  have htrace : WordTrace (prefixWord ++ tailWord_2472124) baseStart_2472124 baseEnd_2472124 := by
    simpa [prefixWord, tailWord_2472124, baseEnd_2472124] using wordTrace_append hprefix tailTrace_2472124
  have hstable : (prefixWord ++ tailWord_2472124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472124).length < 2 ^ (prefixWord ++ tailWord_2472124).sum := by decide
  have hdescent : baseEnd_2472124 < baseStart_2472124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472153 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2472153 : Nat := 118140960795 + 2472153 * 2 ^ 59
def prefixEnd_2472153 : Nat := 4983230072969 + 3 ^ 40 * 2472153 * 2
def baseEnd_2472153 : Nat := 1269402740454571423718281

theorem tailTrace_2472153 : CollatzResearch.WordTrace tailWord_2472153 prefixEnd_2472153 1269402740454571423718281 := by
  unfold tailWord_2472153
  simp only [CollatzResearch.WordTrace]
  refine ⟨90166827412819365963645113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60111218275212910642430075 90166827412819365963645113)
  ·
    refine ⟨67625120559614524472733835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90166827412819365963645113 67625120559614524472733835)
    ·
      refine ⟨101437680839421786709100753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67625120559614524472733835 101437680839421786709100753)
      ·
        refine ⟨76078260629566340031825565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101437680839421786709100753 76078260629566340031825565)
        ·
          refine ⟨28529347736087377511934587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76078260629566340031825565 28529347736087377511934587)
          ·
            refine ⟨42794021604131066267901881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28529347736087377511934587 42794021604131066267901881)
            ·
              refine ⟨32095516203098299700926411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42794021604131066267901881 32095516203098299700926411)
              ·
                refine ⟨48143274304647449551389617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32095516203098299700926411 48143274304647449551389617)
                ·
                  refine ⟨36107455728485587163542213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48143274304647449551389617 36107455728485587163542213)
                  ·
                    refine ⟨6770147949091047593164165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36107455728485587163542213 6770147949091047593164165)
                    ·
                      refine ⟨1269402740454571423718281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6770147949091047593164165 1269402740454571423718281)
                      ·
                        rfl

theorem cell23_2472153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2472153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472153 prefixEnd_2472153 := by exact prefixLift 2472153
  have htrace : WordTrace (prefixWord ++ tailWord_2472153) baseStart_2472153 baseEnd_2472153 := by
    simpa [prefixWord, tailWord_2472153, baseEnd_2472153] using wordTrace_append hprefix tailTrace_2472153
  have hstable : (prefixWord ++ tailWord_2472153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472153).length < 2 ^ (prefixWord ++ tailWord_2472153).sum := by decide
  have hdescent : baseEnd_2472153 < baseStart_2472153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472157 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2472157 : Nat := 118140960795 + 2472157 * 2 ^ 59
def prefixEnd_2472157 : Nat := 4983230072969 + 3 ^ 40 * 2472157 * 2
def baseEnd_2472157 : Nat := 1269404794377189408068263

theorem tailTrace_2472157 : CollatzResearch.WordTrace tailWord_2472157 prefixEnd_2472157 1269404794377189408068263 := by
  unfold tailWord_2472157
  simp only [CollatzResearch.WordTrace]
  refine ⟨90166973304804874646790725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60111315536536583097860483 90166973304804874646790725)
  ·
    refine ⟨16906307494650913996273261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90166973304804874646790725 16906307494650913996273261)
    ·
      refine ⟨6339865310494092748602473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16906307494650913996273261 6339865310494092748602473)
      ·
        refine ⟨4754898982870569561451855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6339865310494092748602473 4754898982870569561451855)
        ·
          refine ⟨7132348474305854342177783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754898982870569561451855 7132348474305854342177783)
          ·
            refine ⟨10698522711458781513266675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7132348474305854342177783 10698522711458781513266675)
            ·
              refine ⟨16047784067188172269900013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698522711458781513266675 16047784067188172269900013)
              ·
                refine ⟨6017919025195564601212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16047784067188172269900013 6017919025195564601212505)
                ·
                  refine ⟨4513439268896673450909379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017919025195564601212505 4513439268896673450909379)
                  ·
                    refine ⟨6770158903345010176364069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4513439268896673450909379 6770158903345010176364069)
                    ·
                      refine ⟨1269404794377189408068263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6770158903345010176364069 1269404794377189408068263)
                      ·
                        rfl

theorem cell23_2472157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2472157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472157 prefixEnd_2472157 := by exact prefixLift 2472157
  have htrace : WordTrace (prefixWord ++ tailWord_2472157) baseStart_2472157 baseEnd_2472157 := by
    simpa [prefixWord, tailWord_2472157, baseEnd_2472157] using wordTrace_append hprefix tailTrace_2472157
  have hstable : (prefixWord ++ tailWord_2472157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472157).length < 2 ^ (prefixWord ++ tailWord_2472157).sum := by decide
  have hdescent : baseEnd_2472157 < baseStart_2472157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472203 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_2472203 : Nat := 118140960795 + 2472203 * 2 ^ 59
def prefixEnd_2472203 : Nat := 4983230072969 + 3 ^ 40 * 2472203 * 2
def baseEnd_2472203 : Nat := 1269428414487296228093051

theorem tailTrace_2472203 : CollatzResearch.WordTrace tailWord_2472203 prefixEnd_2472203 1269428414487296228093051 := by
  unfold tailWord_2472203
  simp only [CollatzResearch.WordTrace]
  refine ⟨90168651062638224502965263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60112434041758816335310175 90168651062638224502965263)
  ·
    refine ⟨135252976593957336754447895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90168651062638224502965263 135252976593957336754447895)
    ·
      refine ⟨202879464890936005131671843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135252976593957336754447895 202879464890936005131671843)
      ·
        refine ⟨304319197336404007697507765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202879464890936005131671843 304319197336404007697507765)
        ·
          refine ⟨28529924750287875721641353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304319197336404007697507765 28529924750287875721641353)
          ·
            refine ⟨21397443562715906791231015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28529924750287875721641353 21397443562715906791231015)
            ·
              refine ⟨32096165344073860186846523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21397443562715906791231015 32096165344073860186846523)
              ·
                refine ⟨48144248016110790280269785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32096165344073860186846523 48144248016110790280269785)
                ·
                  refine ⟨36108186012083092710202339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48144248016110790280269785 36108186012083092710202339)
                  ·
                    refine ⟨54162279018124639065303509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36108186012083092710202339 54162279018124639065303509)
                    ·
                      refine ⟨1269428414487296228093051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54162279018124639065303509 1269428414487296228093051)
                      ·
                        rfl

theorem cell23_2472203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_2472203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472203 prefixEnd_2472203 := by exact prefixLift 2472203
  have htrace : WordTrace (prefixWord ++ tailWord_2472203) baseStart_2472203 baseEnd_2472203 := by
    simpa [prefixWord, tailWord_2472203, baseEnd_2472203] using wordTrace_append hprefix tailTrace_2472203
  have hstable : (prefixWord ++ tailWord_2472203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472203).length < 2 ^ (prefixWord ++ tailWord_2472203).sum := by decide
  have hdescent : baseEnd_2472203 < baseStart_2472203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472233 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_2472233 : Nat := 118140960795 + 2472233 * 2 ^ 59
def prefixEnd_2472233 : Nat := 4983230072969 + 3 ^ 40 * 2472233 * 2
def baseEnd_2472233 : Nat := 1269443818906931110717913

theorem tailTrace_2472233 : CollatzResearch.WordTrace tailWord_2472233 prefixEnd_2472233 1269443818906931110717913 := by
  unfold tailWord_2472233
  simp only [CollatzResearch.WordTrace]
  refine ⟨90169745252529539626557353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60113163501686359751038235 90169745252529539626557353)
  ·
    refine ⟨67627308939397154719918015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90169745252529539626557353 67627308939397154719918015)
    ·
      refine ⟨101440963409095732079877023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67627308939397154719918015 101440963409095732079877023)
      ·
        refine ⟨152161445113643598119815535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101440963409095732079877023 152161445113643598119815535)
        ·
          refine ⟨228242167670465397179723303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152161445113643598119815535 228242167670465397179723303)
          ·
            refine ⟨342363251505698095769584955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228242167670465397179723303 342363251505698095769584955)
            ·
              refine ⟨513544877258547143654377433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342363251505698095769584955 513544877258547143654377433)
              ·
                refine ⟨385158657943910357740783075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513544877258547143654377433 385158657943910357740783075)
                ·
                  refine ⟨577737986915865536611174613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385158657943910357740783075 577737986915865536611174613)
                  ·
                    refine ⟨13540734068340598514324405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 577737986915865536611174613 13540734068340598514324405)
                    ·
                      refine ⟨1269443818906931110717913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13540734068340598514324405 1269443818906931110717913)
                      ·
                        rfl

theorem cell23_2472233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_2472233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472233 prefixEnd_2472233 := by exact prefixLift 2472233
  have htrace : WordTrace (prefixWord ++ tailWord_2472233) baseStart_2472233 baseEnd_2472233 := by
    simpa [prefixWord, tailWord_2472233, baseEnd_2472233] using wordTrace_append hprefix tailTrace_2472233
  have hstable : (prefixWord ++ tailWord_2472233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472233).length < 2 ^ (prefixWord ++ tailWord_2472233).sum := by decide
  have hdescent : baseEnd_2472233 < baseStart_2472233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472250 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_2472250 : Nat := 118140960795 + 2472250 * 2 ^ 59
def prefixEnd_2472250 : Nat := 4983230072969 + 3 ^ 40 * 2472250 * 2
def baseEnd_2472250 : Nat := 1269452548078057544205335

theorem tailTrace_2472250 : CollatzResearch.WordTrace tailWord_2472250 prefixEnd_2472250 1269452548078057544205335 := by
  unfold tailWord_2472250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22542591323366987882481551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60113576862311967686617469 22542591323366987882481551)
  ·
    refine ⟨33813886985050481823722327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22542591323366987882481551 33813886985050481823722327)
    ·
      refine ⟨50720830477575722735583491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33813886985050481823722327 50720830477575722735583491)
      ·
        refine ⟨76081245716363584103375237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50720830477575722735583491 76081245716363584103375237)
        ·
          refine ⟨14265233571818172019382857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76081245716363584103375237 14265233571818172019382857)
          ·
            refine ⟨10698925178863629014537143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14265233571818172019382857 10698925178863629014537143)
            ·
              refine ⟨16048387768295443521805715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698925178863629014537143 16048387768295443521805715)
              ·
                refine ⟨24072581652443165282708573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16048387768295443521805715 24072581652443165282708573)
                ·
                  refine ⟨9027218119666186981015715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24072581652443165282708573 9027218119666186981015715)
                  ·
                    refine ⟨13540827179499280471523573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9027218119666186981015715 13540827179499280471523573)
                    ·
                      refine ⟨1269452548078057544205335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13540827179499280471523573 1269452548078057544205335)
                      ·
                        rfl

theorem cell23_2472250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_2472250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472250 prefixEnd_2472250 := by exact prefixLift 2472250
  have htrace : WordTrace (prefixWord ++ tailWord_2472250) baseStart_2472250 baseEnd_2472250 := by
    simpa [prefixWord, tailWord_2472250, baseEnd_2472250] using wordTrace_append hprefix tailTrace_2472250
  have hstable : (prefixWord ++ tailWord_2472250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472250).length < 2 ^ (prefixWord ++ tailWord_2472250).sum := by decide
  have hdescent : baseEnd_2472250 < baseStart_2472250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472264 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_2472264 : Nat := 118140960795 + 2472264 * 2 ^ 59
def prefixEnd_2472264 : Nat := 4983230072969 + 3 ^ 40 * 2472264 * 2
def baseEnd_2472264 : Nat := 1269459736807220489430271

theorem tailTrace_2472264 : CollatzResearch.WordTrace tailWord_2472264 prefixEnd_2472264 1269459736807220489430271 := by
  unfold tailWord_2472264
  simp only [CollatzResearch.WordTrace]
  refine ⟨45085437957708615960467923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60113917276944821280623897 45085437957708615960467923)
  ·
    refine ⟨67628156936562923940701885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45085437957708615960467923 67628156936562923940701885)
    ·
      refine ⟨25360558851211096477763207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67628156936562923940701885 25360558851211096477763207)
      ·
        refine ⟨38040838276816644716644811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25360558851211096477763207 38040838276816644716644811)
        ·
          refine ⟨57061257415224967074967217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38040838276816644716644811 57061257415224967074967217)
          ·
            refine ⟨42795943061418725306225413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57061257415224967074967217 42795943061418725306225413)
            ·
              refine ⟨8024239324016010994917265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42795943061418725306225413 8024239324016010994917265)
              ·
                refine ⟨6018179493012008246187949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024239324016010994917265 6018179493012008246187949)
                ·
                  refine ⟨2256817309879503092320481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6018179493012008246187949 2256817309879503092320481)
                  ·
                    refine ⟨1692612982409627319240361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256817309879503092320481 1692612982409627319240361)
                    ·
                      refine ⟨1269459736807220489430271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692612982409627319240361 1269459736807220489430271)
                      ·
                        rfl

theorem cell23_2472264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_2472264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472264 prefixEnd_2472264 := by exact prefixLift 2472264
  have htrace : WordTrace (prefixWord ++ tailWord_2472264) baseStart_2472264 baseEnd_2472264 := by
    simpa [prefixWord, tailWord_2472264, baseEnd_2472264] using wordTrace_append hprefix tailTrace_2472264
  have hstable : (prefixWord ++ tailWord_2472264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472264).length < 2 ^ (prefixWord ++ tailWord_2472264).sum := by decide
  have hdescent : baseEnd_2472264 < baseStart_2472264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472297 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_2472297 : Nat := 118140960795 + 2472297 * 2 ^ 59
def prefixEnd_2472297 : Nat := 4983230072969 + 3 ^ 40 * 2472297 * 2
def baseEnd_2472297 : Nat := 1269476681668818860317619

theorem tailTrace_2472297 : CollatzResearch.WordTrace tailWord_2472297 prefixEnd_2472297 1269476681668818860317619 := by
  unfold tailWord_2472297
  simp only [CollatzResearch.WordTrace]
  refine ⟨90172079524297678556887145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60114719682865119037924763 90172079524297678556887145)
  ·
    refine ⟨67629059643223258917665359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90172079524297678556887145 67629059643223258917665359)
    ·
      refine ⟨101443589464834888376498039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67629059643223258917665359 101443589464834888376498039)
      ·
        refine ⟨152165384197252332564747059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101443589464834888376498039 152165384197252332564747059)
        ·
          refine ⟨228248076295878498847120589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152165384197252332564747059 228248076295878498847120589)
          ·
            refine ⟨85593028610954437067670221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228248076295878498847120589 85593028610954437067670221)
            ·
              refine ⟨32097385729107913900376333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85593028610954437067670221 32097385729107913900376333)
              ·
                refine ⟨12036519648415467712641125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32097385729107913900376333 12036519648415467712641125)
                ·
                  refine ⟨2256847434077900196120211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12036519648415467712641125 2256847434077900196120211)
                  ·
                    refine ⟨3385271151116850294180317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2256847434077900196120211 3385271151116850294180317)
                    ·
                      refine ⟨1269476681668818860317619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3385271151116850294180317 1269476681668818860317619)
                      ·
                        rfl

theorem cell23_2472297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_2472297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472297 prefixEnd_2472297 := by exact prefixLift 2472297
  have htrace : WordTrace (prefixWord ++ tailWord_2472297) baseStart_2472297 baseEnd_2472297 := by
    simpa [prefixWord, tailWord_2472297, baseEnd_2472297] using wordTrace_append hprefix tailTrace_2472297
  have hstable : (prefixWord ++ tailWord_2472297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472297).length < 2 ^ (prefixWord ++ tailWord_2472297).sum := by decide
  have hdescent : baseEnd_2472297 < baseStart_2472297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472298 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2472298 : Nat := 118140960795 + 2472298 * 2 ^ 59
def prefixEnd_2472298 : Nat := 4983230072969 + 3 ^ 40 * 2472298 * 2
def baseEnd_2472298 : Nat := 1269477195149473356405115

theorem tailTrace_2472298 : CollatzResearch.WordTrace tailWord_2472298 prefixEnd_2472298 1269477195149473356405115 := by
  unfold tailWord_2472298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543028999323513931918387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60114743998196037151782365 22543028999323513931918387)
  ·
    refine ⟨33814543498985270897877581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22543028999323513931918387 33814543498985270897877581)
    ·
      refine ⟨12680453812119476586704093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33814543498985270897877581 12680453812119476586704093)
      ·
        refine ⟨4755170179544803720014035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12680453812119476586704093 4755170179544803720014035)
        ·
          refine ⟨7132755269317205580021053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4755170179544803720014035 7132755269317205580021053)
          ·
            refine ⟨2674783225993952092507895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7132755269317205580021053 2674783225993952092507895)
            ·
              refine ⟨4012174838990928138761843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674783225993952092507895 4012174838990928138761843)
              ·
                refine ⟨6018262258486392208142765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012174838990928138761843 6018262258486392208142765)
                ·
                  refine ⟨2256848346932397078053537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6018262258486392208142765 2256848346932397078053537)
                  ·
                    refine ⟨1692636260199297808540153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256848346932397078053537 1692636260199297808540153)
                    ·
                      refine ⟨1269477195149473356405115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692636260199297808540153 1269477195149473356405115)
                      ·
                        rfl

theorem cell23_2472298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2472298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472298 prefixEnd_2472298 := by exact prefixLift 2472298
  have htrace : WordTrace (prefixWord ++ tailWord_2472298) baseStart_2472298 baseEnd_2472298 := by
    simpa [prefixWord, tailWord_2472298, baseEnd_2472298] using wordTrace_append hprefix tailTrace_2472298
  have hstable : (prefixWord ++ tailWord_2472298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472298).length < 2 ^ (prefixWord ++ tailWord_2472298).sum := by decide
  have hdescent : baseEnd_2472298 < baseStart_2472298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472307 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 5, 3, 2]
def baseStart_2472307 : Nat := 118140960795 + 2472307 * 2 ^ 59
def prefixEnd_2472307 : Nat := 4983230072969 + 3 ^ 40 * 2472307 * 2
def baseEnd_2472307 : Nat := 1269481816475363821192573

theorem tailTrace_2472307 : CollatzResearch.WordTrace tailWord_2472307 prefixEnd_2472307 1269481816475363821192573 := by
  unfold tailWord_2472307
  simp only [CollatzResearch.WordTrace]
  refine ⟨90172444254261450264751175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60114962836174300176500783 90172444254261450264751175)
  ·
    refine ⟨135258666381392175397126763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90172444254261450264751175 135258666381392175397126763)
    ·
      refine ⟨202887999572088263095690145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135258666381392175397126763 202887999572088263095690145)
      ·
        refine ⟨152165999679066197321767609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202887999572088263095690145 152165999679066197321767609)
        ·
          refine ⟨114124499759299647991325707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152165999679066197321767609 114124499759299647991325707)
          ·
            refine ⟨171186749638949471986988561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114124499759299647991325707 171186749638949471986988561)
            ·
              refine ⟨128390062229212103990241421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171186749638949471986988561 128390062229212103990241421)
              ·
                refine ⟨48146273335954538996340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128390062229212103990241421 48146273335954538996340533)
                ·
                  refine ⟨4513713125245738030906925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48146273335954538996340533 4513713125245738030906925)
                  ·
                    refine ⟨1692642421967151761590097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4513713125245738030906925 1692642421967151761590097)
                    ·
                      refine ⟨1269481816475363821192573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692642421967151761590097 1269481816475363821192573)
                      ·
                        rfl

theorem cell23_2472307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3, 2].length) (baseStart_2472307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472307 prefixEnd_2472307 := by exact prefixLift 2472307
  have htrace : WordTrace (prefixWord ++ tailWord_2472307) baseStart_2472307 baseEnd_2472307 := by
    simpa [prefixWord, tailWord_2472307, baseEnd_2472307] using wordTrace_append hprefix tailTrace_2472307
  have hstable : (prefixWord ++ tailWord_2472307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472307).length < 2 ^ (prefixWord ++ tailWord_2472307).sum := by decide
  have hdescent : baseEnd_2472307 < baseStart_2472307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472324 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_2472324 : Nat := 118140960795 + 2472324 * 2 ^ 59
def prefixEnd_2472324 : Nat := 4983230072969 + 3 ^ 40 * 2472324 * 2
def baseEnd_2472324 : Nat := 1269490545646490254679995

theorem tailTrace_2472324 : CollatzResearch.WordTrace tailWord_2472324 prefixEnd_2472324 1269490545646490254679995 := by
  unfold tailWord_2472324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45086532147599931084060013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60115376196799908112080017 45086532147599931084060013)
  ·
    refine ⟨16907449555349974156522505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45086532147599931084060013 16907449555349974156522505)
    ·
      refine ⟨12680587166512480617391879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16907449555349974156522505 12680587166512480617391879)
      ·
        refine ⟨19020880749768720926087819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12680587166512480617391879 19020880749768720926087819)
        ·
          refine ⟨28531321124653081389131729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19020880749768720926087819 28531321124653081389131729)
          ·
            refine ⟨21398490843489811041848797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28531321124653081389131729 21398490843489811041848797)
            ·
              refine ⟨8024434066308679140693299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21398490843489811041848797 8024434066308679140693299)
              ·
                refine ⟨12036651099463018711039949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024434066308679140693299 12036651099463018711039949)
                ·
                  refine ⟨4513744162298632016639981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12036651099463018711039949 4513744162298632016639981)
                  ·
                    refine ⟨1692654060861987006239993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4513744162298632016639981 1692654060861987006239993)
                    ·
                      refine ⟨1269490545646490254679995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692654060861987006239993 1269490545646490254679995)
                      ·
                        rfl

theorem cell23_2472324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_2472324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472324 prefixEnd_2472324 := by exact prefixLift 2472324
  have htrace : WordTrace (prefixWord ++ tailWord_2472324) baseStart_2472324 baseEnd_2472324 := by
    simpa [prefixWord, tailWord_2472324, baseEnd_2472324] using wordTrace_append hprefix tailTrace_2472324
  have hstable : (prefixWord ++ tailWord_2472324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472324).length < 2 ^ (prefixWord ++ tailWord_2472324).sum := by decide
  have hdescent : baseEnd_2472324 < baseStart_2472324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472354 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_2472354 : Nat := 118140960795 + 2472354 * 2 ^ 59
def prefixEnd_2472354 : Nat := 4983230072969 + 3 ^ 40 * 2472354 * 2
def baseEnd_2472354 : Nat := 1269505950066125137304857

theorem tailTrace_2472354 : CollatzResearch.WordTrace tailWord_2472354 prefixEnd_2472354 1269505950066125137304857 := by
  unfold tailWord_2472354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543539621272794322928029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60116105656727451527808077 22543539621272794322928029)
  ·
    refine ⟨8453827357977297871098011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22543539621272794322928029 8453827357977297871098011)
    ·
      refine ⟨12680741036965946806647017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453827357977297871098011 12680741036965946806647017)
      ·
        refine ⟨9510555777724460104985263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12680741036965946806647017 9510555777724460104985263)
        ·
          refine ⟨14265833666586690157477895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9510555777724460104985263 14265833666586690157477895)
          ·
            refine ⟨21398750499880035236216843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14265833666586690157477895 21398750499880035236216843)
            ·
              refine ⟨32098125749820052854325265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21398750499880035236216843 32098125749820052854325265)
              ·
                refine ⟨24073594312365039640743949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32098125749820052854325265 24073594312365039640743949)
                ·
                  refine ⟨9027597867136889865278981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24073594312365039640743949 9027597867136889865278981)
                  ·
                    refine ⟨1692674600088166849739809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9027597867136889865278981 1692674600088166849739809)
                    ·
                      refine ⟨1269505950066125137304857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692674600088166849739809 1269505950066125137304857)
                      ·
                        rfl

theorem cell23_2472354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_2472354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472354 prefixEnd_2472354 := by exact prefixLift 2472354
  have htrace : WordTrace (prefixWord ++ tailWord_2472354) baseStart_2472354 baseEnd_2472354 := by
    simpa [prefixWord, tailWord_2472354, baseEnd_2472354] using wordTrace_append hprefix tailTrace_2472354
  have hstable : (prefixWord ++ tailWord_2472354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472354).length < 2 ^ (prefixWord ++ tailWord_2472354).sum := by decide
  have hdescent : baseEnd_2472354 < baseStart_2472354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472377 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 7]
def baseStart_2472377 : Nat := 118140960795 + 2472377 * 2 ^ 59
def prefixEnd_2472377 : Nat := 4983230072969 + 3 ^ 40 * 2472377 * 2
def baseEnd_2472377 : Nat := 141057528902353171924139

theorem tailTrace_2472377 : CollatzResearch.WordTrace tailWord_2472377 prefixEnd_2472377 141057528902353171924139 := by
  unfold tailWord_2472377
  simp only [CollatzResearch.WordTrace]
  refine ⟨90174997364007852219799385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60116664909338568146532923 90174997364007852219799385)
  ·
    refine ⟨67631248023005889164849539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90174997364007852219799385 67631248023005889164849539)
    ·
      refine ⟨101446872034508833747274309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67631248023005889164849539 101446872034508833747274309)
      ·
        refine ⟨19021288506470406327613933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101446872034508833747274309 19021288506470406327613933)
        ·
          refine ⟨7132983189926402372855225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19021288506470406327613933 7132983189926402372855225)
          ·
            refine ⟨5349737392444801779641419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7132983189926402372855225 5349737392444801779641419)
            ·
              refine ⟨8024606088667202669462129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349737392444801779641419 8024606088667202669462129)
              ·
                refine ⟨6018454566500402002096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024606088667202669462129 6018454566500402002096597)
                ·
                  refine ⟨141057528902353171924139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6018454566500402002096597 141057528902353171924139)
                  ·
                    rfl

theorem cell23_2472377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_2472377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472377 prefixEnd_2472377 := by exact prefixLift 2472377
  have htrace : WordTrace (prefixWord ++ tailWord_2472377) baseStart_2472377 baseEnd_2472377 := by
    simpa [prefixWord, tailWord_2472377, baseEnd_2472377] using wordTrace_append hprefix tailTrace_2472377
  have hstable : (prefixWord ++ tailWord_2472377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472377).length < 2 ^ (prefixWord ++ tailWord_2472377).sum := by decide
  have hdescent : baseEnd_2472377 < baseStart_2472377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472394 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_2472394 : Nat := 118140960795 + 2472394 * 2 ^ 59
def prefixEnd_2472394 : Nat := 4983230072969 + 3 ^ 40 * 2472394 * 2
def baseEnd_2472394 : Nat := 141058498810256108978297

theorem tailTrace_2472394 : CollatzResearch.WordTrace tailWord_2472394 prefixEnd_2472394 141058498810256108978297 := by
  unfold tailWord_2472394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543904351236566030792059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60117078269964176082112157 22543904351236566030792059)
  ·
    refine ⟨33815856526854849046188089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22543904351236566030792059 33815856526854849046188089)
    ·
      refine ⟨25361892395141136784641067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33815856526854849046188089 25361892395141136784641067)
      ·
        refine ⟨38042838592711705176961601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25361892395141136784641067 38042838592711705176961601)
        ·
          refine ⟨28532128944533778882721201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38042838592711705176961601 28532128944533778882721201)
          ·
            refine ⟨21399096708400334162040901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28532128944533778882721201 21399096708400334162040901)
            ·
              refine ⟨4012330632825062655382669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21399096708400334162040901 4012330632825062655382669)
              ·
                refine ⟨1504623987309398495768501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4012330632825062655382669 1504623987309398495768501)
                ·
                  refine ⟨141058498810256108978297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1504623987309398495768501 141058498810256108978297)
                  ·
                    rfl

theorem cell23_2472394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_2472394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472394 prefixEnd_2472394 := by exact prefixLift 2472394
  have htrace : WordTrace (prefixWord ++ tailWord_2472394) baseStart_2472394 baseEnd_2472394 := by
    simpa [prefixWord, tailWord_2472394, baseEnd_2472394] using wordTrace_append hprefix tailTrace_2472394
  have hstable : (prefixWord ++ tailWord_2472394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472394).length < 2 ^ (prefixWord ++ tailWord_2472394).sum := by decide
  have hdescent : baseEnd_2472394 < baseStart_2472394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472404 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2472404 : Nat := 118140960795 + 2472404 * 2 ^ 59
def prefixEnd_2472404 : Nat := 4983230072969 + 3 ^ 40 * 2472404 * 2
def baseEnd_2472404 : Nat := 1269531624098849941679627

theorem tailTrace_2472404 : CollatzResearch.WordTrace tailWord_2472404 prefixEnd_2472404 1269531624098849941679627 := by
  unfold tailWord_2472404
  simp only [CollatzResearch.WordTrace]
  refine ⟨45087991067455017915516133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60117321423273357220688177 45087991067455017915516133)
  ·
    refine ⟨8453998325147815859159275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45087991067455017915516133 8453998325147815859159275)
    ·
      refine ⟨12680997487721723788738913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453998325147815859159275 12680997487721723788738913)
      ·
        refine ⟨9510748115791292841554185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12680997487721723788738913 9510748115791292841554185)
        ·
          refine ⟨7133061086843469631165639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9510748115791292841554185 7133061086843469631165639)
          ·
            refine ⟨10699591630265204446748459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7133061086843469631165639 10699591630265204446748459)
            ·
              refine ⟨16049387445397806670122689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10699591630265204446748459 16049387445397806670122689)
              ·
                refine ⟨12037040584048355002592017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16049387445397806670122689 12037040584048355002592017)
                ·
                  refine ⟨9027780438036266251944013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12037040584048355002592017 9027780438036266251944013)
                  ·
                    refine ⟨3385417664263599844479005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9027780438036266251944013 3385417664263599844479005)
                    ·
                      refine ⟨1269531624098849941679627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3385417664263599844479005 1269531624098849941679627)
                      ·
                        rfl

theorem cell23_2472404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2472404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472404 prefixEnd_2472404 := by exact prefixLift 2472404
  have htrace : WordTrace (prefixWord ++ tailWord_2472404) baseStart_2472404 baseEnd_2472404 := by
    simpa [prefixWord, tailWord_2472404, baseEnd_2472404] using wordTrace_append hprefix tailTrace_2472404
  have hstable : (prefixWord ++ tailWord_2472404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472404).length < 2 ^ (prefixWord ++ tailWord_2472404).sum := by decide
  have hdescent : baseEnd_2472404 < baseStart_2472404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472447 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_2472447 : Nat := 118140960795 + 2472447 * 2 ^ 59
def prefixEnd_2472447 : Nat := 4983230072969 + 3 ^ 40 * 2472447 * 2
def baseEnd_2472447 : Nat := 1269553703766993273441929

theorem tailTrace_2472447 : CollatzResearch.WordTrace tailWord_2472447 prefixEnd_2472447 1269553703766993273441929 := by
  unfold tailWord_2472447
  simp only [CollatzResearch.WordTrace]
  refine ⟨90177550473754254174847595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60118366982502836116565063 90177550473754254174847595)
  ·
    refine ⟨135266325710631381262271393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90177550473754254174847595 135266325710631381262271393)
    ·
      refine ⟨101449744282973535946703545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135266325710631381262271393 101449744282973535946703545)
      ·
        refine ⟨76087308212230151960027659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101449744282973535946703545 76087308212230151960027659)
        ·
          refine ⟨114130962318345227940041489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76087308212230151960027659 114130962318345227940041489)
          ·
            refine ⟨85598221738758920955031117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114130962318345227940041489 85598221738758920955031117)
            ·
              refine ⟨32099333152034595358136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85598221738758920955031117 32099333152034595358136669)
              ·
                refine ⟨12037249932012973259301251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32099333152034595358136669 12037249932012973259301251)
                ·
                  refine ⟨18055874898019459888951877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12037249932012973259301251 18055874898019459888951877)
                  ·
                    refine ⟨3385476543378648729178477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18055874898019459888951877 3385476543378648729178477)
                    ·
                      refine ⟨1269553703766993273441929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3385476543378648729178477 1269553703766993273441929)
                      ·
                        rfl

theorem cell23_2472447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_2472447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472447 prefixEnd_2472447 := by exact prefixLift 2472447
  have htrace : WordTrace (prefixWord ++ tailWord_2472447) baseStart_2472447 baseEnd_2472447 := by
    simpa [prefixWord, tailWord_2472447, baseEnd_2472447] using wordTrace_append hprefix tailTrace_2472447
  have hstable : (prefixWord ++ tailWord_2472447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472447).length < 2 ^ (prefixWord ++ tailWord_2472447).sum := by decide
  have hdescent : baseEnd_2472447 < baseStart_2472447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472467 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 6]
def baseStart_2472467 : Nat := 118140960795 + 2472467 * 2 ^ 59
def prefixEnd_2472467 : Nat := 4983230072969 + 3 ^ 40 * 2472467 * 2
def baseEnd_2472467 : Nat := 141062663708898132799093

theorem tailTrace_2472467 : CollatzResearch.WordTrace tailWord_2472467 prefixEnd_2472467 141062663708898132799093 := by
  unfold tailWord_2472467
  simp only [CollatzResearch.WordTrace]
  refine ⟨90178279933681797590575655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60118853289121198393717103 90178279933681797590575655)
  ·
    refine ⟨135267419900522696385863483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90178279933681797590575655 135267419900522696385863483)
    ·
      refine ⟨202901129850784044578795225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135267419900522696385863483 202901129850784044578795225)
      ·
        refine ⟨152175847388088033434096419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202901129850784044578795225 152175847388088033434096419)
        ·
          refine ⟨228263771082132050151144629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152175847388088033434096419 228263771082132050151144629)
          ·
            refine ⟨21399728538949879701669809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228263771082132050151144629 21399728538949879701669809)
            ·
              refine ⟨16049796404212409776252357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21399728538949879701669809 16049796404212409776252357)
              ·
                refine ⟨3009336825789826833047317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16049796404212409776252357 3009336825789826833047317)
                ·
                  refine ⟨141062663708898132799093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009336825789826833047317 141062663708898132799093)
                  ·
                    rfl

theorem cell23_2472467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 6].length) (baseStart_2472467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472467 prefixEnd_2472467 := by exact prefixLift 2472467
  have htrace : WordTrace (prefixWord ++ tailWord_2472467) baseStart_2472467 baseEnd_2472467 := by
    simpa [prefixWord, tailWord_2472467, baseEnd_2472467] using wordTrace_append hprefix tailTrace_2472467
  have hstable : (prefixWord ++ tailWord_2472467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472467).length < 2 ^ (prefixWord ++ tailWord_2472467).sum := by decide
  have hdescent : baseEnd_2472467 < baseStart_2472467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472518 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2472518 : Nat := 118140960795 + 2472518 * 2 ^ 59
def prefixEnd_2472518 : Nat := 4983230072969 + 3 ^ 40 * 2472518 * 2
def baseEnd_2472518 : Nat := 141065573432606943961567

theorem tailTrace_2472518 : CollatzResearch.WordTrace tailWord_2472518 prefixEnd_2472518 141065573432606943961567 := by
  unfold tailWord_2472518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818129376765532290646319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60120093370998022200454805 2818129376765532290646319)
  ·
    refine ⟨4227194065148298435969479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2818129376765532290646319 4227194065148298435969479)
    ·
      refine ⟨6340791097722447653954219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4227194065148298435969479 6340791097722447653954219)
      ·
        refine ⟨9511186646583671480931329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340791097722447653954219 9511186646583671480931329)
        ·
          refine ⟨7133389984937753610698497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9511186646583671480931329 7133389984937753610698497)
          ·
            refine ⟨5350042488703315208023873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7133389984937753610698497 5350042488703315208023873)
            ·
              refine ⟨4012531866527486406017905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350042488703315208023873 4012531866527486406017905)
              ·
                refine ⟨3009398899895614804513429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012531866527486406017905 3009398899895614804513429)
                ·
                  refine ⟨141065573432606943961567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009398899895614804513429 141065573432606943961567)
                  ·
                    rfl

theorem cell23_2472518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2472518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472518 prefixEnd_2472518 := by exact prefixLift 2472518
  have htrace : WordTrace (prefixWord ++ tailWord_2472518) baseStart_2472518 baseEnd_2472518 := by
    simpa [prefixWord, tailWord_2472518, baseEnd_2472518] using wordTrace_append hprefix tailTrace_2472518
  have hstable : (prefixWord ++ tailWord_2472518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472518).length < 2 ^ (prefixWord ++ tailWord_2472518).sum := by decide
  have hdescent : baseEnd_2472518 < baseStart_2472518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472565 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2472565 : Nat := 118140960795 + 2472565 * 2 ^ 59
def prefixEnd_2472565 : Nat := 4983230072969 + 3 ^ 40 * 2472565 * 2
def baseEnd_2472565 : Nat := 423204764828074603922129

theorem tailTrace_2472565 : CollatzResearch.WordTrace tailWord_2472565 prefixEnd_2472565 423204764828074603922129 := by
  unfold tailWord_2472565
  simp only [CollatzResearch.WordTrace]
  refine ⟨90181854287326760327643149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60121236191551173551762099 90181854287326760327643149)
  ·
    refine ⟨33818195357747535122866181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90181854287326760327643149 33818195357747535122866181)
    ·
      refine ⟨6340911629577662835537409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33818195357747535122866181 6340911629577662835537409)
      ·
        refine ⟨4755683722183247126653057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6340911629577662835537409 4755683722183247126653057)
        ·
          refine ⟨3566762791637435344989793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4755683722183247126653057 3566762791637435344989793)
          ·
            refine ⟨2675072093728076508742345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566762791637435344989793 2675072093728076508742345)
            ·
              refine ⟨2006304070296057381556759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675072093728076508742345 2006304070296057381556759)
              ·
                refine ⟨3009456105444086072335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006304070296057381556759 3009456105444086072335139)
                ·
                  refine ⟨4514184158166129108502709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009456105444086072335139 4514184158166129108502709)
                  ·
                    refine ⟨423204764828074603922129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4514184158166129108502709 423204764828074603922129)
                    ·
                      rfl

theorem cell23_2472565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2472565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472565 prefixEnd_2472565 := by exact prefixLift 2472565
  have htrace : WordTrace (prefixWord ++ tailWord_2472565) baseStart_2472565 baseEnd_2472565 := by
    simpa [prefixWord, tailWord_2472565, baseEnd_2472565] using wordTrace_append hprefix tailTrace_2472565
  have hstable : (prefixWord ++ tailWord_2472565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472565).length < 2 ^ (prefixWord ++ tailWord_2472565).sum := by decide
  have hdescent : baseEnd_2472565 < baseStart_2472565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472587 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 7]
def baseStart_2472587 : Nat := 118140960795 + 2472587 * 2 ^ 59
def prefixEnd_2472587 : Nat := 4983230072969 + 3 ^ 40 * 2472587 * 2
def baseEnd_2472587 : Nat := 423208530352874241897095

theorem tailTrace_2472587 : CollatzResearch.WordTrace tailWord_2472587 prefixEnd_2472587 423208530352874241897095 := by
  unfold tailWord_2472587
  simp only [CollatzResearch.WordTrace]
  refine ⟨90182656693247058084944015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60121771128831372056629343 90182656693247058084944015)
  ·
    refine ⟨135273985039870587127416023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90182656693247058084944015 135273985039870587127416023)
    ·
      refine ⟨202910977559805880691124035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135273985039870587127416023 202910977559805880691124035)
      ·
        refine ⟨304366466339708821036686053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202910977559805880691124035 304366466339708821036686053)
        ·
          refine ⟨57068712438695403944378635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304366466339708821036686053 57068712438695403944378635)
          ·
            refine ⟨85603068658043105916567953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57068712438695403944378635 85603068658043105916567953)
            ·
              refine ⟨64202301493532329437425965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85603068658043105916567953 64202301493532329437425965)
              ·
                refine ⟨24075863060074623539034737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64202301493532329437425965 24075863060074623539034737)
                ·
                  refine ⟨18056897295055967654276053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24075863060074623539034737 18056897295055967654276053)
                  ·
                    refine ⟨423208530352874241897095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18056897295055967654276053 423208530352874241897095)
                    ·
                      rfl

theorem cell23_2472587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_2472587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472587 prefixEnd_2472587 := by exact prefixLift 2472587
  have htrace : WordTrace (prefixWord ++ tailWord_2472587) baseStart_2472587 baseEnd_2472587 := by
    simpa [prefixWord, tailWord_2472587, baseEnd_2472587] using wordTrace_append hprefix tailTrace_2472587
  have hstable : (prefixWord ++ tailWord_2472587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472587).length < 2 ^ (prefixWord ++ tailWord_2472587).sum := by decide
  have hdescent : baseEnd_2472587 < baseStart_2472587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472608 : List Nat := [2, 1, 1, 4, 5, 1, 2, 7]
def baseStart_2472608 : Nat := 118140960795 + 2472608 * 2 ^ 59
def prefixEnd_2472608 : Nat := 4983230072969 + 3 ^ 40 * 2472608 * 2
def baseEnd_2472608 : Nat := 47023569413050634945507

theorem tailTrace_2472608 : CollatzResearch.WordTrace tailWord_2472608 prefixEnd_2472608 47023569413050634945507 := by
  unfold tailWord_2472608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45091711313085489335729239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60122281750780652447638985 45091711313085489335729239)
  ·
    refine ⟨67637566969628234003593859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45091711313085489335729239 67637566969628234003593859)
    ·
      refine ⟨101456350454442351005390789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67637566969628234003593859 101456350454442351005390789)
      ·
        refine ⟨19023065710207940813510773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101456350454442351005390789 19023065710207940813510773)
        ·
          refine ⟨1783412410331994451266635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19023065710207940813510773 1783412410331994451266635)
          ·
            refine ⟨2675118615497991676899953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783412410331994451266635 2675118615497991676899953)
            ·
              refine ⟨2006338961623493757674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675118615497991676899953 2006338961623493757674965)
              ·
                refine ⟨47023569413050634945507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2006338961623493757674965 47023569413050634945507)
                ·
                  rfl

theorem cell23_2472608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 7].length) (baseStart_2472608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472608 prefixEnd_2472608 := by exact prefixLift 2472608
  have htrace : WordTrace (prefixWord ++ tailWord_2472608) baseStart_2472608 baseEnd_2472608 := by
    simpa [prefixWord, tailWord_2472608, baseEnd_2472608] using wordTrace_append hprefix tailTrace_2472608
  have hstable : (prefixWord ++ tailWord_2472608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472608).length < 2 ^ (prefixWord ++ tailWord_2472608).sum := by decide
  have hdescent : baseEnd_2472608 < baseStart_2472608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_2472617 : Nat := 118140960795 + 2472617 * 2 ^ 59
def prefixEnd_2472617 : Nat := 4983230072969 + 3 ^ 40 * 2472617 * 2
def baseEnd_2472617 : Nat := 423213665159419202772049

theorem tailTrace_2472617 : CollatzResearch.WordTrace tailWord_2472617 prefixEnd_2472617 423213665159419202772049 := by
  unfold tailWord_2472617
  simp only [CollatzResearch.WordTrace]
  refine ⟨90183750883138373208536105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60122500588758915472357403 90183750883138373208536105)
  ·
    refine ⟨67637813162353779906402079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90183750883138373208536105 67637813162353779906402079)
    ·
      refine ⟨101456719743530669859603119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67637813162353779906402079 101456719743530669859603119)
      ·
        refine ⟨152185079615296004789404679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101456719743530669859603119 152185079615296004789404679)
        ·
          refine ⟨228277619422944007184107019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152185079615296004789404679 228277619422944007184107019)
          ·
            refine ⟨342416429134416010776160529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228277619422944007184107019 342416429134416010776160529)
            ·
              refine ⟨256812321850812008082120397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342416429134416010776160529 256812321850812008082120397)
              ·
                refine ⟨96304620694054503030795149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256812321850812008082120397 96304620694054503030795149)
                ·
                  refine ⟨36114232760270438636548181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96304620694054503030795149 36114232760270438636548181)
                  ·
                    refine ⟨423213665159419202772049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36114232760270438636548181 423213665159419202772049)
                    ·
                      rfl

theorem cell23_2472617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_2472617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472617 prefixEnd_2472617 := by exact prefixLift 2472617
  have htrace : WordTrace (prefixWord ++ tailWord_2472617) baseStart_2472617 baseEnd_2472617 := by
    simpa [prefixWord, tailWord_2472617, baseEnd_2472617] using wordTrace_append hprefix tailTrace_2472617
  have hstable : (prefixWord ++ tailWord_2472617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472617).length < 2 ^ (prefixWord ++ tailWord_2472617).sum := by decide
  have hdescent : baseEnd_2472617 < baseStart_2472617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472646 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2472646 : Nat := 118140960795 + 2472646 * 2 ^ 59
def prefixEnd_2472646 : Nat := 4983230072969 + 3 ^ 40 * 2472646 * 2
def baseEnd_2472646 : Nat := 423218628805745998284505

theorem tailTrace_2472646 : CollatzResearch.WordTrace tailWord_2472646 prefixEnd_2472646 423218628805745998284505 := by
  unfold tailWord_2472646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818275268751040973791931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60123205733355540774227861 2818275268751040973791931)
  ·
    refine ⟨4227412903126561460687897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2818275268751040973791931 4227412903126561460687897)
    ·
      refine ⟨3170559677344921095515923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4227412903126561460687897 3170559677344921095515923)
      ·
        refine ⟨4755839516017381643273885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170559677344921095515923 4755839516017381643273885)
        ·
          refine ⟨1783439818506518116227707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4755839516017381643273885 1783439818506518116227707)
          ·
            refine ⟨2675159727759777174341561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783439818506518116227707 2675159727759777174341561)
            ·
              refine ⟨2006369795819832880756171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675159727759777174341561 2006369795819832880756171)
              ·
                refine ⟨3009554693729749321134257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006369795819832880756171 3009554693729749321134257)
                ·
                  refine ⟨2257166020297311990850693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009554693729749321134257 2257166020297311990850693)
                  ·
                    refine ⟨423218628805745998284505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257166020297311990850693 423218628805745998284505)
                    ·
                      rfl

theorem cell23_2472646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2472646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472646 prefixEnd_2472646 := by exact prefixLift 2472646
  have htrace : WordTrace (prefixWord ++ tailWord_2472646) baseStart_2472646 baseEnd_2472646 := by
    simpa [prefixWord, tailWord_2472646, baseEnd_2472646] using wordTrace_append hprefix tailTrace_2472646
  have hstable : (prefixWord ++ tailWord_2472646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472646).length < 2 ^ (prefixWord ++ tailWord_2472646).sum := by decide
  have hdescent : baseEnd_2472646 < baseStart_2472646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472652 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2472652 : Nat := 118140960795 + 2472652 * 2 ^ 59
def prefixEnd_2472652 : Nat := 4983230072969 + 3 ^ 40 * 2472652 * 2
def baseEnd_2472652 : Nat := 1269658967301164971378487

theorem tailTrace_2472652 : CollatzResearch.WordTrace tailWord_2472652 prefixEnd_2472652 1269658967301164971378487 := by
  unfold tailWord_2472652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45092513719005787093030105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60123351625341049457373473 45092513719005787093030105)
  ·
    refine ⟨33819385289254340319772579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45092513719005787093030105 33819385289254340319772579)
    ·
      refine ⟨50729077933881510479658869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33819385289254340319772579 50729077933881510479658869)
      ·
        refine ⟨4755851056301391607468019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50729077933881510479658869 4755851056301391607468019)
        ·
          refine ⟨7133776584452087411202029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4755851056301391607468019 7133776584452087411202029)
          ·
            refine ⟨2675166219169532779200761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7133776584452087411202029 2675166219169532779200761)
            ·
              refine ⟨2006374664377149584400571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675166219169532779200761 2006374664377149584400571)
              ·
                refine ⟨3009561996565724376600857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006374664377149584400571 3009561996565724376600857)
                ·
                  refine ⟨2257171497424293282450643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009561996565724376600857 2257171497424293282450643)
                  ·
                    refine ⟨3385757246136439923675965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257171497424293282450643 3385757246136439923675965)
                    ·
                      refine ⟨1269658967301164971378487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3385757246136439923675965 1269658967301164971378487)
                      ·
                        rfl

theorem cell23_2472652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2472652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472652 prefixEnd_2472652 := by exact prefixLift 2472652
  have htrace : WordTrace (prefixWord ++ tailWord_2472652) baseStart_2472652 baseEnd_2472652 := by
    simpa [prefixWord, tailWord_2472652, baseEnd_2472652] using wordTrace_append hprefix tailTrace_2472652
  have hstable : (prefixWord ++ tailWord_2472652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472652).length < 2 ^ (prefixWord ++ tailWord_2472652).sum := by decide
  have hdescent : baseEnd_2472652 < baseStart_2472652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472698 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_2472698 : Nat := 118140960795 + 2472698 * 2 ^ 59
def prefixEnd_2472698 : Nat := 4983230072969 + 3 ^ 40 * 2472698 * 2
def baseEnd_2472698 : Nat := 141075843045696865711475

theorem tailTrace_2472698 : CollatzResearch.WordTrace tailWord_2472698 prefixEnd_2472698 141075843045696865711475 := by
  unfold tailWord_2472698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22546676298961231010558687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60124470130563282694823165 22546676298961231010558687)
  ·
    refine ⟨33820014448441846515838031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22546676298961231010558687 33820014448441846515838031)
    ·
      refine ⟨50730021672662769773757047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33820014448441846515838031 50730021672662769773757047)
      ·
        refine ⟨76095032508994154660635571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50730021672662769773757047 76095032508994154660635571)
        ·
          refine ⟨114142548763491231990953357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76095032508994154660635571 114142548763491231990953357)
          ·
            refine ⟨42803455786309211996607509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114142548763491231990953357 42803455786309211996607509)
            ·
              refine ⟨2006411989983244312340977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42803455786309211996607509 2006411989983244312340977)
              ·
                refine ⟨1504808992487433234255733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006411989983244312340977 1504808992487433234255733)
                ·
                  refine ⟨141075843045696865711475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1504808992487433234255733 141075843045696865711475)
                  ·
                    rfl

theorem cell23_2472698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_2472698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472698 prefixEnd_2472698 := by exact prefixLift 2472698
  have htrace : WordTrace (prefixWord ++ tailWord_2472698) baseStart_2472698 baseEnd_2472698 := by
    simpa [prefixWord, tailWord_2472698, baseEnd_2472698] using wordTrace_append hprefix tailTrace_2472698
  have hstable : (prefixWord ++ tailWord_2472698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472698).length < 2 ^ (prefixWord ++ tailWord_2472698).sum := by decide
  have hdescent : baseEnd_2472698 < baseStart_2472698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472701 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_2472701 : Nat := 118140960795 + 2472701 * 2 ^ 59
def prefixEnd_2472701 : Nat := 4983230072969 + 3 ^ 40 * 2472701 * 2
def baseEnd_2472701 : Nat := 1269684127853235279665761

theorem tailTrace_2472701 : CollatzResearch.WordTrace tailWord_2472701 prefixEnd_2472701 1269684127853235279665761 := by
  unfold tailWord_2472701
  simp only [CollatzResearch.WordTrace]
  refine ⟨90186814614834055554593957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60124543076556037036395971 90186814614834055554593957)
  ·
    refine ⟨16910027740281385416486367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90186814614834055554593957 16910027740281385416486367)
    ·
      refine ⟨25365041610422078124729551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16910027740281385416486367 25365041610422078124729551)
      ·
        refine ⟨38047562415633117187094327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25365041610422078124729551 38047562415633117187094327)
        ·
          refine ⟨57071343623449675780641491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38047562415633117187094327 57071343623449675780641491)
          ·
            refine ⟨85607015435174513670962237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57071343623449675780641491 85607015435174513670962237)
            ·
              refine ⟨32102630788190442626610839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85607015435174513670962237 32102630788190442626610839)
              ·
                refine ⟨48153946182285663939916259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32102630788190442626610839 48153946182285663939916259)
                ·
                  refine ⟨72230919273428495909874389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48153946182285663939916259 72230919273428495909874389)
                  ·
                    refine ⟨1692912170470980372887681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72230919273428495909874389 1692912170470980372887681)
                    ·
                      refine ⟨1269684127853235279665761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692912170470980372887681 1269684127853235279665761)
                      ·
                        rfl

theorem cell23_2472701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_2472701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472701 prefixEnd_2472701 := by exact prefixLift 2472701
  have htrace : WordTrace (prefixWord ++ tailWord_2472701) baseStart_2472701 baseEnd_2472701 := by
    simpa [prefixWord, tailWord_2472701, baseEnd_2472701] using wordTrace_append hprefix tailTrace_2472701
  have hstable : (prefixWord ++ tailWord_2472701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472701).length < 2 ^ (prefixWord ++ tailWord_2472701).sum := by decide
  have hdescent : baseEnd_2472701 < baseStart_2472701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472731 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 4, 2]
def baseStart_2472731 : Nat := 118140960795 + 2472731 * 2 ^ 59
def prefixEnd_2472731 : Nat := 4983230072969 + 3 ^ 40 * 2472731 * 2
def baseEnd_2472731 : Nat := 1269699532272870162290623

theorem tailTrace_2472731 : CollatzResearch.WordTrace tailWord_2472731 prefixEnd_2472731 1269699532272870162290623 := by
  unfold tailWord_2472731
  simp only [CollatzResearch.WordTrace]
  refine ⟨90187908804725370678186047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60125272536483580452124031 90187908804725370678186047)
  ·
    refine ⟨135281863207088056017279071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90187908804725370678186047 135281863207088056017279071)
    ·
      refine ⟨202922794810632084025918607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135281863207088056017279071 202922794810632084025918607)
      ·
        refine ⟨304384192215948126038877911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202922794810632084025918607 304384192215948126038877911)
        ·
          refine ⟨456576288323922189058316867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304384192215948126038877911 456576288323922189058316867)
          ·
            refine ⟨684864432485883283587475301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456576288323922189058316867 684864432485883283587475301)
            ·
              refine ⟨128412081091103115672651619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 684864432485883283587475301 128412081091103115672651619)
              ·
                refine ⟨192618121636654673508977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128412081091103115672651619 192618121636654673508977429)
                ·
                  refine ⟨9028974451718187820733317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192618121636654673508977429 9028974451718187820733317)
                  ·
                    refine ⟨1692932709697160216387497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9028974451718187820733317 1692932709697160216387497)
                    ·
                      refine ⟨1269699532272870162290623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1692932709697160216387497 1269699532272870162290623)
                      ·
                        rfl

theorem cell23_2472731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4, 2].length) (baseStart_2472731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472731 prefixEnd_2472731 := by exact prefixLift 2472731
  have htrace : WordTrace (prefixWord ++ tailWord_2472731) baseStart_2472731 baseEnd_2472731 := by
    simpa [prefixWord, tailWord_2472731, baseEnd_2472731] using wordTrace_append hprefix tailTrace_2472731
  have hstable : (prefixWord ++ tailWord_2472731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472731).length < 2 ^ (prefixWord ++ tailWord_2472731).sum := by decide
  have hdescent : baseEnd_2472731 < baseStart_2472731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472741 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_2472741 : Nat := 118140960795 + 2472741 * 2 ^ 59
def prefixEnd_2472741 : Nat := 4983230072969 + 3 ^ 40 * 2472741 * 2
def baseEnd_2472741 : Nat := 423234889026471707721859

theorem tailTrace_2472741 : CollatzResearch.WordTrace tailWord_2472741 prefixEnd_2472741 423234889026471707721859 := by
  unfold tailWord_2472741
  simp only [CollatzResearch.WordTrace]
  refine ⟨90188273534689142386050077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60125515689792761590700051 90188273534689142386050077)
  ·
    refine ⟨33820602575508428394768779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90188273534689142386050077 33820602575508428394768779)
    ·
      refine ⟨50730903863262642592153169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33820602575508428394768779 50730903863262642592153169)
      ·
        refine ⟨38048177897446981944114877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50730903863262642592153169 38048177897446981944114877)
        ·
          refine ⟨14268066711542618229043079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38048177897446981944114877 14268066711542618229043079)
          ·
            refine ⟨21402100067313927343564619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14268066711542618229043079 21402100067313927343564619)
            ·
              refine ⟨32103150100970891015346929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21402100067313927343564619 32103150100970891015346929)
              ·
                refine ⟨24077362575728168261510197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32103150100970891015346929 24077362575728168261510197)
                ·
                  refine ⟨2257252741474515774516581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24077362575728168261510197 2257252741474515774516581)
                  ·
                    refine ⟨423234889026471707721859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257252741474515774516581 423234889026471707721859)
                    ·
                      rfl

theorem cell23_2472741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_2472741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472741 prefixEnd_2472741 := by exact prefixLift 2472741
  have htrace : WordTrace (prefixWord ++ tailWord_2472741) baseStart_2472741 baseEnd_2472741 := by
    simpa [prefixWord, tailWord_2472741, baseEnd_2472741] using wordTrace_append hprefix tailTrace_2472741
  have hstable : (prefixWord ++ tailWord_2472741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472741).length < 2 ^ (prefixWord ++ tailWord_2472741).sum := by decide
  have hdescent : baseEnd_2472741 < baseStart_2472741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 1, 1, 3]
def baseStart_2472815 : Nat := 118140960795 + 2472815 * 2 ^ 59
def prefixEnd_2472815 : Nat := 4983230072969 + 3 ^ 40 * 2472815 * 2
def baseEnd_2472815 : Nat := 1269742664647847833640237

theorem tailTrace_2472815 : CollatzResearch.WordTrace tailWord_2472815 prefixEnd_2472815 1269742664647847833640237 := by
  unfold tailWord_2472815
  simp only [CollatzResearch.WordTrace]
  refine ⟨90190972536421053024243899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60127315024280702016162599 90190972536421053024243899)
  ·
    refine ⟨135286458804631579536365849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90190972536421053024243899 135286458804631579536365849)
    ·
      refine ⟨101464844103473684652274387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135286458804631579536365849 101464844103473684652274387)
      ·
        refine ⟨152197266155210526978411581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101464844103473684652274387 152197266155210526978411581)
        ·
          refine ⟨57073974808203947616904343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152197266155210526978411581 57073974808203947616904343)
          ·
            refine ⟨85610962212305921425356515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57073974808203947616904343 85610962212305921425356515)
            ·
              refine ⟨128416443318458882138034773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85610962212305921425356515 128416443318458882138034773)
              ·
                refine ⟨1504880195138190025055095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128416443318458882138034773 1504880195138190025055095)
                ·
                  refine ⟨2257320292707285037582643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504880195138190025055095 2257320292707285037582643)
                  ·
                    refine ⟨3385980439060927556373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257320292707285037582643 3385980439060927556373965)
                    ·
                      refine ⟨1269742664647847833640237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3385980439060927556373965 1269742664647847833640237)
                      ·
                        rfl

theorem cell23_2472815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 1, 3].length) (baseStart_2472815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472815 prefixEnd_2472815 := by exact prefixLift 2472815
  have htrace : WordTrace (prefixWord ++ tailWord_2472815) baseStart_2472815 baseEnd_2472815 := by
    simpa [prefixWord, tailWord_2472815, baseEnd_2472815] using wordTrace_append hprefix tailTrace_2472815
  have hstable : (prefixWord ++ tailWord_2472815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472815).length < 2 ^ (prefixWord ++ tailWord_2472815).sum := by decide
  have hdescent : baseEnd_2472815 < baseStart_2472815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472822 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2472822 : Nat := 118140960795 + 2472822 * 2 ^ 59
def prefixEnd_2472822 : Nat := 4983230072969 + 3 ^ 40 * 2472822 * 2
def baseEnd_2472822 : Nat := 141082917668047700694745

theorem tailTrace_2472822 : CollatzResearch.WordTrace tailWord_2472822 prefixEnd_2472822 141082917668047700694745 := by
  unfold tailWord_2472822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636951740462230826234295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60127485231597128813165813 5636951740462230826234295)
  ·
    refine ⟨8455427610693346239351443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5636951740462230826234295 8455427610693346239351443)
    ·
      refine ⟨12683141416040019359027165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455427610693346239351443 12683141416040019359027165)
      ·
        refine ⟨4756178031015007259635187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12683141416040019359027165 4756178031015007259635187)
        ·
          refine ⟨7134267046522510889452781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756178031015007259635187 7134267046522510889452781)
          ·
            refine ⟨2675350142445941583544793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7134267046522510889452781 2675350142445941583544793)
            ·
              refine ⟨2006512606834456187658595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675350142445941583544793 2006512606834456187658595)
              ·
                refine ⟨3009768910251684281487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006512606834456187658595 3009768910251684281487893)
                ·
                  refine ⟨141082917668047700694745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009768910251684281487893 141082917668047700694745)
                  ·
                    rfl

theorem cell23_2472822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2472822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472822 prefixEnd_2472822 := by exact prefixLift 2472822
  have htrace : WordTrace (prefixWord ++ tailWord_2472822) baseStart_2472822 baseEnd_2472822 := by
    simpa [prefixWord, tailWord_2472822, baseEnd_2472822] using wordTrace_append hprefix tailTrace_2472822
  have hstable : (prefixWord ++ tailWord_2472822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472822).length < 2 ^ (prefixWord ++ tailWord_2472822).sum := by decide
  have hdescent : baseEnd_2472822 < baseStart_2472822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472842 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2472842 : Nat := 118140960795 + 2472842 * 2 ^ 59
def prefixEnd_2472842 : Nat := 4983230072969 + 3 ^ 40 * 2472842 * 2
def baseEnd_2472842 : Nat := 1269756528625519228002613

theorem tailTrace_2472842 : CollatzResearch.WordTrace tailWord_2472842 prefixEnd_2472842 1269756528625519228002613 := by
  unfold tailWord_2472842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22547989326830809158869195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60127971538215491090317853 22547989326830809158869195)
  ·
    refine ⟨33821983990246213738303793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22547989326830809158869195 33821983990246213738303793)
    ·
      refine ⟨25366487992684660303727845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33821983990246213738303793 25366487992684660303727845)
      ·
        refine ⟨4756216498628373806948971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25366487992684660303727845 4756216498628373806948971)
        ·
          refine ⟨7134324747942560710423457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756216498628373806948971 7134324747942560710423457)
          ·
            refine ⟨5350743560956920532817593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7134324747942560710423457 5350743560956920532817593)
            ·
              refine ⟨4013057670717690399613195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350743560956920532817593 4013057670717690399613195)
              ·
                refine ⟨6019586506076535599419793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013057670717690399613195 6019586506076535599419793)
                ·
                  refine ⟨4514689879557401699564845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6019586506076535599419793 4514689879557401699564845)
                  ·
                    refine ⟨1693008704834025637336817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4514689879557401699564845 1693008704834025637336817)
                    ·
                      refine ⟨1269756528625519228002613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693008704834025637336817 1269756528625519228002613)
                      ·
                        rfl

theorem cell23_2472842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2472842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472842 prefixEnd_2472842 := by exact prefixLift 2472842
  have htrace : WordTrace (prefixWord ++ tailWord_2472842) baseStart_2472842 baseEnd_2472842 := by
    simpa [prefixWord, tailWord_2472842, baseEnd_2472842] using wordTrace_append hprefix tailTrace_2472842
  have hstable : (prefixWord ++ tailWord_2472842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472842).length < 2 ^ (prefixWord ++ tailWord_2472842).sum := by decide
  have hdescent : baseEnd_2472842 < baseStart_2472842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472855 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_2472855 : Nat := 118140960795 + 2472855 * 2 ^ 59
def prefixEnd_2472855 : Nat := 4983230072969 + 3 ^ 40 * 2472855 * 2
def baseEnd_2472855 : Nat := 1269763203874027677140053

theorem tailTrace_2472855 : CollatzResearch.WordTrace tailWord_2472855 prefixEnd_2472855 1269763203874027677140053 := by
  unfold tailWord_2472855
  simp only [CollatzResearch.WordTrace]
  refine ⟨90192431456276139855700019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60128287637517426570466679 90192431456276139855700019)
  ·
    refine ⟨135288647184414209783550029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90192431456276139855700019 135288647184414209783550029)
    ·
      refine ⟨50733242694155328668831261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135288647184414209783550029 50733242694155328668831261)
      ·
        refine ⟨19024966010308248250811723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50733242694155328668831261 19024966010308248250811723)
        ·
          refine ⟨28537449015462372376217585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19024966010308248250811723 28537449015462372376217585)
          ·
            refine ⟨21403086761596779282163189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28537449015462372376217585 21403086761596779282163189)
            ·
              refine ⟨2006539383899698057702799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21403086761596779282163189 2006539383899698057702799)
              ·
                refine ⟨3009809075849547086554199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006539383899698057702799 3009809075849547086554199)
                ·
                  refine ⟨4514713613774320629831299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009809075849547086554199 4514713613774320629831299)
                  ·
                    refine ⟨6772070420661480944746949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4514713613774320629831299 6772070420661480944746949)
                    ·
                      refine ⟨1269763203874027677140053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6772070420661480944746949 1269763203874027677140053)
                      ·
                        rfl

theorem cell23_2472855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_2472855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472855 prefixEnd_2472855 := by exact prefixLift 2472855
  have htrace : WordTrace (prefixWord ++ tailWord_2472855) baseStart_2472855 baseEnd_2472855 := by
    simpa [prefixWord, tailWord_2472855, baseEnd_2472855] using wordTrace_append hprefix tailTrace_2472855
  have hstable : (prefixWord ++ tailWord_2472855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472855).length < 2 ^ (prefixWord ++ tailWord_2472855).sum := by decide
  have hdescent : baseEnd_2472855 < baseStart_2472855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472865 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2472865 : Nat := 118140960795 + 2472865 * 2 ^ 59
def prefixEnd_2472865 : Nat := 4983230072969 + 3 ^ 40 * 2472865 * 2
def baseEnd_2472865 : Nat := 423256112893524212671669

theorem tailTrace_2472865 : CollatzResearch.WordTrace tailWord_2472865 prefixEnd_2472865 423256112893524212671669 := by
  unfold tailWord_2472865
  simp only [CollatzResearch.WordTrace]
  refine ⟨90192796186239911563564049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60128530790826607709042699 90192796186239911563564049)
  ·
    refine ⟨67644597139679933672673037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90192796186239911563564049 67644597139679933672673037)
    ·
      refine ⟨25366723927379975127252389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67644597139679933672673037 25366723927379975127252389)
      ·
        refine ⟨4756260736383745336359823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25366723927379975127252389 4756260736383745336359823)
        ·
          refine ⟨7134391104575618004539735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756260736383745336359823 7134391104575618004539735)
          ·
            refine ⟨10701586656863427006809603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134391104575618004539735 10701586656863427006809603)
            ·
              refine ⟨16052379985295140510214405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701586656863427006809603 16052379985295140510214405)
              ·
                refine ⟨3009821247242838845665201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16052379985295140510214405 3009821247242838845665201)
                ·
                  refine ⟨2257365935432129134248901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009821247242838845665201 2257365935432129134248901)
                  ·
                    refine ⟨423256112893524212671669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257365935432129134248901 423256112893524212671669)
                    ·
                      rfl

theorem cell23_2472865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2472865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472865 prefixEnd_2472865 := by exact prefixLift 2472865
  have htrace : WordTrace (prefixWord ++ tailWord_2472865) baseStart_2472865 baseEnd_2472865 := by
    simpa [prefixWord, tailWord_2472865, baseEnd_2472865] using wordTrace_append hprefix tailTrace_2472865
  have hstable : (prefixWord ++ tailWord_2472865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472865).length < 2 ^ (prefixWord ++ tailWord_2472865).sum := by decide
  have hdescent : baseEnd_2472865 < baseStart_2472865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472866 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_2472866 : Nat := 118140960795 + 2472866 * 2 ^ 59
def prefixEnd_2472866 : Nat := 4983230072969 + 3 ^ 40 * 2472866 * 2
def baseEnd_2472866 : Nat := 1269768852161227134102503

theorem tailTrace_2472866 : CollatzResearch.WordTrace tailWord_2472866 prefixEnd_2472866 1269768852161227134102503 := by
  unfold tailWord_2472866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548208164809072183587613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60128555106157525822900301 22548208164809072183587613)
  ·
    refine ⟨8455578061803402068845355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22548208164809072183587613 8455578061803402068845355)
    ·
      refine ⟨12683367092705103103268033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455578061803402068845355 12683367092705103103268033)
      ·
        refine ⟨9512525319528827327451025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12683367092705103103268033 9512525319528827327451025)
        ·
          refine ⟨7134393989646620495588269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9512525319528827327451025 7134393989646620495588269)
          ·
            refine ⟨2675397746117482685845601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7134393989646620495588269 2675397746117482685845601)
            ·
              refine ⟨2006548309588112014384201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675397746117482685845601 2006548309588112014384201)
              ·
                refine ⟨1504911232191084010788151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006548309588112014384201 1504911232191084010788151)
                ·
                  refine ⟨2257366848286626016182227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504911232191084010788151 2257366848286626016182227)
                  ·
                    refine ⟨3386050272429939024273341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257366848286626016182227 3386050272429939024273341)
                    ·
                      refine ⟨1269768852161227134102503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386050272429939024273341 1269768852161227134102503)
                      ·
                        rfl

theorem cell23_2472866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_2472866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472866 prefixEnd_2472866 := by exact prefixLift 2472866
  have htrace : WordTrace (prefixWord ++ tailWord_2472866) baseStart_2472866 baseEnd_2472866 := by
    simpa [prefixWord, tailWord_2472866, baseEnd_2472866] using wordTrace_append hprefix tailTrace_2472866
  have hstable : (prefixWord ++ tailWord_2472866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472866).length < 2 ^ (prefixWord ++ tailWord_2472866).sum := by decide
  have hdescent : baseEnd_2472866 < baseStart_2472866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472888 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2472888 : Nat := 118140960795 + 2472888 * 2 ^ 59
def prefixEnd_2472888 : Nat := 4983230072969 + 3 ^ 40 * 2472888 * 2
def baseEnd_2472888 : Nat := 1269780148735626048027401

theorem tailTrace_2472888 : CollatzResearch.WordTrace tailWord_2472888 prefixEnd_2472888 1269780148735626048027401 := by
  unfold tailWord_2472888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45096817532578293245825659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60129090043437724327767545 45096817532578293245825659)
  ·
    refine ⟨67645226298867439868738489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45096817532578293245825659 67645226298867439868738489)
    ·
      refine ⟨50733919724150579901553867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67645226298867439868738489 50733919724150579901553867)
      ·
        refine ⟨76100879586225869852330801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50733919724150579901553867 76100879586225869852330801)
        ·
          refine ⟨57075659689669402389248101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76100879586225869852330801 57075659689669402389248101)
          ·
            refine ⟨10701686191813012947984019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57075659689669402389248101 10701686191813012947984019)
            ·
              refine ⟨16052529287719519421976029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701686191813012947984019 16052529287719519421976029)
              ·
                refine ⟨6019698482894819783241011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16052529287719519421976029 6019698482894819783241011)
                ·
                  refine ⟨9029547724342229674861517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019698482894819783241011 9029547724342229674861517)
                  ·
                    refine ⟨3386080396628336128073069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9029547724342229674861517 3386080396628336128073069)
                    ·
                      refine ⟨1269780148735626048027401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386080396628336128073069 1269780148735626048027401)
                      ·
                        rfl

theorem cell23_2472888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2472888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472888 prefixEnd_2472888 := by exact prefixLift 2472888
  have htrace : WordTrace (prefixWord ++ tailWord_2472888) baseStart_2472888 baseEnd_2472888 := by
    simpa [prefixWord, tailWord_2472888, baseEnd_2472888] using wordTrace_append hprefix tailTrace_2472888
  have hstable : (prefixWord ++ tailWord_2472888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472888).length < 2 ^ (prefixWord ++ tailWord_2472888).sum := by decide
  have hdescent : baseEnd_2472888 < baseStart_2472888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472922 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2472922 : Nat := 118140960795 + 2472922 * 2 ^ 59
def prefixEnd_2472922 : Nat := 4983230072969 + 3 ^ 40 * 2472922 * 2
def baseEnd_2472922 : Nat := 1269797607077878915002245

theorem tailTrace_2472922 : CollatzResearch.WordTrace tailWord_2472922 prefixEnd_2472922 1269797607077878915002245 := by
  unfold tailWord_2472922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548718786758352574597255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60129916764688940198926013 22548718786758352574597255)
  ·
    refine ⟨33823078180137528861895883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22548718786758352574597255 33823078180137528861895883)
    ·
      refine ⟨50734617270206293292843825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33823078180137528861895883 50734617270206293292843825)
      ·
        refine ⟨38050962952654719969632869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50734617270206293292843825 38050962952654719969632869)
        ·
          refine ⟨7134555553622759994306163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38050962952654719969632869 7134555553622759994306163)
          ·
            refine ⟨10701833330434139991459245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134555553622759994306163 10701833330434139991459245)
            ·
              refine ⟨4013187498912802496797217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10701833330434139991459245 4013187498912802496797217)
              ·
                refine ⟨3009890624184601872597913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013187498912802496797217 3009890624184601872597913)
                ·
                  refine ⟨2257417968138451404448435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009890624184601872597913 2257417968138451404448435)
                  ·
                    refine ⟨3386126952207677106672653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257417968138451404448435 3386126952207677106672653)
                    ·
                      refine ⟨1269797607077878915002245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386126952207677106672653 1269797607077878915002245)
                      ·
                        rfl

theorem cell23_2472922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2472922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472922 prefixEnd_2472922 := by exact prefixLift 2472922
  have htrace : WordTrace (prefixWord ++ tailWord_2472922) baseStart_2472922 baseEnd_2472922 := by
    simpa [prefixWord, tailWord_2472922, baseEnd_2472922] using wordTrace_append hprefix tailTrace_2472922
  have hstable : (prefixWord ++ tailWord_2472922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472922).length < 2 ^ (prefixWord ++ tailWord_2472922).sum := by decide
  have hdescent : baseEnd_2472922 < baseStart_2472922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472928 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2]
def baseStart_2472928 : Nat := 118140960795 + 2472928 * 2 ^ 59
def prefixEnd_2472928 : Nat := 4983230072969 + 3 ^ 40 * 2472928 * 2
def baseEnd_2472928 : Nat := 1269800687961805891527217

theorem tailTrace_2472928 : CollatzResearch.WordTrace tailWord_2472928 prefixEnd_2472928 1269800687961805891527217 := by
  unfold tailWord_2472928
  simp only [CollatzResearch.WordTrace]
  refine ⟨45097546992505836661553719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60130062656674448882071625 45097546992505836661553719)
  ·
    refine ⟨67646320488758754992330579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45097546992505836661553719 67646320488758754992330579)
    ·
      refine ⟨101469480733138132488495869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67646320488758754992330579 101469480733138132488495869)
      ·
        refine ⟨38051055274926799683185951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101469480733138132488495869 38051055274926799683185951)
        ·
          refine ⟨57076582912390199524778927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38051055274926799683185951 57076582912390199524778927)
          ·
            refine ⟨85614874368585299287168391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57076582912390199524778927 85614874368585299287168391)
            ·
              refine ⟨128422311552877948930752587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85614874368585299287168391 128422311552877948930752587)
              ·
                refine ⟨192633467329316923396128881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128422311552877948930752587 192633467329316923396128881)
                ·
                  refine ⟨144475100496987692547096661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192633467329316923396128881 144475100496987692547096661)
                  ·
                    refine ⟨1693067583949074522036289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 144475100496987692547096661 1693067583949074522036289)
                    ·
                      refine ⟨1269800687961805891527217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693067583949074522036289 1269800687961805891527217)
                      ·
                        rfl

theorem cell23_2472928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_2472928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472928 prefixEnd_2472928 := by exact prefixLift 2472928
  have htrace : WordTrace (prefixWord ++ tailWord_2472928) baseStart_2472928 baseEnd_2472928 := by
    simpa [prefixWord, tailWord_2472928, baseEnd_2472928] using wordTrace_append hprefix tailTrace_2472928
  have hstable : (prefixWord ++ tailWord_2472928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472928).length < 2 ^ (prefixWord ++ tailWord_2472928).sum := by decide
  have hdescent : baseEnd_2472928 < baseStart_2472928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472938 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2472938 : Nat := 118140960795 + 2472938 * 2 ^ 59
def prefixEnd_2472938 : Nat := 4983230072969 + 3 ^ 40 * 2472938 * 2
def baseEnd_2472938 : Nat := 423268607589450284134057

theorem tailTrace_2472938 : CollatzResearch.WordTrace tailWord_2472938 prefixEnd_2472938 423268607589450284134057 := by
  unfold tailWord_2472938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548864678743861257742867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60130305809983630020647645 22548864678743861257742867)
  ·
    refine ⟨33823297018115791886614301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22548864678743861257742867 33823297018115791886614301)
    ·
      refine ⟨12683736381793421957480363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33823297018115791886614301 12683736381793421957480363)
      ·
        refine ⟨19025604572690132936220545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683736381793421957480363 19025604572690132936220545)
        ·
          refine ⟨14269203429517599702165409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19025604572690132936220545 14269203429517599702165409)
          ·
            refine ⟨10701902572138199776624057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14269203429517599702165409 10701902572138199776624057)
            ·
              refine ⟨8026426929103649832468043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10701902572138199776624057 8026426929103649832468043)
              ·
                refine ⟨12039640393655474748702065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026426929103649832468043 12039640393655474748702065)
                ·
                  refine ⟨9029730295241606061526549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12039640393655474748702065 9029730295241606061526549)
                  ·
                    refine ⟨423268607589450284134057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9029730295241606061526549 423268607589450284134057)
                    ·
                      rfl

theorem cell23_2472938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2472938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472938 prefixEnd_2472938 := by exact prefixLift 2472938
  have htrace : WordTrace (prefixWord ++ tailWord_2472938) baseStart_2472938 baseEnd_2472938 := by
    simpa [prefixWord, tailWord_2472938, baseEnd_2472938] using wordTrace_append hprefix tailTrace_2472938
  have hstable : (prefixWord ++ tailWord_2472938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472938).length < 2 ^ (prefixWord ++ tailWord_2472938).sum := by decide
  have hdescent : baseEnd_2472938 < baseStart_2472938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472996 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2472996 : Nat := 118140960795 + 2472996 * 2 ^ 59
def prefixEnd_2472996 : Nat := 4983230072969 + 3 ^ 40 * 2472996 * 2
def baseEnd_2472996 : Nat := 1269835604646311625476905

theorem tailTrace_2472996 : CollatzResearch.WordTrace tailWord_2472996 prefixEnd_2472996 1269835604646311625476905 := by
  unfold tailWord_2472996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45098787074382660468291421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60131716099176880624388561 45098787074382660468291421)
  ·
    refine ⟨16912045152893497675609283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45098787074382660468291421 16912045152893497675609283)
    ·
      refine ⟨25368067729340246513413925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16912045152893497675609283 25368067729340246513413925)
      ·
        refine ⟨4756512699251296221265111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25368067729340246513413925 4756512699251296221265111)
        ·
          refine ⟨7134769048876944331897667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756512699251296221265111 7134769048876944331897667)
          ·
            refine ⟨10702153573315416497846501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134769048876944331897667 10702153573315416497846501)
            ·
              refine ⟨2006653794996640593346219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10702153573315416497846501 2006653794996640593346219)
              ·
                refine ⟨3009980692494960890019329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006653794996640593346219 3009980692494960890019329)
                ·
                  refine ⟨2257485519371220667514497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009980692494960890019329 2257485519371220667514497)
                  ·
                    refine ⟨1693114139528415500635873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2257485519371220667514497 1693114139528415500635873)
                    ·
                      refine ⟨1269835604646311625476905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693114139528415500635873 1269835604646311625476905)
                      ·
                        rfl

theorem cell23_2472996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2472996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2472996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2472996 prefixEnd_2472996 := by exact prefixLift 2472996
  have htrace : WordTrace (prefixWord ++ tailWord_2472996) baseStart_2472996 baseEnd_2472996 := by
    simpa [prefixWord, tailWord_2472996, baseEnd_2472996] using wordTrace_append hprefix tailTrace_2472996
  have hstable : (prefixWord ++ tailWord_2472996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472996).length < 2 ^ (prefixWord ++ tailWord_2472996).sum := by decide
  have hdescent : baseEnd_2472996 < baseStart_2472996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473018 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_2473018 : Nat := 118140960795 + 2473018 * 2 ^ 59
def prefixEnd_2473018 : Nat := 4983230072969 + 3 ^ 40 * 2473018 * 2
def baseEnd_2473018 : Nat := 1269846901220710539401803

theorem tailTrace_2473018 : CollatzResearch.WordTrace tailWord_2473018 prefixEnd_2473018 1269846901220710539401803 := by
  unfold tailWord_2473018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549594138671404673470927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60132251036457079129255805 22549594138671404673470927)
  ·
    refine ⟨33824391208007107010206391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22549594138671404673470927 33824391208007107010206391)
    ·
      refine ⟨50736586812010660515309587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33824391208007107010206391 50736586812010660515309587)
      ·
        refine ⟨76104880218015990772964381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50736586812010660515309587 76104880218015990772964381)
        ·
          refine ⟨28539330081755996539861643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76104880218015990772964381 28539330081755996539861643)
          ·
            refine ⟨42808995122633994809792465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28539330081755996539861643 42808995122633994809792465)
            ·
              refine ⟨32106746341975496107344349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42808995122633994809792465 32106746341975496107344349)
              ·
                refine ⟨12040029878240811040254131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32106746341975496107344349 12040029878240811040254131)
                ·
                  refine ⟨18060044817361216560381197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040029878240811040254131 18060044817361216560381197)
                  ·
                    refine ⟨6772516806510456210142949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18060044817361216560381197 6772516806510456210142949)
                    ·
                      refine ⟨1269846901220710539401803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6772516806510456210142949 1269846901220710539401803)
                      ·
                        rfl

theorem cell23_2473018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_2473018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473018 prefixEnd_2473018 := by exact prefixLift 2473018
  have htrace : WordTrace (prefixWord ++ tailWord_2473018) baseStart_2473018 baseEnd_2473018 := by
    simpa [prefixWord, tailWord_2473018, baseEnd_2473018] using wordTrace_append hprefix tailTrace_2473018
  have hstable : (prefixWord ++ tailWord_2473018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473018).length < 2 ^ (prefixWord ++ tailWord_2473018).sum := by decide
  have hdescent : baseEnd_2473018 < baseStart_2473018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473038 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2473038 : Nat := 118140960795 + 2473038 * 2 ^ 59
def prefixEnd_2473038 : Nat := 4983230072969 + 3 ^ 40 * 2473038 * 2
def baseEnd_2473038 : Nat := 1269857170833800461151711

theorem tailTrace_2473038 : CollatzResearch.WordTrace tailWord_2473038 prefixEnd_2473038 1269857170833800461151711 := by
  unfold tailWord_2473038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274888251826645263701471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60132737343075441406407845 11274888251826645263701471)
  ·
    refine ⟨16912332377739967895552207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11274888251826645263701471 16912332377739967895552207)
    ·
      refine ⟨25368498566609951843328311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16912332377739967895552207 25368498566609951843328311)
      ·
        refine ⟨38052747849914927764992467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25368498566609951843328311 38052747849914927764992467)
        ·
          refine ⟨57079121774872391647488701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38052747849914927764992467 57079121774872391647488701)
          ·
            refine ⟨21404670665577146867808263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57079121774872391647488701 21404670665577146867808263)
            ·
              refine ⟨32107005998365720301712395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21404670665577146867808263 32107005998365720301712395)
              ·
                refine ⟨48160508997548580452568593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32107005998365720301712395 48160508997548580452568593)
                ·
                  refine ⟨36120381748161435339426445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48160508997548580452568593 36120381748161435339426445)
                  ·
                    refine ⟨13545143155560538252284917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36120381748161435339426445 13545143155560538252284917)
                    ·
                      refine ⟨1269857170833800461151711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13545143155560538252284917 1269857170833800461151711)
                      ·
                        rfl

theorem cell23_2473038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2473038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473038 prefixEnd_2473038 := by exact prefixLift 2473038
  have htrace : WordTrace (prefixWord ++ tailWord_2473038) baseStart_2473038 baseEnd_2473038 := by
    simpa [prefixWord, tailWord_2473038, baseEnd_2473038] using wordTrace_append hprefix tailTrace_2473038
  have hstable : (prefixWord ++ tailWord_2473038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473038).length < 2 ^ (prefixWord ++ tailWord_2473038).sum := by decide
  have hdescent : baseEnd_2473038 < baseStart_2473038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473045 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2473045 : Nat := 118140960795 + 2473045 * 2 ^ 59
def prefixEnd_2473045 : Nat := 4983230072969 + 3 ^ 40 * 2473045 * 2
def baseEnd_2473045 : Nat := 423286921732793977921393

theorem tailTrace_2473045 : CollatzResearch.WordTrace tailWord_2473045 prefixEnd_2473045 423286921732793977921393 := by
  unfold tailWord_2473045
  simp only [CollatzResearch.WordTrace]
  refine ⟨90199361325587802305116589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60132907550391868203411059 90199361325587802305116589)
  ·
    refine ⟨33824760497095425864418721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90199361325587802305116589 33824760497095425864418721)
    ·
      refine ⟨25368570372821569398314041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33824760497095425864418721 25368570372821569398314041)
      ·
        refine ⟨19026427779616177048735531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25368570372821569398314041 19026427779616177048735531)
        ·
          refine ⟨28539641669424265573103297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19026427779616177048735531 28539641669424265573103297)
          ·
            refine ⟨21404731252068199179827473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28539641669424265573103297 21404731252068199179827473)
            ·
              refine ⟨16053548439051149384870605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21404731252068199179827473 16053548439051149384870605)
              ·
                refine ⟨6020080664644181019326477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16053548439051149384870605 6020080664644181019326477)
                ·
                  refine ⟨2257530249241567882247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6020080664644181019326477 2257530249241567882247429)
                  ·
                    refine ⟨423286921732793977921393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257530249241567882247429 423286921732793977921393)
                    ·
                      rfl

theorem cell23_2473045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2473045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473045 prefixEnd_2473045 := by exact prefixLift 2473045
  have htrace : WordTrace (prefixWord ++ tailWord_2473045) baseStart_2473045 baseEnd_2473045 := by
    simpa [prefixWord, tailWord_2473045, baseEnd_2473045] using wordTrace_append hprefix tailTrace_2473045
  have hstable : (prefixWord ++ tailWord_2473045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473045).length < 2 ^ (prefixWord ++ tailWord_2473045).sum := by decide
  have hdescent : baseEnd_2473045 < baseStart_2473045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473052 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2473052 : Nat := 118140960795 + 2473052 * 2 ^ 59
def prefixEnd_2473052 : Nat := 4983230072969 + 3 ^ 40 * 2473052 * 2
def baseEnd_2473052 : Nat := 1269864359562963406376647

theorem tailTrace_2473052 : CollatzResearch.WordTrace tailWord_2473052 prefixEnd_2473052 1269864359562963406376647 := by
  unfold tailWord_2473052
  simp only [CollatzResearch.WordTrace]
  refine ⟨45099808318281221250310705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60133077757708295000414273 45099808318281221250310705)
  ·
    refine ⟨33824856238710915937733029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45099808318281221250310705 33824856238710915937733029)
    ·
      refine ⟨6342160544758296738324943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33824856238710915937733029 6342160544758296738324943)
      ·
        refine ⟨9513240817137445107487415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342160544758296738324943 9513240817137445107487415)
        ·
          refine ⟨14269861225706167661231123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513240817137445107487415 14269861225706167661231123)
          ·
            refine ⟨21404791838559251491846685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14269861225706167661231123 21404791838559251491846685)
            ·
              refine ⟨8026796939459719309442507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21404791838559251491846685 8026796939459719309442507)
              ·
                refine ⟨12040195409189578964163761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026796939459719309442507 12040195409189578964163761)
                ·
                  refine ⟨9030146556892184223122821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12040195409189578964163761 9030146556892184223122821)
                  ·
                    refine ⟨1693152479417284541835529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9030146556892184223122821 1693152479417284541835529)
                    ·
                      refine ⟨1269864359562963406376647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693152479417284541835529 1269864359562963406376647)
                      ·
                        rfl

theorem cell23_2473052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2473052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473052 prefixEnd_2473052 := by exact prefixLift 2473052
  have htrace : WordTrace (prefixWord ++ tailWord_2473052) baseStart_2473052 baseEnd_2473052 := by
    simpa [prefixWord, tailWord_2473052, baseEnd_2473052] using wordTrace_append hprefix tailTrace_2473052
  have hstable : (prefixWord ++ tailWord_2473052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473052).length < 2 ^ (prefixWord ++ tailWord_2473052).sum := by decide
  have hdescent : baseEnd_2473052 < baseStart_2473052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473092 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 6]
def baseStart_2473092 : Nat := 118140960795 + 2473092 * 2 ^ 59
def prefixEnd_2473092 : Nat := 4983230072969 + 3 ^ 40 * 2473092 * 2
def baseEnd_2473092 : Nat := 141098322087682583319607

theorem tailTrace_2473092 : CollatzResearch.WordTrace tailWord_2473092 prefixEnd_2473092 141098322087682583319607 := by
  unfold tailWord_2473092
  simp only [CollatzResearch.WordTrace]
  refine ⟨45100537778208764666038765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60134050370945019554718353 45100537778208764666038765)
  ·
    refine ⟨16912701666828286749764537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45100537778208764666038765 16912701666828286749764537)
    ·
      refine ⟨12684526250121215062323403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16912701666828286749764537 12684526250121215062323403)
      ·
        refine ⟨19026789375181822593485105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12684526250121215062323403 19026789375181822593485105)
        ·
          refine ⟨14270092031386366945113829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19026789375181822593485105 14270092031386366945113829)
          ·
            refine ⟨2675642255884943802208843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14270092031386366945113829 2675642255884943802208843)
            ·
              refine ⟨4013463383827415703313265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675642255884943802208843 4013463383827415703313265)
              ·
                refine ⟨3010097537870561777484949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013463383827415703313265 3010097537870561777484949)
                ·
                  refine ⟨141098322087682583319607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3010097537870561777484949 141098322087682583319607)
                  ·
                    rfl

theorem cell23_2473092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_2473092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473092 prefixEnd_2473092 := by exact prefixLift 2473092
  have htrace : WordTrace (prefixWord ++ tailWord_2473092) baseStart_2473092 baseEnd_2473092 := by
    simpa [prefixWord, tailWord_2473092, baseEnd_2473092] using wordTrace_append hprefix tailTrace_2473092
  have hstable : (prefixWord ++ tailWord_2473092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473092).length < 2 ^ (prefixWord ++ tailWord_2473092).sum := by decide
  have hdescent : baseEnd_2473092 < baseStart_2473092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473112 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2473112 : Nat := 118140960795 + 2473112 * 2 ^ 59
def prefixEnd_2473112 : Nat := 4983230072969 + 3 ^ 40 * 2473112 * 2
def baseEnd_2473112 : Nat := 1269895168402233171626371

theorem tailTrace_2473112 : CollatzResearch.WordTrace tailWord_2473112 prefixEnd_2473112 1269895168402233171626371 := by
  unfold tailWord_2473112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45100902508172536373902795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60134536677563381831870393 45100902508172536373902795)
  ·
    refine ⟨67651353762258804560854193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45100902508172536373902795 67651353762258804560854193)
    ·
      refine ⟨50738515321694103420640645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67651353762258804560854193 50738515321694103420640645)
      ·
        refine ⟨9513471622817644391370121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50738515321694103420640645 9513471622817644391370121)
        ·
          refine ⟨7135103717113233293527591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9513471622817644391370121 7135103717113233293527591)
          ·
            refine ⟨10702655575669849940291387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7135103717113233293527591 10702655575669849940291387)
            ·
              refine ⟨16053983363504774910437081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10702655575669849940291387 16053983363504774910437081)
              ·
                refine ⟨12040487522628581182827811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16053983363504774910437081 12040487522628581182827811)
                ·
                  refine ⟨18060731283942871774241717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040487522628581182827811 18060731283942871774241717)
                  ·
                    refine ⟨1693193557869644228835161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18060731283942871774241717 1693193557869644228835161)
                    ·
                      refine ⟨1269895168402233171626371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693193557869644228835161 1269895168402233171626371)
                      ·
                        rfl

theorem cell23_2473112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2473112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473112 prefixEnd_2473112 := by exact prefixLift 2473112
  have htrace : WordTrace (prefixWord ++ tailWord_2473112) baseStart_2473112 baseEnd_2473112 := by
    simpa [prefixWord, tailWord_2473112, baseEnd_2473112] using wordTrace_append hprefix tailTrace_2473112
  have hstable : (prefixWord ++ tailWord_2473112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473112).length < 2 ^ (prefixWord ++ tailWord_2473112).sum := by decide
  have hdescent : baseEnd_2473112 < baseStart_2473112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473135 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 4, 4]
def baseStart_2473135 : Nat := 118140960795 + 2473135 * 2 ^ 59
def prefixEnd_2473135 : Nat := 4983230072969 + 3 ^ 40 * 2473135 * 2
def baseEnd_2473135 : Nat := 423302326152428860546255

theorem tailTrace_2473135 : CollatzResearch.WordTrace tailWord_2473135 prefixEnd_2473135 423302326152428860546255 := by
  unfold tailWord_2473135
  simp only [CollatzResearch.WordTrace]
  refine ⟨90202643895261747675892859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60135095930174498450595239 90202643895261747675892859)
  ·
    refine ⟨135303965842892621513839289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90202643895261747675892859 135303965842892621513839289)
    ·
      refine ⟨101477974382169466135379467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135303965842892621513839289 101477974382169466135379467)
      ·
        refine ⟨152216961573254199203069201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101477974382169466135379467 152216961573254199203069201)
        ·
          refine ⟨114162721179940649402301901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152216961573254199203069201 114162721179940649402301901)
          ·
            refine ⟨42811020442477743525863213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114162721179940649402301901 42811020442477743525863213)
            ·
              refine ⟨16054132665929153822198705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42811020442477743525863213 16054132665929153822198705)
              ·
                refine ⟨12040599499446865366649029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16054132665929153822198705 12040599499446865366649029)
                ·
                  refine ⟨2257612406146287256246693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12040599499446865366649029 2257612406146287256246693)
                  ·
                    refine ⟨423302326152428860546255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257612406146287256246693 423302326152428860546255)
                    ·
                      rfl

theorem cell23_2473135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_2473135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473135 prefixEnd_2473135 := by exact prefixLift 2473135
  have htrace : WordTrace (prefixWord ++ tailWord_2473135) baseStart_2473135 baseEnd_2473135 := by
    simpa [prefixWord, tailWord_2473135, baseEnd_2473135] using wordTrace_append hprefix tailTrace_2473135
  have hstable : (prefixWord ++ tailWord_2473135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473135).length < 2 ^ (prefixWord ++ tailWord_2473135).sum := by decide
  have hdescent : baseEnd_2473135 < baseStart_2473135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473145 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2473145 : Nat := 118140960795 + 2473145 * 2 ^ 59
def prefixEnd_2473145 : Nat := 4983230072969 + 3 ^ 40 * 2473145 * 2
def baseEnd_2473145 : Nat := 1269912113263831542513719

theorem tailTrace_2473145 : CollatzResearch.WordTrace tailWord_2473145 prefixEnd_2473145 1269912113263831542513719 := by
  unfold tailWord_2473145
  simp only [CollatzResearch.WordTrace]
  refine ⟨90203008625225519383756889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60135339083483679589171259 90203008625225519383756889)
  ·
    refine ⟨67652256468919139537817667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90203008625225519383756889 67652256468919139537817667)
    ·
      refine ⟨101478384703378709306726501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67652256468919139537817667 101478384703378709306726501)
      ·
        refine ⟨19027197131883507995011219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101478384703378709306726501 19027197131883507995011219)
        ·
          refine ⟨28540795697825261992516829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19027197131883507995011219 28540795697825261992516829)
          ·
            refine ⟨10702798386684473247193811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28540795697825261992516829 10702798386684473247193811)
            ·
              refine ⟨16054197580026709870790717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10702798386684473247193811 16054197580026709870790717)
              ·
                refine ⟨6020324092510016201546519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16054197580026709870790717 6020324092510016201546519)
                ·
                  refine ⟨9030486138765024302319779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020324092510016201546519 9030486138765024302319779)
                  ·
                    refine ⟨13545729208147536453479669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9030486138765024302319779 13545729208147536453479669)
                    ·
                      refine ⟨1269912113263831542513719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13545729208147536453479669 1269912113263831542513719)
                      ·
                        rfl

theorem cell23_2473145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2473145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473145 prefixEnd_2473145 := by exact prefixLift 2473145
  have htrace : WordTrace (prefixWord ++ tailWord_2473145) baseStart_2473145 baseEnd_2473145 := by
    simpa [prefixWord, tailWord_2473145, baseEnd_2473145] using wordTrace_append hprefix tailTrace_2473145
  have hstable : (prefixWord ++ tailWord_2473145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473145).length < 2 ^ (prefixWord ++ tailWord_2473145).sum := by decide
  have hdescent : baseEnd_2473145 < baseStart_2473145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473176 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_2473176 : Nat := 118140960795 + 2473176 * 2 ^ 59
def prefixEnd_2473176 : Nat := 4983230072969 + 3 ^ 40 * 2473176 * 2
def baseEnd_2473176 : Nat := 1269928031164120921226077

theorem tailTrace_2473176 : CollatzResearch.WordTrace tailWord_2473176 prefixEnd_2473176 1269928031164120921226077 := by
  unfold tailWord_2473176
  simp only [CollatzResearch.WordTrace]
  refine ⟨45102069644056605839067691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60136092858742141118756921 45102069644056605839067691)
  ·
    refine ⟨67653104466084908758601537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45102069644056605839067691 67653104466084908758601537)
    ·
      refine ⟨50739828349563681568951153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67653104466084908758601537 50739828349563681568951153)
      ·
        refine ⟨38054871262172761176713365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50739828349563681568951153 38054871262172761176713365)
        ·
          refine ⟨1783822090414348180158439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38054871262172761176713365 1783822090414348180158439)
          ·
            refine ⟨2675733135621522270237659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783822090414348180158439 2675733135621522270237659)
            ·
              refine ⟨4013599703432283405356489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675733135621522270237659 4013599703432283405356489)
              ·
                refine ⟨3010199777574212554017367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013599703432283405356489 3010199777574212554017367)
                ·
                  refine ⟨4515299666361318831026051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010199777574212554017367 4515299666361318831026051)
                  ·
                    refine ⟨6772949499541978246539077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4515299666361318831026051 6772949499541978246539077)
                    ·
                      refine ⟨1269928031164120921226077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6772949499541978246539077 1269928031164120921226077)
                      ·
                        rfl

theorem cell23_2473176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_2473176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473176 prefixEnd_2473176 := by exact prefixLift 2473176
  have htrace : WordTrace (prefixWord ++ tailWord_2473176) baseStart_2473176 baseEnd_2473176 := by
    simpa [prefixWord, tailWord_2473176, baseEnd_2473176] using wordTrace_append hprefix tailTrace_2473176
  have hstable : (prefixWord ++ tailWord_2473176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473176).length < 2 ^ (prefixWord ++ tailWord_2473176).sum := by decide
  have hdescent : baseEnd_2473176 < baseStart_2473176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473192 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2473192 : Nat := 118140960795 + 2473192 * 2 ^ 59
def prefixEnd_2473192 : Nat := 4983230072969 + 3 ^ 40 * 2473192 * 2
def baseEnd_2473192 : Nat := 1269936246854592858626003

theorem tailTrace_2473192 : CollatzResearch.WordTrace tailWord_2473192 prefixEnd_2473192 1269936246854592858626003 := by
  unfold tailWord_2473192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45102361428027623205358915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60136481904036830940478553 45102361428027623205358915)
  ·
    refine ⟨67653542142041434808038373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45102361428027623205358915 67653542142041434808038373)
    ·
      refine ⟨12685039151632769026507195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67653542142041434808038373 12685039151632769026507195)
      ·
        refine ⟨19027558727449153539760793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12685039151632769026507195 19027558727449153539760793)
        ·
          refine ⟨14270669045586865154820595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19027558727449153539760793 14270669045586865154820595)
          ·
            refine ⟨21406003568380297732230893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270669045586865154820595 21406003568380297732230893)
            ·
              refine ⟨8027251338142611649586585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21406003568380297732230893 8027251338142611649586585)
              ·
                refine ⟨6020438503606958737189939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027251338142611649586585 6020438503606958737189939)
                ·
                  refine ⟨9030657755410438105784909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6020438503606958737189939 9030657755410438105784909)
                  ·
                    refine ⟨3386496658278914289669341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9030657755410438105784909 3386496658278914289669341)
                    ·
                      refine ⟨1269936246854592858626003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386496658278914289669341 1269936246854592858626003)
                      ·
                        rfl

theorem cell23_2473192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2473192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473192 prefixEnd_2473192 := by exact prefixLift 2473192
  have htrace : WordTrace (prefixWord ++ tailWord_2473192) baseStart_2473192 baseEnd_2473192 := by
    simpa [prefixWord, tailWord_2473192, baseEnd_2473192] using wordTrace_append hprefix tailTrace_2473192
  have hstable : (prefixWord ++ tailWord_2473192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473192).length < 2 ^ (prefixWord ++ tailWord_2473192).sum := by decide
  have hdescent : baseEnd_2473192 < baseStart_2473192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473204 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2473204 : Nat := 118140960795 + 2473204 * 2 ^ 59
def prefixEnd_2473204 : Nat := 4983230072969 + 3 ^ 40 * 2473204 * 2
def baseEnd_2473204 : Nat := 1269942408622446811675949

theorem tailTrace_2473204 : CollatzResearch.WordTrace tailWord_2473204 prefixEnd_2473204 1269942408622446811675949 := by
  unfold tailWord_2473204
  simp only [CollatzResearch.WordTrace]
  refine ⟨45102580266005886230077333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60136773688007848306769777 45102580266005886230077333)
  ·
    refine ⟨2114183449969025917034875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45102580266005886230077333 2114183449969025917034875)
    ·
      refine ⟨3171275174953538875552313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114183449969025917034875 3171275174953538875552313)
      ·
        refine ⟨2378456381215154156664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3171275174953538875552313 2378456381215154156664235)
        ·
          refine ⟨3567684571822731234996353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378456381215154156664235 3567684571822731234996353)
          ·
            refine ⟨2675763428867048426247265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3567684571822731234996353 2675763428867048426247265)
            ·
              refine ⟨2006822571650286319685449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675763428867048426247265 2006822571650286319685449)
              ·
                refine ⟨1505116928737714739764087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006822571650286319685449 1505116928737714739764087)
                ·
                  refine ⟨2257675393106572109646131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505116928737714739764087 2257675393106572109646131)
                  ·
                    refine ⟨3386513089659858164469197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257675393106572109646131 3386513089659858164469197)
                    ·
                      refine ⟨1269942408622446811675949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386513089659858164469197 1269942408622446811675949)
                      ·
                        rfl

theorem cell23_2473204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2473204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473204 prefixEnd_2473204 := by exact prefixLift 2473204
  have htrace : WordTrace (prefixWord ++ tailWord_2473204) baseStart_2473204 baseEnd_2473204 := by
    simpa [prefixWord, tailWord_2473204, baseEnd_2473204] using wordTrace_append hprefix tailTrace_2473204
  have hstable : (prefixWord ++ tailWord_2473204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473204).length < 2 ^ (prefixWord ++ tailWord_2473204).sum := by decide
  have hdescent : baseEnd_2473204 < baseStart_2473204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473209 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2473209 : Nat := 118140960795 + 2473209 * 2 ^ 59
def prefixEnd_2473209 : Nat := 4983230072969 + 3 ^ 40 * 2473209 * 2
def baseEnd_2473209 : Nat := 1269944976025719292113425

theorem tailTrace_2473209 : CollatzResearch.WordTrace tailWord_2473209 prefixEnd_2473209 1269944976025719292113425 := by
  unfold tailWord_2473209
  simp only [CollatzResearch.WordTrace]
  refine ⟨90205342896993658314086681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60136895264662438876057787 90205342896993658314086681)
  ·
    refine ⟨67654007172745243735565011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90205342896993658314086681 67654007172745243735565011)
    ·
      refine ⟨101481010759117865603347517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67654007172745243735565011 101481010759117865603347517)
      ·
        refine ⟨38055379034669199601255319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101481010759117865603347517 38055379034669199601255319)
        ·
          refine ⟨57083068552003799401882979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38055379034669199601255319 57083068552003799401882979)
          ·
            refine ⟨85624602828005699102824469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57083068552003799401882979 85624602828005699102824469)
            ·
              refine ⟨4013653257562767145444897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85624602828005699102824469 4013653257562767145444897)
              ·
                refine ⟨3010239943172075359083673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013653257562767145444897 3010239943172075359083673)
                ·
                  refine ⟨2257679957379056519312755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010239943172075359083673 2257679957379056519312755)
                  ·
                    refine ⟨3386519936068584778969133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2257679957379056519312755 3386519936068584778969133)
                    ·
                      refine ⟨1269944976025719292113425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386519936068584778969133 1269944976025719292113425)
                      ·
                        rfl

theorem cell23_2473209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2473209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473209 prefixEnd_2473209 := by exact prefixLift 2473209
  have htrace : WordTrace (prefixWord ++ tailWord_2473209) baseStart_2473209 baseEnd_2473209 := by
    simpa [prefixWord, tailWord_2473209, baseEnd_2473209] using wordTrace_append hprefix tailTrace_2473209
  have hstable : (prefixWord ++ tailWord_2473209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473209).length < 2 ^ (prefixWord ++ tailWord_2473209).sum := by decide
  have hdescent : baseEnd_2473209 < baseStart_2473209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473215 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2473215 : Nat := 118140960795 + 2473215 * 2 ^ 59
def prefixEnd_2473215 : Nat := 4983230072969 + 3 ^ 40 * 2473215 * 2
def baseEnd_2473215 : Nat := 1269948056909646268638397

theorem tailTrace_2473215 : CollatzResearch.WordTrace tailWord_2473215 prefixEnd_2473215 1269948056909646268638397 := by
  unfold tailWord_2473215
  simp only [CollatzResearch.WordTrace]
  refine ⟨90205561734971921338805099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60137041156647947559203399 90205561734971921338805099)
  ·
    refine ⟨135308342602457882008207649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90205561734971921338805099 135308342602457882008207649)
    ·
      refine ⟨101481256951843411506155737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135308342602457882008207649 101481256951843411506155737)
      ·
        refine ⟨76110942713882558629616803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101481256951843411506155737 76110942713882558629616803)
        ·
          refine ⟨114166414070823837944425205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76110942713882558629616803 114166414070823837944425205)
          ·
            refine ⟨10703101319139734807289863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114166414070823837944425205 10703101319139734807289863)
            ·
              refine ⟨16054651978709602210934795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10703101319139734807289863 16054651978709602210934795)
              ·
                refine ⟨24081977968064403316402193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16054651978709602210934795 24081977968064403316402193)
                ·
                  refine ⟨18061483476048302487301645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24081977968064403316402193 18061483476048302487301645)
                  ·
                    refine ⟨6773056303518113432738117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18061483476048302487301645 6773056303518113432738117)
                    ·
                      refine ⟨1269948056909646268638397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6773056303518113432738117 1269948056909646268638397)
                      ·
                        rfl

theorem cell23_2473215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2473215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473215 prefixEnd_2473215 := by exact prefixLift 2473215
  have htrace : WordTrace (prefixWord ++ tailWord_2473215) baseStart_2473215 baseEnd_2473215 := by
    simpa [prefixWord, tailWord_2473215, baseEnd_2473215] using wordTrace_append hprefix tailTrace_2473215
  have hstable : (prefixWord ++ tailWord_2473215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473215).length < 2 ^ (prefixWord ++ tailWord_2473215).sum := by decide
  have hdescent : baseEnd_2473215 < baseStart_2473215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473225 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_2473225 : Nat := 118140960795 + 2473225 * 2 ^ 59
def prefixEnd_2473225 : Nat := 4983230072969 + 3 ^ 40 * 2473225 * 2
def baseEnd_2473225 : Nat := 423317730572063743171117

theorem tailTrace_2473225 : CollatzResearch.WordTrace tailWord_2473225 prefixEnd_2473225 423317730572063743171117 := by
  unfold tailWord_2473225
  simp only [CollatzResearch.WordTrace]
  refine ⟨90205926464935693046669129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60137284309957128697779419 90205926464935693046669129)
  ·
    refine ⟨67654444848701769785001847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90205926464935693046669129 67654444848701769785001847)
    ·
      refine ⟨101481667273052654677502771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67654444848701769785001847 101481667273052654677502771)
      ·
        refine ⟨152222500909578982016254157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101481667273052654677502771 152222500909578982016254157)
        ·
          refine ⟨57083437841092118256095309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152222500909578982016254157 57083437841092118256095309)
          ·
            refine ⟨21406289190409544346035741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57083437841092118256095309 21406289190409544346035741)
            ·
              refine ⟨8027358446403579129763403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21406289190409544346035741 8027358446403579129763403)
              ·
                refine ⟨12041037669605368694645105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027358446403579129763403 12041037669605368694645105)
                ·
                  refine ⟨9030778252204026520983829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12041037669605368694645105 9030778252204026520983829)
                  ·
                    refine ⟨423317730572063743171117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9030778252204026520983829 423317730572063743171117)
                    ·
                      rfl

theorem cell23_2473225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_2473225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473225 prefixEnd_2473225 := by exact prefixLift 2473225
  have htrace : WordTrace (prefixWord ++ tailWord_2473225) baseStart_2473225 baseEnd_2473225 := by
    simpa [prefixWord, tailWord_2473225, baseEnd_2473225] using wordTrace_append hprefix tailTrace_2473225
  have hstable : (prefixWord ++ tailWord_2473225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473225).length < 2 ^ (prefixWord ++ tailWord_2473225).sum := by decide
  have hdescent : baseEnd_2473225 < baseStart_2473225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473249 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2473249 : Nat := 118140960795 + 2473249 * 2 ^ 59
def prefixEnd_2473249 : Nat := 4983230072969 + 3 ^ 40 * 2473249 * 2
def baseEnd_2473249 : Nat := 1269965515251899135613241

theorem tailTrace_2473249 : CollatzResearch.WordTrace tailWord_2473249 prefixEnd_2473249 1269965515251899135613241 := by
  unfold tailWord_2473249
  simp only [CollatzResearch.WordTrace]
  refine ⟨90206801816848745145542801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60137867877899163430361867 90206801816848745145542801)
  ·
    refine ⟨67655101362636558859157101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90206801816848745145542801 67655101362636558859157101)
    ·
      refine ⟨25370663010988709572183913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67655101362636558859157101 25370663010988709572183913)
      ·
        refine ⟨19027997258241532179137935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25370663010988709572183913 19027997258241532179137935)
        ·
          refine ⟨28541995887362298268706903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19027997258241532179137935 28541995887362298268706903)
          ·
            refine ⟨42812993831043447403060355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28541995887362298268706903 42812993831043447403060355)
            ·
              refine ⟨64219490746565171104590533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42812993831043447403060355 64219490746565171104590533)
              ·
                refine ⟨12041154514980969582110725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64219490746565171104590533 12041154514980969582110725)
                ·
                  refine ⟨2257716471558931796645761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12041154514980969582110725 2257716471558931796645761)
                  ·
                    refine ⟨1693287353669198847484321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2257716471558931796645761 1693287353669198847484321)
                    ·
                      refine ⟨1269965515251899135613241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693287353669198847484321 1269965515251899135613241)
                      ·
                        rfl

theorem cell23_2473249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2473249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473249 prefixEnd_2473249 := by exact prefixLift 2473249
  have htrace : WordTrace (prefixWord ++ tailWord_2473249) baseStart_2473249 baseEnd_2473249 := by
    simpa [prefixWord, tailWord_2473249, baseEnd_2473249] using wordTrace_append hprefix tailTrace_2473249
  have hstable : (prefixWord ++ tailWord_2473249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473249).length < 2 ^ (prefixWord ++ tailWord_2473249).sum := by decide
  have hdescent : baseEnd_2473249 < baseStart_2473249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473253 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_2473253 : Nat := 118140960795 + 2473253 * 2 ^ 59
def prefixEnd_2473253 : Nat := 4983230072969 + 3 ^ 40 * 2473253 * 2
def baseEnd_2473253 : Nat := 1269967569174517119963223

theorem tailTrace_2473253 : CollatzResearch.WordTrace tailWord_2473253 prefixEnd_2473253 1269967569174517119963223 := by
  unfold tailWord_2473253
  simp only [CollatzResearch.WordTrace]
  refine ⟨90206947708834253828688413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60137965139222835885792275 90206947708834253828688413)
  ·
    refine ⟨33827605390812845185758155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90206947708834253828688413 33827605390812845185758155)
    ·
      refine ⟨50741408086219267778637233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33827605390812845185758155 50741408086219267778637233)
      ·
        refine ⟨38056056064664450833977925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50741408086219267778637233 38056056064664450833977925)
        ·
          refine ⟨7135510512124584531370861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38056056064664450833977925 7135510512124584531370861)
          ·
            refine ⟨2675816442046719199264073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7135510512124584531370861 2675816442046719199264073)
            ·
              refine ⟨2006862331535039399448055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675816442046719199264073 2006862331535039399448055)
              ·
                refine ⟨3010293497302559099172083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006862331535039399448055 3010293497302559099172083)
                ·
                  refine ⟨4515440245953838648758125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010293497302559099172083 4515440245953838648758125)
                  ·
                    refine ⟨1693290092232689493284297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4515440245953838648758125 1693290092232689493284297)
                    ·
                      refine ⟨1269967569174517119963223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693290092232689493284297 1269967569174517119963223)
                      ·
                        rfl

theorem cell23_2473253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_2473253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473253 prefixEnd_2473253 := by exact prefixLift 2473253
  have htrace : WordTrace (prefixWord ++ tailWord_2473253) baseStart_2473253 baseEnd_2473253 := by
    simpa [prefixWord, tailWord_2473253, baseEnd_2473253] using wordTrace_append hprefix tailTrace_2473253
  have hstable : (prefixWord ++ tailWord_2473253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473253).length < 2 ^ (prefixWord ++ tailWord_2473253).sum := by decide
  have hdescent : baseEnd_2473253 < baseStart_2473253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473266 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_2473266 : Nat := 118140960795 + 2473266 * 2 ^ 59
def prefixEnd_2473266 : Nat := 4983230072969 + 3 ^ 40 * 2473266 * 2
def baseEnd_2473266 : Nat := 1269974244423025569100663

theorem tailTrace_2473266 : CollatzResearch.WordTrace tailWord_2473266 prefixEnd_2473266 1269974244423025569100663 := by
  unfold tailWord_2473266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22551855464446789262227913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60138281238524771365941101 22551855464446789262227913)
  ·
    refine ⟨16913891598335091946670935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22551855464446789262227913 16913891598335091946670935)
    ·
      refine ⟨25370837397502637920006403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16913891598335091946670935 25370837397502637920006403)
      ·
        refine ⟨38056256096253956880009605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25370837397502637920006403 38056256096253956880009605)
        ·
          refine ⟨7135548018047616915001801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38056256096253956880009605 7135548018047616915001801)
          ·
            refine ⟨5351661013535712686251351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7135548018047616915001801 5351661013535712686251351)
            ·
              refine ⟨8027491520303569029377027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351661013535712686251351 8027491520303569029377027)
              ·
                refine ⟨12041237280455353544065541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027491520303569029377027 12041237280455353544065541)
                ·
                  refine ⟨2257731990085378789512289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12041237280455353544065541 2257731990085378789512289)
                  ·
                    refine ⟨1693298992564034092134217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2257731990085378789512289 1693298992564034092134217)
                    ·
                      refine ⟨1269974244423025569100663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693298992564034092134217 1269974244423025569100663)
                      ·
                        rfl

theorem cell23_2473266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_2473266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473266 prefixEnd_2473266 := by exact prefixLift 2473266
  have htrace : WordTrace (prefixWord ++ tailWord_2473266) baseStart_2473266 baseEnd_2473266 := by
    simpa [prefixWord, tailWord_2473266, baseEnd_2473266] using wordTrace_append hprefix tailTrace_2473266
  have hstable : (prefixWord ++ tailWord_2473266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473266).length < 2 ^ (prefixWord ++ tailWord_2473266).sum := by decide
  have hdescent : baseEnd_2473266 < baseStart_2473266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473319 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 2, 5]
def baseStart_2473319 : Nat := 118140960795 + 2473319 * 2 ^ 59
def prefixEnd_2473319 : Nat := 4983230072969 + 3 ^ 40 * 2473319 * 2
def baseEnd_2473319 : Nat := 423333819632571287245973

theorem tailTrace_2473319 : CollatzResearch.WordTrace tailWord_2473319 prefixEnd_2473319 423333819632571287245973 := by
  unfold tailWord_2473319
  simp only [CollatzResearch.WordTrace]
  refine ⟨90209354926595147100591011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60139569951063431400394007 90209354926595147100591011)
  ·
    refine ⟨135314032389892720650886517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90209354926595147100591011 135314032389892720650886517)
    ·
      refine ⟨12685690536552442561020611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135314032389892720650886517 12685690536552442561020611)
      ·
        refine ⟨19028535804828663841530917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12685690536552442561020611 19028535804828663841530917)
        ·
          refine ⟨3567850463405374470287047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19028535804828663841530917 3567850463405374470287047)
          ·
            refine ⟨5351775695108061705430571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567850463405374470287047 5351775695108061705430571)
            ·
              refine ⟨8027663542662092558145857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351775695108061705430571 8027663542662092558145857)
              ·
                refine ⟨6020747656996569418609393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027663542662092558145857 6020747656996569418609393)
                ·
                  refine ⟨4515560742747427063957045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020747656996569418609393 4515560742747427063957045)
                  ·
                    refine ⟨423333819632571287245973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4515560742747427063957045 423333819632571287245973)
                    ·
                      rfl

theorem cell23_2473319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_2473319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473319 prefixEnd_2473319 := by exact prefixLift 2473319
  have htrace : WordTrace (prefixWord ++ tailWord_2473319) baseStart_2473319 baseEnd_2473319 := by
    simpa [prefixWord, tailWord_2473319, baseEnd_2473319] using wordTrace_append hprefix tailTrace_2473319
  have hstable : (prefixWord ++ tailWord_2473319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473319).length < 2 ^ (prefixWord ++ tailWord_2473319).sum := by decide
  have hdescent : baseEnd_2473319 < baseStart_2473319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473399 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_2473399 : Nat := 118140960795 + 2473399 * 2 ^ 59
def prefixEnd_2473399 : Nat := 4983230072969 + 3 ^ 40 * 2473399 * 2
def baseEnd_2473399 : Nat := 1270042537350073548737551

theorem tailTrace_2473399 : CollatzResearch.WordTrace tailWord_2473399 prefixEnd_2473399 1270042537350073548737551 := by
  unfold tailWord_2473399
  simp only [CollatzResearch.WordTrace]
  refine ⟨90212272766305320763503251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60141515177536880509002167 90212272766305320763503251)
  ·
    refine ⟨135318409149457981145254877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90212272766305320763503251 135318409149457981145254877)
    ·
      refine ⟨50744403431046742929470579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135318409149457981145254877 50744403431046742929470579)
      ·
        refine ⟨76116605146570114394205869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50744403431046742929470579 76116605146570114394205869)
        ·
          refine ⟨28543726929963792897827201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76116605146570114394205869 28543726929963792897827201)
          ·
            refine ⟨21407795197472844673370401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28543726929963792897827201 21407795197472844673370401)
            ·
              refine ⟨16055846398104633505027801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21407795197472844673370401 16055846398104633505027801)
              ·
                refine ⟨12041884798578475128770851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16055846398104633505027801 12041884798578475128770851)
                ·
                  refine ⟨18062827197867712693156277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12041884798578475128770851 18062827197867712693156277)
                  ·
                    refine ⟨1693390049800098064983401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18062827197867712693156277 1693390049800098064983401)
                    ·
                      refine ⟨1270042537350073548737551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693390049800098064983401 1270042537350073548737551)
                      ·
                        rfl

theorem cell23_2473399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_2473399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473399 prefixEnd_2473399 := by exact prefixLift 2473399
  have htrace : WordTrace (prefixWord ++ tailWord_2473399) baseStart_2473399 baseEnd_2473399 := by
    simpa [prefixWord, tailWord_2473399, baseEnd_2473399] using wordTrace_append hprefix tailTrace_2473399
  have hstable : (prefixWord ++ tailWord_2473399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473399).length < 2 ^ (prefixWord ++ tailWord_2473399).sum := by decide
  have hdescent : baseEnd_2473399 < baseStart_2473399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473439 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 4, 4]
def baseStart_2473439 : Nat := 118140960795 + 2473439 * 2 ^ 59
def prefixEnd_2473439 : Nat := 4983230072969 + 3 ^ 40 * 2473439 * 2
def baseEnd_2473439 : Nat := 423354358858751130745789

theorem tailTrace_2473439 : CollatzResearch.WordTrace tailWord_2473439 prefixEnd_2473439 423354358858751130745789 := by
  unfold tailWord_2473439
  simp only [CollatzResearch.WordTrace]
  refine ⟨90213731686160407594959371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60142487790773605063306247 90213731686160407594959371)
  ·
    refine ⟨135320597529240611392439057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90213731686160407594959371 135320597529240611392439057)
    ·
      refine ⟨101490448146930458544329293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135320597529240611392439057 101490448146930458544329293)
      ·
        refine ⟨38058918055098921954123485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101490448146930458544329293 38058918055098921954123485)
        ·
          refine ⟨14272094270662095732796307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38058918055098921954123485 14272094270662095732796307)
          ·
            refine ⟨21408141405993143599194461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14272094270662095732796307 21408141405993143599194461)
            ·
              refine ⟨8028053027247428849697923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21408141405993143599194461 8028053027247428849697923)
              ·
                refine ⟨12042079540871143274546885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8028053027247428849697923 12042079540871143274546885)
                ·
                  refine ⟨2257889913913339363977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12042079540871143274546885 2257889913913339363977541)
                  ·
                    refine ⟨423354358858751130745789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257889913913339363977541 423354358858751130745789)
                    ·
                      rfl

theorem cell23_2473439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_2473439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473439 prefixEnd_2473439 := by exact prefixLift 2473439
  have htrace : WordTrace (prefixWord ++ tailWord_2473439) baseStart_2473439 baseEnd_2473439 := by
    simpa [prefixWord, tailWord_2473439, baseEnd_2473439] using wordTrace_append hprefix tailTrace_2473439
  have hstable : (prefixWord ++ tailWord_2473439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473439).length < 2 ^ (prefixWord ++ tailWord_2473439).sum := by decide
  have hdescent : baseEnd_2473439 < baseStart_2473439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473466 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_2473466 : Nat := 118140960795 + 2473466 * 2 ^ 59
def prefixEnd_2473466 : Nat := 4983230072969 + 3 ^ 40 * 2473466 * 2
def baseEnd_2473466 : Nat := 1270076940553924786599743

theorem tailTrace_2473466 : CollatzResearch.WordTrace tailWord_2473466 prefixEnd_2473466 1270076940553924786599743 := by
  unfold tailWord_2473466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553679114265647801548063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60143144304708394137461501 22553679114265647801548063)
  ·
    refine ⟨33830518671398471702322095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22553679114265647801548063 33830518671398471702322095)
    ·
      refine ⟨50745778007097707553483143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33830518671398471702322095 50745778007097707553483143)
      ·
        refine ⟨76118667010646561330224715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50745778007097707553483143 76118667010646561330224715)
        ·
          refine ⟨114178000515969841995337073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76118667010646561330224715 114178000515969841995337073)
          ·
            refine ⟨85633500386977381496502805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114178000515969841995337073 85633500386977381496502805)
            ·
              refine ⟨4014070330639564757648569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85633500386977381496502805 4014070330639564757648569)
              ·
                refine ⟨3010552747979673568236427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014070330639564757648569 3010552747979673568236427)
                ·
                  refine ⟨4515829121969510352354641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010552747979673568236427 4515829121969510352354641)
                  ·
                    refine ⟨3386871841477132764265981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4515829121969510352354641 3386871841477132764265981)
                    ·
                      refine ⟨1270076940553924786599743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3386871841477132764265981 1270076940553924786599743)
                      ·
                        rfl

theorem cell23_2473466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_2473466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473466 prefixEnd_2473466 := by exact prefixLift 2473466
  have htrace : WordTrace (prefixWord ++ tailWord_2473466) baseStart_2473466 baseEnd_2473466 := by
    simpa [prefixWord, tailWord_2473466, baseEnd_2473466] using wordTrace_append hprefix tailTrace_2473466
  have hstable : (prefixWord ++ tailWord_2473466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473466).length < 2 ^ (prefixWord ++ tailWord_2473466).sum := by decide
  have hdescent : baseEnd_2473466 < baseStart_2473466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473469 : List Nat := [1, 4, 1, 1, 1, 4, 4, 7]
def baseStart_2473469 : Nat := 118140960795 + 2473469 * 2 ^ 59
def prefixEnd_2473469 : Nat := 4983230072969 + 3 ^ 40 * 2473469 * 2
def baseEnd_2473469 : Nat := 47039943740588454624527

theorem tailTrace_2473469 : CollatzResearch.WordTrace tailWord_2473469 prefixEnd_2473469 47039943740588454624527 := by
  unfold tailWord_2473469
  simp only [CollatzResearch.WordTrace]
  refine ⟨90214825876051722718551461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60143217250701148479034307 90214825876051722718551461)
  ·
    refine ⟨16915279851759698009728399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90214825876051722718551461 16915279851759698009728399)
    ·
      refine ⟨25372919777639547014592599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915279851759698009728399 25372919777639547014592599)
      ·
        refine ⟨38059379666459320521888899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25372919777639547014592599 38059379666459320521888899)
        ·
          refine ⟨57089069499688980782833349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38059379666459320521888899 57089069499688980782833349)
          ·
            refine ⟨10704200531191683896781253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57089069499688980782833349 10704200531191683896781253)
            ·
              refine ⟨2007037599598440730646485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10704200531191683896781253 2007037599598440730646485)
              ·
                refine ⟨47039943740588454624527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2007037599598440730646485 47039943740588454624527)
                ·
                  rfl

theorem cell23_2473469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 7].length) (baseStart_2473469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473469 prefixEnd_2473469 := by exact prefixLift 2473469
  have htrace : WordTrace (prefixWord ++ tailWord_2473469) baseStart_2473469 baseEnd_2473469 := by
    simpa [prefixWord, tailWord_2473469, baseEnd_2473469] using wordTrace_append hprefix tailTrace_2473469
  have hstable : (prefixWord ++ tailWord_2473469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473469).length < 2 ^ (prefixWord ++ tailWord_2473469).sum := by decide
  have hdescent : baseEnd_2473469 < baseStart_2473469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473480 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_2473480 : Nat := 118140960795 + 2473480 * 2 ^ 59
def prefixEnd_2473480 : Nat := 4983230072969 + 3 ^ 40 * 2473480 * 2
def baseEnd_2473480 : Nat := 1270084129283087731824679

theorem tailTrace_2473480 : CollatzResearch.WordTrace tailWord_2473480 prefixEnd_2473480 1270084129283087731824679 := by
  unfold tailWord_2473480
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107613539505935798600947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60143484719341247731467929 45107613539505935798600947)
  ·
    refine ⟨67661420309258903697901421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45107613539505935798600947 67661420309258903697901421)
    ·
      refine ⟨25373032615972088886713033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67661420309258903697901421 25373032615972088886713033)
      ·
        refine ⟨19029774461979066665034775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25373032615972088886713033 19029774461979066665034775)
        ·
          refine ⟨28544661692968599997552163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19029774461979066665034775 28544661692968599997552163)
          ·
            refine ⟨42816992539452899996328245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28544661692968599997552163 42816992539452899996328245)
            ·
              refine ⟨4014093050573709374655773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42816992539452899996328245 4014093050573709374655773)
              ·
                refine ⟨1505284893965141015495915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4014093050573709374655773 1505284893965141015495915)
                ·
                  refine ⟨2257927340947711523243873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505284893965141015495915 2257927340947711523243873)
                  ·
                    refine ⟨1693445505710783642432905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2257927340947711523243873 1693445505710783642432905)
                    ·
                      refine ⟨1270084129283087731824679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693445505710783642432905 1270084129283087731824679)
                      ·
                        rfl

theorem cell23_2473480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_2473480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473480 prefixEnd_2473480 := by exact prefixLift 2473480
  have htrace : WordTrace (prefixWord ++ tailWord_2473480) baseStart_2473480 baseEnd_2473480 := by
    simpa [prefixWord, tailWord_2473480, baseEnd_2473480] using wordTrace_append hprefix tailTrace_2473480
  have hstable : (prefixWord ++ tailWord_2473480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473480).length < 2 ^ (prefixWord ++ tailWord_2473480).sum := by decide
  have hdescent : baseEnd_2473480 < baseStart_2473480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473486 : List Nat := [4, 1, 1, 2, 5, 1, 9]
def baseStart_2473486 : Nat := 118140960795 + 2473486 * 2 ^ 59
def prefixEnd_2473486 : Nat := 4983230072969 + 3 ^ 40 * 2473486 * 2
def baseEnd_2473486 : Nat := 15680089014407588991971

theorem tailTrace_2473486 : CollatzResearch.WordTrace tailWord_2473486 prefixEnd_2473486 15680089014407588991971 := by
  unfold tailWord_2473486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11276930739623766827740039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60143630611326756414613541 11276930739623766827740039)
  ·
    refine ⟨16915396109435650241610059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11276930739623766827740039 16915396109435650241610059)
    ·
      refine ⟨25373094164153475362415089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915396109435650241610059 25373094164153475362415089)
      ·
        refine ⟨19029820623115106521811317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25373094164153475362415089 19029820623115106521811317)
        ·
          refine ⟨1784045683417041236419811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19029820623115106521811317 1784045683417041236419811)
          ·
            refine ⟨2676068525125561854629717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784045683417041236419811 2676068525125561854629717)
            ·
              refine ⟨15680089014407588991971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2676068525125561854629717 15680089014407588991971)
              ·
                rfl

theorem cell23_2473486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 9].length) (baseStart_2473486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473486 prefixEnd_2473486 := by exact prefixLift 2473486
  have htrace : WordTrace (prefixWord ++ tailWord_2473486) baseStart_2473486 baseEnd_2473486 := by
    simpa [prefixWord, tailWord_2473486, baseEnd_2473486] using wordTrace_append hprefix tailTrace_2473486
  have hstable : (prefixWord ++ tailWord_2473486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473486).length < 2 ^ (prefixWord ++ tailWord_2473486).sum := by decide
  have hdescent : baseEnd_2473486 < baseStart_2473486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473523 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 1, 3, 2]
def baseStart_2473523 : Nat := 118140960795 + 2473523 * 2 ^ 59
def prefixEnd_2473523 : Nat := 4983230072969 + 3 ^ 40 * 2473523 * 2
def baseEnd_2473523 : Nat := 1270106208951231063586981

theorem tailTrace_2473523 : CollatzResearch.WordTrace tailWord_2473523 prefixEnd_2473523 1270106208951231063586981 := by
  unfold tailWord_2473523
  simp only [CollatzResearch.WordTrace]
  refine ⟨90216795417856089941017223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60144530278570726627344815 90216795417856089941017223)
  ·
    refine ⟨135325193126784134911525835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90216795417856089941017223 135325193126784134911525835)
    ·
      refine ⟨202987789690176202367288753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135325193126784134911525835 202987789690176202367288753)
      ·
        refine ⟨152240842267632151775466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202987789690176202367288753 152240842267632151775466565)
        ·
          refine ⟨28545157925181028457899981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152240842267632151775466565 28545157925181028457899981)
          ·
            refine ⟨10704434221942885671712493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28545157925181028457899981 10704434221942885671712493)
            ·
              refine ⟨4014162833228582126892185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10704434221942885671712493 4014162833228582126892185)
              ·
                refine ⟨3010622124921436595169139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014162833228582126892185 3010622124921436595169139)
                ·
                  refine ⟨4515933187382154892753709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010622124921436595169139 4515933187382154892753709)
                  ·
                    refine ⟨1693474945268308084782641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4515933187382154892753709 1693474945268308084782641)
                    ·
                      refine ⟨1270106208951231063586981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693474945268308084782641 1270106208951231063586981)
                      ·
                        rfl

theorem cell23_2473523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3, 2].length) (baseStart_2473523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473523 prefixEnd_2473523 := by exact prefixLift 2473523
  have htrace : WordTrace (prefixWord ++ tailWord_2473523) baseStart_2473523 baseEnd_2473523 := by
    simpa [prefixWord, tailWord_2473523, baseEnd_2473523] using wordTrace_append hprefix tailTrace_2473523
  have hstable : (prefixWord ++ tailWord_2473523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473523).length < 2 ^ (prefixWord ++ tailWord_2473523).sum := by decide
  have hdescent : baseEnd_2473523 < baseStart_2473523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473576 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 7]
def baseStart_2473576 : Nat := 118140960795 + 2473576 * 2 ^ 59
def prefixEnd_2473576 : Nat := 4983230072969 + 3 ^ 40 * 2473576 * 2
def baseEnd_2473576 : Nat := 141125935936213261802693

theorem tailTrace_2473576 : CollatzResearch.WordTrace tailWord_2473576 prefixEnd_2473576 141125935936213261802693 := by
  unfold tailWord_2473576
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109364243332039996348291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60145818991109386661797721 45109364243332039996348291)
  ·
    refine ⟨67664046364998059994522437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45109364243332039996348291 67664046364998059994522437)
    ·
      refine ⟨12687008693437136248972957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67664046364998059994522437 12687008693437136248972957)
      ·
        refine ⟨4757628260038926093364859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12687008693437136248972957 4757628260038926093364859)
        ·
          refine ⟨7136442390058389140047289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757628260038926093364859 7136442390058389140047289)
          ·
            refine ⟨5352331792543791855035467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7136442390058389140047289 5352331792543791855035467)
            ·
              refine ⟨8028497688815687782553201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5352331792543791855035467 8028497688815687782553201)
              ·
                refine ⟨6021373266611765836914901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8028497688815687782553201 6021373266611765836914901)
                ·
                  refine ⟨141125935936213261802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6021373266611765836914901 141125935936213261802693)
                  ·
                    rfl

theorem cell23_2473576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_2473576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473576 prefixEnd_2473576 := by exact prefixLift 2473576
  have htrace : WordTrace (prefixWord ++ tailWord_2473576) baseStart_2473576 baseEnd_2473576 := by
    simpa [prefixWord, tailWord_2473576, baseEnd_2473576] using wordTrace_append hprefix tailTrace_2473576
  have hstable : (prefixWord ++ tailWord_2473576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473576).length < 2 ^ (prefixWord ++ tailWord_2473576).sum := by decide
  have hdescent : baseEnd_2473576 < baseStart_2473576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473604 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_2473604 : Nat := 118140960795 + 2473604 * 2 ^ 59
def prefixEnd_2473604 : Nat := 4983230072969 + 3 ^ 40 * 2473604 * 2
def baseEnd_2473604 : Nat := 1270147800884245246674109

theorem tailTrace_2473604 : CollatzResearch.WordTrace tailWord_2473604 prefixEnd_2473604 1270147800884245246674109 := by
  unfold tailWord_2473604
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109874865281320387357933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60146499820375093849810577 45109874865281320387357933)
  ·
    refine ⟨16916203074480495145259225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45109874865281320387357933 16916203074480495145259225)
    ·
      refine ⟨12687152305860371358944419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16916203074480495145259225 12687152305860371358944419)
      ·
        refine ⟨19030728458790557038416629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12687152305860371358944419 19030728458790557038416629)
        ·
          refine ⟨1784130793011614722351559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19030728458790557038416629 1784130793011614722351559)
          ·
            refine ⟨2676196189517422083527339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784130793011614722351559 2676196189517422083527339)
            ·
              refine ⟨4014294284276133125291009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676196189517422083527339 4014294284276133125291009)
              ·
                refine ⟨3010720713207099843968257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014294284276133125291009 3010720713207099843968257)
                ·
                  refine ⟨2258040534905324882976193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010720713207099843968257 2258040534905324882976193)
                  ·
                    refine ⟨1693530401178993662232145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2258040534905324882976193 1693530401178993662232145)
                    ·
                      refine ⟨1270147800884245246674109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693530401178993662232145 1270147800884245246674109)
                      ·
                        rfl

theorem cell23_2473604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_2473604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473604 prefixEnd_2473604 := by exact prefixLift 2473604
  have htrace : WordTrace (prefixWord ++ tailWord_2473604) baseStart_2473604 baseEnd_2473604 := by
    simpa [prefixWord, tailWord_2473604, baseEnd_2473604] using wordTrace_append hprefix tailTrace_2473604
  have hstable : (prefixWord ++ tailWord_2473604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473604).length < 2 ^ (prefixWord ++ tailWord_2473604).sum := by decide
  have hdescent : baseEnd_2473604 < baseStart_2473604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473727 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 1, 1, 3]
def baseStart_2473727 : Nat := 118140960795 + 2473727 * 2 ^ 59
def prefixEnd_2473727 : Nat := 4983230072969 + 3 ^ 40 * 2473727 * 2
def baseEnd_2473727 : Nat := 1270210959004748265436043

theorem tailTrace_2473727 : CollatzResearch.WordTrace tailWord_2473727 prefixEnd_2473727 1270210959004748265436043 := by
  unfold tailWord_2473727
  simp only [CollatzResearch.WordTrace]
  refine ⟨90224235909117032781443435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60149490606078021854295623 90224235909117032781443435)
  ·
    refine ⟨135336353863675549172165153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90224235909117032781443435 135336353863675549172165153)
    ·
      refine ⟨101502265397756661879123865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135336353863675549172165153 101502265397756661879123865)
      ·
        refine ⟨76126699048317496409342899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101502265397756661879123865 76126699048317496409342899)
        ·
          refine ⟨114190048572476244614014349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76126699048317496409342899 114190048572476244614014349)
          ·
            refine ⟨42821268214678591730255381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114190048572476244614014349 42821268214678591730255381)
            ·
              refine ⟨2007246947563058987355721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42821268214678591730255381 2007246947563058987355721)
              ·
                refine ⟨1505435210672294240516791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007246947563058987355721 1505435210672294240516791)
                ·
                  refine ⟨2258152816008441360775187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505435210672294240516791 2258152816008441360775187)
                  ·
                    refine ⟨3387229224012662041162781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2258152816008441360775187 3387229224012662041162781)
                    ·
                      refine ⟨1270210959004748265436043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3387229224012662041162781 1270210959004748265436043)
                      ·
                        rfl

theorem cell23_2473727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_2473727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473727 prefixEnd_2473727 := by exact prefixLift 2473727
  have htrace : WordTrace (prefixWord ++ tailWord_2473727) baseStart_2473727 baseEnd_2473727 := by
    simpa [prefixWord, tailWord_2473727, baseEnd_2473727] using wordTrace_append hprefix tailTrace_2473727
  have hstable : (prefixWord ++ tailWord_2473727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473727).length < 2 ^ (prefixWord ++ tailWord_2473727).sum := by decide
  have hdescent : baseEnd_2473727 < baseStart_2473727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473736 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2473736 : Nat := 118140960795 + 2473736 * 2 ^ 59
def prefixEnd_2473736 : Nat := 4983230072969 + 3 ^ 40 * 2473736 * 2
def baseEnd_2473736 : Nat := 1270215580330638730223501

theorem tailTrace_2473736 : CollatzResearch.WordTrace tailWord_2473736 prefixEnd_2473736 1270215580330638730223501 := by
  unfold tailWord_2473736
  simp only [CollatzResearch.WordTrace]
  refine ⟨45112282083042213659260531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60149709444056284879014041 45112282083042213659260531)
  ·
    refine ⟨67668423124563320488890797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45112282083042213659260531 67668423124563320488890797)
    ·
      refine ⟨25375658671711245183334049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67668423124563320488890797 25375658671711245183334049)
      ·
        refine ⟨19031744003783433887500537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25375658671711245183334049 19031744003783433887500537)
        ·
          refine ⟨14273808002837575415625403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19031744003783433887500537 14273808002837575415625403)
          ·
            refine ⟨21410712004256363123438105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14273808002837575415625403 21410712004256363123438105)
            ·
              refine ⟨16058034003192272342578579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21410712004256363123438105 16058034003192272342578579)
              ·
                refine ⟨24087051004788408513867869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16058034003192272342578579 24087051004788408513867869)
                ·
                  refine ⟨9032644126795653192700451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24087051004788408513867869 9032644126795653192700451)
                  ·
                    refine ⟨13548966190193479789050677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9032644126795653192700451 13548966190193479789050677)
                    ·
                      refine ⟨1270215580330638730223501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13548966190193479789050677 1270215580330638730223501)
                      ·
                        rfl

theorem cell23_2473736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2473736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473736 prefixEnd_2473736 := by exact prefixLift 2473736
  have htrace : WordTrace (prefixWord ++ tailWord_2473736) baseStart_2473736 baseEnd_2473736 := by
    simpa [prefixWord, tailWord_2473736, baseEnd_2473736] using wordTrace_append hprefix tailTrace_2473736
  have hstable : (prefixWord ++ tailWord_2473736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473736).length < 2 ^ (prefixWord ++ tailWord_2473736).sum := by decide
  have hdescent : baseEnd_2473736 < baseStart_2473736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473800 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2473800 : Nat := 118140960795 + 2473800 * 2 ^ 59
def prefixEnd_2473800 : Nat := 4983230072969 + 3 ^ 40 * 2473800 * 2
def baseEnd_2473800 : Nat := 1270248443092526479823207

theorem tailTrace_2473800 : CollatzResearch.WordTrace tailWord_2473800 prefixEnd_2473800 1270248443092526479823207 := by
  unfold tailWord_2473800
  simp only [CollatzResearch.WordTrace]
  refine ⟨45113449218926283124425427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60151265625235044165900569 45113449218926283124425427)
  ·
    refine ⟨67670173828389424686638141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45113449218926283124425427 67670173828389424686638141)
    ·
      refine ⟨25376315185646034257489303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67670173828389424686638141 25376315185646034257489303)
      ·
        refine ⟨38064472778469051386233955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25376315185646034257489303 38064472778469051386233955)
        ·
          refine ⟨57096709167703577079350933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38064472778469051386233955 57096709167703577079350933)
          ·
            refine ⟨2676408242236105175594575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57096709167703577079350933 2676408242236105175594575)
            ·
              refine ⟨4014612363354157763391863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676408242236105175594575 4014612363354157763391863)
              ·
                refine ⟨6021918545031236645087795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014612363354157763391863 6021918545031236645087795)
                ·
                  refine ⟨9032877817546854967631693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021918545031236645087795 9032877817546854967631693)
                  ·
                    refine ⟨3387329181580070612861885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9032877817546854967631693 3387329181580070612861885)
                    ·
                      refine ⟨1270248443092526479823207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3387329181580070612861885 1270248443092526479823207)
                      ·
                        rfl

theorem cell23_2473800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2473800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473800 prefixEnd_2473800 := by exact prefixLift 2473800
  have htrace : WordTrace (prefixWord ++ tailWord_2473800) baseStart_2473800 baseEnd_2473800 := by
    simpa [prefixWord, tailWord_2473800, baseEnd_2473800] using wordTrace_append hprefix tailTrace_2473800
  have hstable : (prefixWord ++ tailWord_2473800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473800).length < 2 ^ (prefixWord ++ tailWord_2473800).sum := by decide
  have hdescent : baseEnd_2473800 < baseStart_2473800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473913 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2473913 : Nat := 118140960795 + 2473913 * 2 ^ 59
def prefixEnd_2473913 : Nat := 4983230072969 + 3 ^ 40 * 2473913 * 2
def baseEnd_2473913 : Nat := 1270306466406484537710187

theorem tailTrace_2473913 : CollatzResearch.WordTrace tailWord_2473913 prefixEnd_2473913 1270306466406484537710187 := by
  unfold tailWord_2473913
  simp only [CollatzResearch.WordTrace]
  refine ⟨90231019886443186547714393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60154013257628791031809595 90231019886443186547714393)
  ·
    refine ⟨67673264914832389910785795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90231019886443186547714393 67673264914832389910785795)
    ·
      refine ⟨101509897372248584866178693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67673264914832389910785795 101509897372248584866178693)
      ·
        refine ⟨19033105757296609662408505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101509897372248584866178693 19033105757296609662408505)
        ·
          refine ⟨14274829317972457246806379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19033105757296609662408505 14274829317972457246806379)
          ·
            refine ⟨21412243976958685870209569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274829317972457246806379 21412243976958685870209569)
            ·
              refine ⟨16059182982719014402657177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21412243976958685870209569 16059182982719014402657177)
              ·
                refine ⟨12044387237039260801992883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16059182982719014402657177 12044387237039260801992883)
                ·
                  refine ⟨18066580855558891202989325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12044387237039260801992883 18066580855558891202989325)
                  ·
                    refine ⟨6774967820834584201120997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18066580855558891202989325 6774967820834584201120997)
                    ·
                      refine ⟨1270306466406484537710187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6774967820834584201120997 1270306466406484537710187)
                      ·
                        rfl

theorem cell23_2473913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2473913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473913 prefixEnd_2473913 := by exact prefixLift 2473913
  have htrace : WordTrace (prefixWord ++ tailWord_2473913) baseStart_2473913 baseEnd_2473913 := by
    simpa [prefixWord, tailWord_2473913, baseEnd_2473913] using wordTrace_append hprefix tailTrace_2473913
  have hstable : (prefixWord ++ tailWord_2473913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473913).length < 2 ^ (prefixWord ++ tailWord_2473913).sum := by decide
  have hdescent : baseEnd_2473913 < baseStart_2473913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473930 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_2473930 : Nat := 118140960795 + 2473930 * 2 ^ 59
def prefixEnd_2473930 : Nat := 4983230072969 + 3 ^ 40 * 2473930 * 2
def baseEnd_2473930 : Nat := 1270315195577610971197609

theorem tailTrace_2473930 : CollatzResearch.WordTrace tailWord_2473930 prefixEnd_2473930 1270315195577610971197609 := by
  unfold tailWord_2473930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22557909981845399612770811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60154426618254398967388829 22557909981845399612770811)
  ·
    refine ⟨33836864972768099419156217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22557909981845399612770811 33836864972768099419156217)
    ·
      refine ⟨25377648729576074564367163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33836864972768099419156217 25377648729576074564367163)
      ·
        refine ⟨38066473094364111846550745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25377648729576074564367163 38066473094364111846550745)
        ·
          refine ⟨28549854820773083884913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38066473094364111846550745 28549854820773083884913059)
          ·
            refine ⟨42824782231159625827369589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28549854820773083884913059 42824782231159625827369589)
            ·
              refine ⟨4014823334171214921315899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42824782231159625827369589 4014823334171214921315899)
              ·
                refine ⟨6022235001256822381973849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014823334171214921315899 6022235001256822381973849)
                ·
                  refine ⟨4516676250942616786480387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022235001256822381973849 4516676250942616786480387)
                  ·
                    refine ⟨6775014376413925179720581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516676250942616786480387 6775014376413925179720581)
                    ·
                      refine ⟨1270315195577610971197609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6775014376413925179720581 1270315195577610971197609)
                      ·
                        rfl

theorem cell23_2473930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_2473930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473930 prefixEnd_2473930 := by exact prefixLift 2473930
  have htrace : WordTrace (prefixWord ++ tailWord_2473930) baseStart_2473930 baseEnd_2473930 := by
    simpa [prefixWord, tailWord_2473930, baseEnd_2473930] using wordTrace_append hprefix tailTrace_2473930
  have hstable : (prefixWord ++ tailWord_2473930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473930).length < 2 ^ (prefixWord ++ tailWord_2473930).sum := by decide
  have hdescent : baseEnd_2473930 < baseStart_2473930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473940 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2473940 : Nat := 118140960795 + 2473940 * 2 ^ 59
def prefixEnd_2473940 : Nat := 4983230072969 + 3 ^ 40 * 2473940 * 2
def baseEnd_2473940 : Nat := 423440110128051977357521

theorem tailTrace_2473940 : CollatzResearch.WordTrace tailWord_2473940 prefixEnd_2473940 423440110128051977357521 := by
  unfold tailWord_2473940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45116002328672685079473637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60154669771563580105964849 45116002328672685079473637)
  ·
    refine ⟨8459250436626128452401307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45116002328672685079473637 8459250436626128452401307)
    ·
      refine ⟨12688875654939192678601961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8459250436626128452401307 12688875654939192678601961)
      ·
        refine ⟨9516656741204394508951471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12688875654939192678601961 9516656741204394508951471)
        ·
          refine ⟨14274985111806591763427207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9516656741204394508951471 14274985111806591763427207)
          ·
            refine ⟨21412477667709887645140811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274985111806591763427207 21412477667709887645140811)
            ·
              refine ⟨32118716501564831467711217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21412477667709887645140811 32118716501564831467711217)
              ·
                refine ⟨24089037376173623600783413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32118716501564831467711217 24089037376173623600783413)
                ·
                  refine ⟨2258347254016277212573445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24089037376173623600783413 2258347254016277212573445)
                  ·
                    refine ⟨423440110128051977357521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2258347254016277212573445 423440110128051977357521)
                    ·
                      rfl

theorem cell23_2473940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2473940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473940 prefixEnd_2473940 := by exact prefixLift 2473940
  have htrace : WordTrace (prefixWord ++ tailWord_2473940) baseStart_2473940 baseEnd_2473940 := by
    simpa [prefixWord, tailWord_2473940, baseEnd_2473940] using wordTrace_append hprefix tailTrace_2473940
  have hstable : (prefixWord ++ tailWord_2473940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473940).length < 2 ^ (prefixWord ++ tailWord_2473940).sum := by decide
  have hdescent : baseEnd_2473940 < baseStart_2473940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473983 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 3, 5]
def baseStart_2473983 : Nat := 118140960795 + 2473983 * 2 ^ 59
def prefixEnd_2473983 : Nat := 4983230072969 + 3 ^ 40 * 2473983 * 2
def baseEnd_2473983 : Nat := 423447470017433087944955

theorem tailTrace_2473983 : CollatzResearch.WordTrace tailWord_2473983 prefixEnd_2473983 423447470017433087944955 := by
  unfold tailWord_2473983
  simp only [CollatzResearch.WordTrace]
  refine ⟨90233572996189588502762603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60155715330793059001841735 90233572996189588502762603)
  ·
    refine ⟨135350359494284382754143905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90233572996189588502762603 135350359494284382754143905)
    ·
      refine ⟨101512769620713287065607929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135350359494284382754143905 101512769620713287065607929)
      ·
        refine ⟨76134577215534965299205947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101512769620713287065607929 76134577215534965299205947)
        ·
          refine ⟨114201865823302447948808921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76134577215534965299205947 114201865823302447948808921)
          ·
            refine ⟨85651399367476835961606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114201865823302447948808921 85651399367476835961606691)
            ·
              refine ⟨128477099051215253942410037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85651399367476835961606691 128477099051215253942410037)
              ·
                refine ⟨12044728036051430057100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128477099051215253942410037 12044728036051430057100941)
                ·
                  refine ⟨4516773013519286271412853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12044728036051430057100941 4516773013519286271412853)
                  ·
                    refine ⟨423447470017433087944955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4516773013519286271412853 423447470017433087944955)
                    ·
                      rfl

theorem cell23_2473983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_2473983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2473983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2473983 prefixEnd_2473983 := by exact prefixLift 2473983
  have htrace : WordTrace (prefixWord ++ tailWord_2473983) baseStart_2473983 baseEnd_2473983 := by
    simpa [prefixWord, tailWord_2473983, baseEnd_2473983] using wordTrace_append hprefix tailTrace_2473983
  have hstable : (prefixWord ++ tailWord_2473983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473983).length < 2 ^ (prefixWord ++ tailWord_2473983).sum := by decide
  have hdescent : baseEnd_2473983 < baseStart_2473983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474037 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2474037 : Nat := 118140960795 + 2474037 * 2 ^ 59
def prefixEnd_2474037 : Nat := 4983230072969 + 3 ^ 40 * 2474037 * 2
def baseEnd_2474037 : Nat := 1270370138007642052559617

theorem tailTrace_2474037 : CollatzResearch.WordTrace tailWord_2474037 prefixEnd_2474037 1270370138007642052559617 := by
  unfold tailWord_2474037
  simp only [CollatzResearch.WordTrace]
  refine ⟨90235542537993955725228365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60157028358662637150152243 90235542537993955725228365)
  ·
    refine ⟨33838328451747733396960637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90235542537993955725228365 33838328451747733396960637)
    ·
      refine ⟨12689373169405400023860239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33838328451747733396960637 12689373169405400023860239)
      ·
        refine ⟨19034059754108100035790359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12689373169405400023860239 19034059754108100035790359)
        ·
          refine ⟨28551089631162150053685539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19034059754108100035790359 28551089631162150053685539)
          ·
            refine ⟨42826634446743225080528309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28551089631162150053685539 42826634446743225080528309)
            ·
              refine ⟨4014996979382177351299529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42826634446743225080528309 4014996979382177351299529)
              ·
                refine ⟨3011247734536633013474647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014996979382177351299529 3011247734536633013474647)
                ·
                  refine ⟨4516871601804949520211971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011247734536633013474647 4516871601804949520211971)
                  ·
                    refine ⟨6775307402707424280317957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4516871601804949520211971 6775307402707424280317957)
                    ·
                      refine ⟨1270370138007642052559617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6775307402707424280317957 1270370138007642052559617)
                      ·
                        rfl

theorem cell23_2474037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2474037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474037 prefixEnd_2474037 := by exact prefixLift 2474037
  have htrace : WordTrace (prefixWord ++ tailWord_2474037) baseStart_2474037 baseEnd_2474037 := by
    simpa [prefixWord, tailWord_2474037, baseEnd_2474037] using wordTrace_append hprefix tailTrace_2474037
  have hstable : (prefixWord ++ tailWord_2474037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474037).length < 2 ^ (prefixWord ++ tailWord_2474037).sum := by decide
  have hdescent : baseEnd_2474037 < baseStart_2474037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474073 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_2474073 : Nat := 118140960795 + 2474073 * 2 ^ 59
def prefixEnd_2474073 : Nat := 4983230072969 + 3 ^ 40 * 2474073 * 2
def baseEnd_2474073 : Nat := 423462874437067970569817

theorem tailTrace_2474073 : CollatzResearch.WordTrace tailWord_2474073 prefixEnd_2474073 423462874437067970569817 := by
  unfold tailWord_2474073
  simp only [CollatzResearch.WordTrace]
  refine ⟨90236855565863533873538873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60157903710575689249025915 90236855565863533873538873)
  ·
    refine ⟨67677641674397650405154155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90236855565863533873538873 67677641674397650405154155)
    ·
      refine ⟨101516462511596475607731233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67677641674397650405154155 101516462511596475607731233)
      ·
        refine ⟨76137346883697356705798425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101516462511596475607731233 76137346883697356705798425)
        ·
          refine ⟨57103010162773017529348819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76137346883697356705798425 57103010162773017529348819)
          ·
            refine ⟨85654515244159526294023229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57103010162773017529348819 85654515244159526294023229)
            ·
              refine ⟨32120443216559822360258711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85654515244159526294023229 32120443216559822360258711)
              ·
                refine ⟨48180664824839733540388067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32120443216559822360258711 48180664824839733540388067)
                ·
                  refine ⟨72270997237259600310582101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48180664824839733540388067 72270997237259600310582101)
                  ·
                    refine ⟨423462874437067970569817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72270997237259600310582101 423462874437067970569817)
                    ·
                      rfl

theorem cell23_2474073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_2474073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474073 prefixEnd_2474073 := by exact prefixLift 2474073
  have htrace : WordTrace (prefixWord ++ tailWord_2474073) baseStart_2474073 baseEnd_2474073 := by
    simpa [prefixWord, tailWord_2474073, baseEnd_2474073] using wordTrace_append hprefix tailTrace_2474073
  have hstable : (prefixWord ++ tailWord_2474073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474073).length < 2 ^ (prefixWord ++ tailWord_2474073).sum := by decide
  have hdescent : baseEnd_2474073 < baseStart_2474073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474077 : List Nat := [1, 4, 4, 1, 1, 1, 3, 8]
def baseStart_2474077 : Nat := 118140960795 + 2474077 * 2 ^ 59
def prefixEnd_2474077 : Nat := 4983230072969 + 3 ^ 40 * 2474077 * 2
def baseEnd_2474077 : Nat := 47051506564215625779979

theorem tailTrace_2474077 : CollatzResearch.WordTrace tailWord_2474077 prefixEnd_2474077 47051506564215625779979 := by
  unfold tailWord_2474077
  simp only [CollatzResearch.WordTrace]
  refine ⟨90237001457849042556684485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60158000971899361704456323 90237001457849042556684485)
  ·
    refine ⟨16919437773346695479378341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90237001457849042556684485 16919437773346695479378341)
    ·
      refine ⟨3172394582502505402383439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16919437773346695479378341 3172394582502505402383439)
      ·
        refine ⟨4758591873753758103575159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172394582502505402383439 4758591873753758103575159)
        ·
          refine ⟨7137887810630637155362739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758591873753758103575159 7137887810630637155362739)
          ·
            refine ⟨10706831715945955733044109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7137887810630637155362739 10706831715945955733044109)
            ·
              refine ⟨4015061893479733399891541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10706831715945955733044109 4015061893479733399891541)
              ·
                refine ⟨47051506564215625779979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4015061893479733399891541 47051506564215625779979)
                ·
                  rfl

theorem cell23_2474077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 8].length) (baseStart_2474077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474077 prefixEnd_2474077 := by exact prefixLift 2474077
  have htrace : WordTrace (prefixWord ++ tailWord_2474077) baseStart_2474077 baseEnd_2474077 := by
    simpa [prefixWord, tailWord_2474077, baseEnd_2474077] using wordTrace_append hprefix tailTrace_2474077
  have hstable : (prefixWord ++ tailWord_2474077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474077).length < 2 ^ (prefixWord ++ tailWord_2474077).sum := by decide
  have hdescent : baseEnd_2474077 < baseStart_2474077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474087 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2474087 : Nat := 118140960795 + 2474087 * 2 ^ 59
def prefixEnd_2474087 : Nat := 4983230072969 + 3 ^ 40 * 2474087 * 2
def baseEnd_2474087 : Nat := 1270395812040366856934387

theorem tailTrace_2474087 : CollatzResearch.WordTrace tailWord_2474087 prefixEnd_2474087 1270395812040366856934387 := by
  unfold tailWord_2474087
  simp only [CollatzResearch.WordTrace]
  refine ⟨90237366187812814264548515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60158244125208542843032343 90237366187812814264548515)
  ·
    refine ⟨135356049281719221396822773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90237366187812814264548515 135356049281719221396822773)
    ·
      refine ⟨12689629620161177005952135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135356049281719221396822773 12689629620161177005952135)
      ·
        refine ⟨19034444430241765508928203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12689629620161177005952135 19034444430241765508928203)
        ·
          refine ⟨28551666645362648263392305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19034444430241765508928203 28551666645362648263392305)
          ·
            refine ⟨21413749984021986197544229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28551666645362648263392305 21413749984021986197544229)
            ·
              refine ⟨4015078122004122412039543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21413749984021986197544229 4015078122004122412039543)
              ·
                refine ⟨6022617183006183618059315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015078122004122412039543 6022617183006183618059315)
                ·
                  refine ⟨9033925774509275427088973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022617183006183618059315 9033925774509275427088973)
                  ·
                    refine ⟨3387722165440978285158365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9033925774509275427088973 3387722165440978285158365)
                    ·
                      refine ⟨1270395812040366856934387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3387722165440978285158365 1270395812040366856934387)
                      ·
                        rfl

theorem cell23_2474087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2474087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474087 prefixEnd_2474087 := by exact prefixLift 2474087
  have htrace : WordTrace (prefixWord ++ tailWord_2474087) baseStart_2474087 baseEnd_2474087 := by
    simpa [prefixWord, tailWord_2474087, baseEnd_2474087] using wordTrace_append hprefix tailTrace_2474087
  have hstable : (prefixWord ++ tailWord_2474087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474087).length < 2 ^ (prefixWord ++ tailWord_2474087).sum := by decide
  have hdescent : baseEnd_2474087 < baseStart_2474087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474097 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_2474097 : Nat := 118140960795 + 2474097 * 2 ^ 59
def prefixEnd_2474097 : Nat := 4983230072969 + 3 ^ 40 * 2474097 * 2
def baseEnd_2474097 : Nat := 1270400946846911817809341

theorem tailTrace_2474097 : CollatzResearch.WordTrace tailWord_2474097 prefixEnd_2474097 1270400946846911817809341 := by
  unfold tailWord_2474097
  simp only [CollatzResearch.WordTrace]
  refine ⟨90237730917776585972412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60158487278517723981608363 90237730917776585972412545)
  ·
    refine ⟨67678298188332439479309409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90237730917776585972412545 67678298188332439479309409)
    ·
      refine ⟨50758723641249329609482057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67678298188332439479309409 50758723641249329609482057)
      ·
        refine ⟨38069042730936997207111543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50758723641249329609482057 38069042730936997207111543)
        ·
          refine ⟨57103564096405495810667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38069042730936997207111543 57103564096405495810667315)
          ·
            refine ⟨85655346144608243716000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57103564096405495810667315 85655346144608243716000973)
            ·
              refine ⟨32120754804228091393500365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85655346144608243716000973 32120754804228091393500365)
              ·
                refine ⟨12045283051585534272562637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32120754804228091393500365 12045283051585534272562637)
                ·
                  refine ⟨4516981144344575352210989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12045283051585534272562637 4516981144344575352210989)
                  ·
                    refine ⟨1693867929129215757079121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4516981144344575352210989 1693867929129215757079121)
                    ·
                      refine ⟨1270400946846911817809341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693867929129215757079121 1270400946846911817809341)
                      ·
                        rfl

theorem cell23_2474097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_2474097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474097 prefixEnd_2474097 := by exact prefixLift 2474097
  have htrace : WordTrace (prefixWord ++ tailWord_2474097) baseStart_2474097 baseEnd_2474097 := by
    simpa [prefixWord, tailWord_2474097, baseEnd_2474097] using wordTrace_append hprefix tailTrace_2474097
  have hstable : (prefixWord ++ tailWord_2474097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474097).length < 2 ^ (prefixWord ++ tailWord_2474097).sum := by decide
  have hdescent : baseEnd_2474097 < baseStart_2474097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474138 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2474138 : Nat := 118140960795 + 2474138 * 2 ^ 59
def prefixEnd_2474138 : Nat := 4983230072969 + 3 ^ 40 * 2474138 * 2
def baseEnd_2474138 : Nat := 1270421999553746157396653

theorem tailTrace_2474138 : CollatzResearch.WordTrace tailWord_2474138 prefixEnd_2474138 1270421999553746157396653 := by
  unfold tailWord_2474138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559806577657012493663767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60159484207085366649770045 22559806577657012493663767)
  ·
    refine ⟨33839709866485518740495651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559806577657012493663767 33839709866485518740495651)
    ·
      refine ⟨50759564799728278110743477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33839709866485518740495651 50759564799728278110743477)
      ·
        refine ⟨4758709199974526072882201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50759564799728278110743477 4758709199974526072882201)
        ·
          refine ⟨3569031899980894554661651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4758709199974526072882201 3569031899980894554661651)
          ·
            refine ⟨5353547849971341831992477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569031899980894554661651 5353547849971341831992477)
            ·
              refine ⟨2007580443739253186997179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5353547849971341831992477 2007580443739253186997179)
              ·
                refine ⟨3011370665608879780495769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007580443739253186997179 3011370665608879780495769)
                ·
                  refine ⟨2258527999206659835371827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3011370665608879780495769 2258527999206659835371827)
                  ·
                    refine ⟨3387791998809989753057741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2258527999206659835371827 3387791998809989753057741)
                    ·
                      refine ⟨1270421999553746157396653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3387791998809989753057741 1270421999553746157396653)
                      ·
                        rfl

theorem cell23_2474138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2474138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474138 prefixEnd_2474138 := by exact prefixLift 2474138
  have htrace : WordTrace (prefixWord ++ tailWord_2474138) baseStart_2474138 baseEnd_2474138 := by
    simpa [prefixWord, tailWord_2474138, baseEnd_2474138] using wordTrace_append hprefix tailTrace_2474138
  have hstable : (prefixWord ++ tailWord_2474138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474138).length < 2 ^ (prefixWord ++ tailWord_2474138).sum := by decide
  have hdescent : baseEnd_2474138 < baseStart_2474138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474144 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2]
def baseStart_2474144 : Nat := 118140960795 + 2474144 * 2 ^ 59
def prefixEnd_2474144 : Nat := 4983230072969 + 3 ^ 40 * 2474144 * 2
def baseEnd_2474144 : Nat := 1270425080437673133921625

theorem tailTrace_2474144 : CollatzResearch.WordTrace tailWord_2474144 prefixEnd_2474144 1270425080437673133921625 := by
  unfold tailWord_2474144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119722574303156499686743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60159630099070875332915657 45119722574303156499686743)
  ·
    refine ⟨67679583861454734749530115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45119722574303156499686743 67679583861454734749530115)
    ·
      refine ⟨101519375792182102124295173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67679583861454734749530115 101519375792182102124295173)
      ·
        refine ⟨19034882961034144148305345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101519375792182102124295173 19034882961034144148305345)
        ·
          refine ⟨14276162220775608111229009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19034882961034144148305345 14276162220775608111229009)
          ·
            refine ⟨10707121665581706083421757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14276162220775608111229009 10707121665581706083421757)
            ·
              refine ⟨4015170624593139781283159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10707121665581706083421757 4015170624593139781283159)
              ·
                refine ⟨6022755936889709671924739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015170624593139781283159 6022755936889709671924739)
                ·
                  refine ⟨9034133905334564507887109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022755936889709671924739 9034133905334564507887109)
                  ·
                    refine ⟨1693900107250230845228833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9034133905334564507887109 1693900107250230845228833)
                    ·
                      refine ⟨1270425080437673133921625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693900107250230845228833 1270425080437673133921625)
                      ·
                        rfl

theorem cell23_2474144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_2474144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474144 prefixEnd_2474144 := by exact prefixLift 2474144
  have htrace : WordTrace (prefixWord ++ tailWord_2474144) baseStart_2474144 baseEnd_2474144 := by
    simpa [prefixWord, tailWord_2474144, baseEnd_2474144] using wordTrace_append hprefix tailTrace_2474144
  have hstable : (prefixWord ++ tailWord_2474144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474144).length < 2 ^ (prefixWord ++ tailWord_2474144).sum := by decide
  have hdescent : baseEnd_2474144 < baseStart_2474144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474187 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 5, 2]
def baseStart_2474187 : Nat := 118140960795 + 2474187 * 2 ^ 59
def prefixEnd_2474187 : Nat := 4983230072969 + 3 ^ 40 * 2474187 * 2
def baseEnd_2474187 : Nat := 1270447160105816465683927

theorem tailTrace_2474187 : CollatzResearch.WordTrace tailWord_2474187 prefixEnd_2474187 1270447160105816465683927 := by
  unfold tailWord_2474187
  simp only [CollatzResearch.WordTrace]
  refine ⟨90241013487450531343188815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60160675658300354228792543 90241013487450531343188815)
  ·
    refine ⟨135361520231175797014783223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90241013487450531343188815 135361520231175797014783223)
    ·
      refine ⟨203042280346763695522174835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135361520231175797014783223 203042280346763695522174835)
      ·
        refine ⟨304563420520145543283262253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203042280346763695522174835 304563420520145543283262253)
        ·
          refine ⟨114211282695054578731223345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304563420520145543283262253 114211282695054578731223345)
          ·
            refine ⟨85658462021290934048417509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114211282695054578731223345 85658462021290934048417509)
            ·
              refine ⟨16060961628992050134078283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85658462021290934048417509 16060961628992050134078283)
              ·
                refine ⟨24091442443488075201117425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16060961628992050134078283 24091442443488075201117425)
                ·
                  refine ⟨18068581832616056400838069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24091442443488075201117425 18068581832616056400838069)
                  ·
                    refine ⟨1693929546807755287578569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18068581832616056400838069 1693929546807755287578569)
                    ·
                      refine ⟨1270447160105816465683927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693929546807755287578569 1270447160105816465683927)
                      ·
                        rfl

theorem cell23_2474187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5, 2].length) (baseStart_2474187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474187 prefixEnd_2474187 := by exact prefixLift 2474187
  have htrace : WordTrace (prefixWord ++ tailWord_2474187) baseStart_2474187 baseEnd_2474187 := by
    simpa [prefixWord, tailWord_2474187, baseEnd_2474187] using wordTrace_append hprefix tailTrace_2474187
  have hstable : (prefixWord ++ tailWord_2474187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474187).length < 2 ^ (prefixWord ++ tailWord_2474187).sum := by decide
  have hdescent : baseEnd_2474187 < baseStart_2474187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474217 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 6, 2]
def baseStart_2474217 : Nat := 118140960795 + 2474217 * 2 ^ 59
def prefixEnd_2474217 : Nat := 4983230072969 + 3 ^ 40 * 2474217 * 2
def baseEnd_2474217 : Nat := 1270462564525451348308789

theorem tailTrace_2474217 : CollatzResearch.WordTrace tailWord_2474217 prefixEnd_2474217 1270462564525451348308789 := by
  unfold tailWord_2474217
  simp only [CollatzResearch.WordTrace]
  refine ⟨90242107677341846466780905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60161405118227897644520603 90242107677341846466780905)
  ·
    refine ⟨67681580758006384850085679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90242107677341846466780905 67681580758006384850085679)
    ·
      refine ⟨101522371137009577275128519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67681580758006384850085679 101522371137009577275128519)
      ·
        refine ⟨152283556705514365912692779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101522371137009577275128519 152283556705514365912692779)
        ·
          refine ⟨228425335058271548869039169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152283556705514365912692779 228425335058271548869039169)
          ·
            refine ⟨171319001293703661651779377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228425335058271548869039169 171319001293703661651779377)
            ·
              refine ⟨128489250970277746238834533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171319001293703661651779377 128489250970277746238834533)
              ·
                refine ⟨24091734556927077419781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128489250970277746238834533 24091734556927077419781475)
                ·
                  refine ⟨36137601835390616129672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24091734556927077419781475 36137601835390616129672213)
                  ·
                    refine ⟨1693950086033935131078385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36137601835390616129672213 1693950086033935131078385)
                    ·
                      refine ⟨1270462564525451348308789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1693950086033935131078385 1270462564525451348308789)
                      ·
                        rfl

theorem cell23_2474217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6, 2].length) (baseStart_2474217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474217 prefixEnd_2474217 := by exact prefixLift 2474217
  have htrace : WordTrace (prefixWord ++ tailWord_2474217) baseStart_2474217 baseEnd_2474217 := by
    simpa [prefixWord, tailWord_2474217, baseEnd_2474217] using wordTrace_append hprefix tailTrace_2474217
  have hstable : (prefixWord ++ tailWord_2474217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474217).length < 2 ^ (prefixWord ++ tailWord_2474217).sum := by decide
  have hdescent : baseEnd_2474217 < baseStart_2474217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474240 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 8]
def baseStart_2474240 : Nat := 118140960795 + 2474240 * 2 ^ 59
def prefixEnd_2474240 : Nat := 4983230072969 + 3 ^ 40 * 2474240 * 2
def baseEnd_2474240 : Nat := 141163819397833862035687

theorem tailTrace_2474240 : CollatzResearch.WordTrace tailWord_2474240 prefixEnd_2474240 141163819397833862035687 := by
  unfold tailWord_2474240
  simp only [CollatzResearch.WordTrace]
  refine ⟨45121473278129260697434087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60161964370839014263245449 45121473278129260697434087)
  ·
    refine ⟨67682209917193891046151131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45121473278129260697434087 67682209917193891046151131)
    ·
      refine ⟨101523314875790836569226697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67682209917193891046151131 101523314875790836569226697)
      ·
        refine ⟨76142486156843127426920023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101523314875790836569226697 76142486156843127426920023)
        ·
          refine ⟨114213729235264691140380035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76142486156843127426920023 114213729235264691140380035)
          ·
            refine ⟨171320593852897036710570053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114213729235264691140380035 171320593852897036710570053)
            ·
              refine ⟨32122611347418194383231885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171320593852897036710570053 32122611347418194383231885)
              ·
                refine ⟨12045979255281822893711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32122611347418194383231885 12045979255281822893711957)
                ·
                  refine ⟨141163819397833862035687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12045979255281822893711957 141163819397833862035687)
                  ·
                    rfl

theorem cell23_2474240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_2474240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474240 prefixEnd_2474240 := by exact prefixLift 2474240
  have htrace : WordTrace (prefixWord ++ tailWord_2474240) baseStart_2474240 baseEnd_2474240 := by
    simpa [prefixWord, tailWord_2474240, baseEnd_2474240] using wordTrace_append hprefix tailTrace_2474240
  have hstable : (prefixWord ++ tailWord_2474240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474240).length < 2 ^ (prefixWord ++ tailWord_2474240).sum := by decide
  have hdescent : baseEnd_2474240 < baseStart_2474240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474257 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 6]
def baseStart_2474257 : Nat := 118140960795 + 2474257 * 2 ^ 59
def prefixEnd_2474257 : Nat := 4983230072969 + 3 ^ 40 * 2474257 * 2
def baseEnd_2474257 : Nat := 141164789305736799089845

theorem tailTrace_2474257 : CollatzResearch.WordTrace tailWord_2474257 prefixEnd_2474257 141164789305736799089845 := by
  unfold tailWord_2474257
  simp only [CollatzResearch.WordTrace]
  refine ⟨90243566597196933298237025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60162377731464622198824683 90243566597196933298237025)
  ·
    refine ⟨67682674947897699973677769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90243566597196933298237025 67682674947897699973677769)
    ·
      refine ⟨50762006210923274980258327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67682674947897699973677769 50762006210923274980258327)
      ·
        refine ⟨76143009316384912470387491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50762006210923274980258327 76143009316384912470387491)
        ·
          refine ⟨114214513974577368705581237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76143009316384912470387491 114214513974577368705581237)
          ·
            refine ⟨10707610685116628316148241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114214513974577368705581237 10707610685116628316148241)
            ·
              refine ⟨8030708013837471237111181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10707610685116628316148241 8030708013837471237111181)
              ·
                refine ⟨3011515505189051713916693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8030708013837471237111181 3011515505189051713916693)
                ·
                  refine ⟨141164789305736799089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3011515505189051713916693 141164789305736799089845)
                  ·
                    rfl

theorem cell23_2474257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_2474257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474257 prefixEnd_2474257 := by exact prefixLift 2474257
  have htrace : WordTrace (prefixWord ++ tailWord_2474257) baseStart_2474257 baseEnd_2474257 := by
    simpa [prefixWord, tailWord_2474257, baseEnd_2474257] using wordTrace_append hprefix tailTrace_2474257
  have hstable : (prefixWord ++ tailWord_2474257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474257).length < 2 ^ (prefixWord ++ tailWord_2474257).sum := by decide
  have hdescent : baseEnd_2474257 < baseStart_2474257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474271 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2474271 : Nat := 118140960795 + 2474271 * 2 ^ 59
def prefixEnd_2474271 : Nat := 4983230072969 + 3 ^ 40 * 2474271 * 2
def baseEnd_2474271 : Nat := 1270490292480794137033541

theorem tailTrace_2474271 : CollatzResearch.WordTrace tailWord_2474271 prefixEnd_2474271 1270490292480794137033541 := by
  unfold tailWord_2474271
  simp only [CollatzResearch.WordTrace]
  refine ⟨90244077219146213689246667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60162718146097475792831111 90244077219146213689246667)
  ·
    refine ⟨135366115828719320533870001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90244077219146213689246667 135366115828719320533870001)
    ·
      refine ⟨101524586871539490400402501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135366115828719320533870001 101524586871539490400402501)
      ·
        refine ⟨19035860038413654450075469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101524586871539490400402501 19035860038413654450075469)
        ·
          refine ⟨7138447514405120418778301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19035860038413654450075469 7138447514405120418778301)
          ·
            refine ⟨2676917817901920157041863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138447514405120418778301 2676917817901920157041863)
            ·
              refine ⟨4015376726852880235562795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676917817901920157041863 4015376726852880235562795)
              ·
                refine ⟨6023065090279320353344193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015376726852880235562795 6023065090279320353344193)
                ·
                  refine ⟨4517298817709490265008145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6023065090279320353344193 4517298817709490265008145)
                  ·
                    refine ⟨3387974113282117698756109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4517298817709490265008145 3387974113282117698756109)
                    ·
                      refine ⟨1270490292480794137033541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3387974113282117698756109 1270490292480794137033541)
                      ·
                        rfl

theorem cell23_2474271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2474271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474271 prefixEnd_2474271 := by exact prefixLift 2474271
  have htrace : WordTrace (prefixWord ++ tailWord_2474271) baseStart_2474271 baseEnd_2474271 := by
    simpa [prefixWord, tailWord_2474271, baseEnd_2474271] using wordTrace_append hprefix tailTrace_2474271
  have hstable : (prefixWord ++ tailWord_2474271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474271).length < 2 ^ (prefixWord ++ tailWord_2474271).sum := by decide
  have hdescent : baseEnd_2474271 < baseStart_2474271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474307 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4]
def baseStart_2474307 : Nat := 118140960795 + 2474307 * 2 ^ 59
def prefixEnd_2474307 : Nat := 4983230072969 + 3 ^ 40 * 2474307 * 2
def baseEnd_2474307 : Nat := 1270508777784355996183375

theorem tailTrace_2474307 : CollatzResearch.WordTrace tailWord_2474307 prefixEnd_2474307 1270508777784355996183375 := by
  unfold tailWord_2474307
  simp only [CollatzResearch.WordTrace]
  refine ⟨90245390247015791837557175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60163593498010527891704783 90245390247015791837557175)
  ·
    refine ⟨135368085370523687756335763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90245390247015791837557175 135368085370523687756335763)
    ·
      refine ⟨203052128055785531634503645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135368085370523687756335763 203052128055785531634503645)
      ·
        refine ⟨76144548020919574362938867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203052128055785531634503645 76144548020919574362938867)
        ·
          refine ⟨114216822031379361544408301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76144548020919574362938867 114216822031379361544408301)
          ·
            refine ⟨42831308261767260579153113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114216822031379361544408301 42831308261767260579153113)
            ·
              refine ⟨32123481196325445434364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42831308261767260579153113 32123481196325445434364835)
              ·
                refine ⟨48185221794488168151547253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32123481196325445434364835 48185221794488168151547253)
                ·
                  refine ⟨4517364543233265764207555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48185221794488168151547253 4517364543233265764207555)
                  ·
                    refine ⟨6776046814849898646311333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517364543233265764207555 6776046814849898646311333)
                    ·
                      refine ⟨1270508777784355996183375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6776046814849898646311333 1270508777784355996183375)
                      ·
                        rfl

theorem cell23_2474307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_2474307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474307 prefixEnd_2474307 := by exact prefixLift 2474307
  have htrace : WordTrace (prefixWord ++ tailWord_2474307) baseStart_2474307 baseEnd_2474307 := by
    simpa [prefixWord, tailWord_2474307, baseEnd_2474307] using wordTrace_append hprefix tailTrace_2474307
  have hstable : (prefixWord ++ tailWord_2474307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474307).length < 2 ^ (prefixWord ++ tailWord_2474307).sum := by decide
  have hdescent : baseEnd_2474307 < baseStart_2474307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474308 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 6]
def baseStart_2474308 : Nat := 118140960795 + 2474308 * 2 ^ 59
def prefixEnd_2474308 : Nat := 4983230072969 + 3 ^ 40 * 2474308 * 2
def baseEnd_2474308 : Nat := 141167699029445610252319

theorem tailTrace_2474308 : CollatzResearch.WordTrace tailWord_2474308 prefixEnd_2474308 141167699029445610252319 := by
  unfold tailWord_2474308
  simp only [CollatzResearch.WordTrace]
  refine ⟨45122713360006084504171789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60163617813341446005562385 45122713360006084504171789)
  ·
    refine ⟨16921017510002281689064421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45122713360006084504171789 16921017510002281689064421)
    ·
      refine ⟨3172690783125427816699579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16921017510002281689064421 3172690783125427816699579)
      ·
        refine ⟨4759036174688141725049369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172690783125427816699579 4759036174688141725049369)
        ·
          refine ⟨3569277131016106293787027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4759036174688141725049369 3569277131016106293787027)
          ·
            refine ⟨5353915696524159440680541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569277131016106293787027 5353915696524159440680541)
            ·
              refine ⟨2007718386196559790255203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5353915696524159440680541 2007718386196559790255203)
              ·
                refine ⟨3011577579294839685382805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007718386196559790255203 3011577579294839685382805)
                ·
                  refine ⟨141167699029445610252319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3011577579294839685382805 141167699029445610252319)
                  ·
                    rfl

theorem cell23_2474308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_2474308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474308 prefixEnd_2474308 := by exact prefixLift 2474308
  have htrace : WordTrace (prefixWord ++ tailWord_2474308) baseStart_2474308 baseEnd_2474308 := by
    simpa [prefixWord, tailWord_2474308, baseEnd_2474308] using wordTrace_append hprefix tailTrace_2474308
  have hstable : (prefixWord ++ tailWord_2474308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474308).length < 2 ^ (prefixWord ++ tailWord_2474308).sum := by decide
  have hdescent : baseEnd_2474308 < baseStart_2474308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474327 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2474327 : Nat := 118140960795 + 2474327 * 2 ^ 59
def prefixEnd_2474327 : Nat := 4983230072969 + 3 ^ 40 * 2474327 * 2
def baseEnd_2474327 : Nat := 1270519047397445917933283

theorem tailTrace_2474327 : CollatzResearch.WordTrace tailWord_2474327 prefixEnd_2474327 1270519047397445917933283 := by
  unfold tailWord_2474327
  simp only [CollatzResearch.WordTrace]
  refine ⟨90246119706943335253285235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60164079804628890168856823 90246119706943335253285235)
  ·
    refine ⟨135369179560415002879927853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90246119706943335253285235 135369179560415002879927853)
    ·
      refine ⟨50763442335155626079972945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135369179560415002879927853 50763442335155626079972945)
      ·
        refine ⟨38072581751366719559979709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50763442335155626079972945 38072581751366719559979709)
        ·
          refine ⟨14277218156762519834992391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38072581751366719559979709 14277218156762519834992391)
          ·
            refine ⟨21415827235143779752488587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14277218156762519834992391 21415827235143779752488587)
            ·
              refine ⟨32123740852715669628732881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21415827235143779752488587 32123740852715669628732881)
              ·
                refine ⟨24092805639536752221549661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32123740852715669628732881 24092805639536752221549661)
                ·
                  refine ⟨9034802114826282083081123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24092805639536752221549661 9034802114826282083081123)
                  ·
                    refine ⟨13552203172239423124621685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9034802114826282083081123 13552203172239423124621685)
                    ·
                      refine ⟨1270519047397445917933283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13552203172239423124621685 1270519047397445917933283)
                      ·
                        rfl

theorem cell23_2474327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2474327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474327 prefixEnd_2474327 := by exact prefixLift 2474327
  have htrace : WordTrace (prefixWord ++ tailWord_2474327) baseStart_2474327 baseEnd_2474327 := by
    simpa [prefixWord, tailWord_2474327, baseEnd_2474327] using wordTrace_append hprefix tailTrace_2474327
  have hstable : (prefixWord ++ tailWord_2474327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474327).length < 2 ^ (prefixWord ++ tailWord_2474327).sum := by decide
  have hdescent : baseEnd_2474327 < baseStart_2474327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474344 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2474344 : Nat := 118140960795 + 2474344 * 2 ^ 59
def prefixEnd_2474344 : Nat := 4983230072969 + 3 ^ 40 * 2474344 * 2
def baseEnd_2474344 : Nat := 1270527776568572351420705

theorem tailTrace_2474344 : CollatzResearch.WordTrace tailWord_2474344 prefixEnd_2474344 1270527776568572351420705 := by
  unfold tailWord_2474344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45123369873940873578327043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60164493165254498104436057 45123369873940873578327043)
  ·
    refine ⟨67685054810911310367490565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45123369873940873578327043 67685054810911310367490565)
    ·
      refine ⟨12690947777045870693904481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67685054810911310367490565 12690947777045870693904481)
      ·
        refine ⟨9518210832784403020428361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12690947777045870693904481 9518210832784403020428361)
        ·
          refine ⟨7138658124588302265321271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518210832784403020428361 7138658124588302265321271)
          ·
            refine ⟨10707987186882453397981907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138658124588302265321271 10707987186882453397981907)
            ·
              refine ⟨16061980780323680096972861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10707987186882453397981907 16061980780323680096972861)
              ·
                refine ⟨6023242792621380036364823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16061980780323680096972861 6023242792621380036364823)
                ·
                  refine ⟨9034864188932070054547235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023242792621380036364823 9034864188932070054547235)
                  ·
                    refine ⟨13552296283398105081820853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9034864188932070054547235 13552296283398105081820853)
                    ·
                      refine ⟨1270527776568572351420705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13552296283398105081820853 1270527776568572351420705)
                      ·
                        rfl

theorem cell23_2474344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2474344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474344 prefixEnd_2474344 := by exact prefixLift 2474344
  have htrace : WordTrace (prefixWord ++ tailWord_2474344) baseStart_2474344 baseEnd_2474344 := by
    simpa [prefixWord, tailWord_2474344, baseEnd_2474344] using wordTrace_append hprefix tailTrace_2474344
  have hstable : (prefixWord ++ tailWord_2474344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474344).length < 2 ^ (prefixWord ++ tailWord_2474344).sum := by decide
  have hdescent : baseEnd_2474344 < baseStart_2474344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474378 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2474378 : Nat := 118140960795 + 2474378 * 2 ^ 59
def prefixEnd_2474378 : Nat := 4983230072969 + 3 ^ 40 * 2474378 * 2
def baseEnd_2474378 : Nat := 1270545234910825218395549

theorem tailTrace_2474378 : CollatzResearch.WordTrace tailWord_2474378 prefixEnd_2474378 1270545234910825218395549 := by
  unfold tailWord_2474378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561994957439642740847947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60165319886505713975594525 22561994957439642740847947)
  ·
    refine ⟨33842992436159464111271921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22561994957439642740847947 33842992436159464111271921)
    ·
      refine ⟨25382244327119598083453941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33842992436159464111271921 25382244327119598083453941)
      ·
        refine ⟨2379585405667462320323807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25382244327119598083453941 2379585405667462320323807)
        ·
          refine ⟨3569378108501193480485711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379585405667462320323807 3569378108501193480485711)
          ·
            refine ⟨5354067162751790220728567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569378108501193480485711 5354067162751790220728567)
            ·
              refine ⟨8031100744127685331092851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354067162751790220728567 8031100744127685331092851)
              ·
                refine ⟨12046651116191527996639277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031100744127685331092851 12046651116191527996639277)
                ·
                  refine ⟨4517494168571822998739729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12046651116191527996639277 4517494168571822998739729)
                  ·
                    refine ⟨3388120626428867249054797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4517494168571822998739729 3388120626428867249054797)
                    ·
                      refine ⟨1270545234910825218395549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388120626428867249054797 1270545234910825218395549)
                      ·
                        rfl

theorem cell23_2474378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2474378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474378 prefixEnd_2474378 := by exact prefixLift 2474378
  have htrace : WordTrace (prefixWord ++ tailWord_2474378) baseStart_2474378 baseEnd_2474378 := by
    simpa [prefixWord, tailWord_2474378, baseEnd_2474378] using wordTrace_append hprefix tailTrace_2474378
  have hstable : (prefixWord ++ tailWord_2474378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474378).length < 2 ^ (prefixWord ++ tailWord_2474378).sum := by decide
  have hdescent : baseEnd_2474378 < baseStart_2474378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474431 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 8, 2, 2]
def baseStart_2474431 : Nat := 118140960795 + 2474431 * 2 ^ 59
def prefixEnd_2474431 : Nat := 4983230072969 + 3 ^ 40 * 2474431 * 2
def baseEnd_2474431 : Nat := 1270572449385513511032805

theorem tailTrace_2474431 : CollatzResearch.WordTrace tailWord_2474431 prefixEnd_2474431 1270572449385513511032805 := by
  unfold tailWord_2474431
  simp only [CollatzResearch.WordTrace]
  refine ⟨90249912898566561015071147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60166608599044374010047431 90249912898566561015071147)
  ·
    refine ⟨135374869347849841522606721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90249912898566561015071147 135374869347849841522606721)
    ·
      refine ⟨101531152010887381141955041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135374869347849841522606721 101531152010887381141955041)
      ·
        refine ⟨76148364008165535856466281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101531152010887381141955041 76148364008165535856466281)
        ·
          refine ⟨57111273006124151892349711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76148364008165535856466281 57111273006124151892349711)
          ·
            refine ⟨85666909509186227838524567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57111273006124151892349711 85666909509186227838524567)
            ·
              refine ⟨128500364263779341757786851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85666909509186227838524567 128500364263779341757786851)
              ·
                refine ⟨192750546395669012636680277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128500364263779341757786851 192750546395669012636680277)
                ·
                  refine ⟨2258795465574246241836097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 192750546395669012636680277 2258795465574246241836097)
                  ·
                    refine ⟨1694096599180684681377073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2258795465574246241836097 1694096599180684681377073)
                    ·
                      refine ⟨1270572449385513511032805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694096599180684681377073 1270572449385513511032805)
                      ·
                        rfl

theorem cell23_2474431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_2474431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474431 prefixEnd_2474431 := by exact prefixLift 2474431
  have htrace : WordTrace (prefixWord ++ tailWord_2474431) baseStart_2474431 baseEnd_2474431 := by
    simpa [prefixWord, tailWord_2474431, baseEnd_2474431] using wordTrace_append hprefix tailTrace_2474431
  have hstable : (prefixWord ++ tailWord_2474431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474431).length < 2 ^ (prefixWord ++ tailWord_2474431).sum := by decide
  have hdescent : baseEnd_2474431 < baseStart_2474431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_2474447 : Nat := 118140960795 + 2474447 * 2 ^ 59
def prefixEnd_2474447 : Nat := 4983230072969 + 3 ^ 40 * 2474447 * 2
def baseEnd_2474447 : Nat := 1270580665075985448432731

theorem tailTrace_2474447 : CollatzResearch.WordTrace tailWord_2474447 prefixEnd_2474447 1270580665075985448432731 := by
  unfold tailWord_2474447
  simp only [CollatzResearch.WordTrace]
  refine ⟨90250496466508595747653595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60166997644339063831769063 90250496466508595747653595)
  ·
    refine ⟨135375744699762893621480393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90250496466508595747653595 135375744699762893621480393)
    ·
      refine ⟨101531808524822170216110295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135375744699762893621480393 101531808524822170216110295)
      ·
        refine ⟨152297712787233255324165443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101531808524822170216110295 152297712787233255324165443)
        ·
          refine ⟨228446569180849882986248165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152297712787233255324165443 228446569180849882986248165)
          ·
            refine ⟨42833731721409353059921531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228446569180849882986248165 42833731721409353059921531)
            ·
              refine ⟨64250597582114029589882297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42833731721409353059921531 64250597582114029589882297)
              ·
                refine ⟨48187948186585522192411723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64250597582114029589882297 48187948186585522192411723)
                ·
                  refine ⟨72281922279878283288617585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48187948186585522192411723 72281922279878283288617585)
                  ·
                    refine ⟨54211441709908712466463189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72281922279878283288617585 54211441709908712466463189)
                    ·
                      refine ⟨1270580665075985448432731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54211441709908712466463189 1270580665075985448432731)
                      ·
                        rfl

theorem cell23_2474447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_2474447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474447 prefixEnd_2474447 := by exact prefixLift 2474447
  have htrace : WordTrace (prefixWord ++ tailWord_2474447) baseStart_2474447 baseEnd_2474447 := by
    simpa [prefixWord, tailWord_2474447, baseEnd_2474447] using wordTrace_append hprefix tailTrace_2474447
  have hstable : (prefixWord ++ tailWord_2474447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474447).length < 2 ^ (prefixWord ++ tailWord_2474447).sum := by decide
  have hdescent : baseEnd_2474447 < baseStart_2474447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474452 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2474452 : Nat := 118140960795 + 2474452 * 2 ^ 59
def prefixEnd_2474452 : Nat := 4983230072969 + 3 ^ 40 * 2474452 * 2
def baseEnd_2474452 : Nat := 1270583232479257928870209

theorem tailTrace_2474452 : CollatzResearch.WordTrace tailWord_2474452 prefixEnd_2474452 1270583232479257928870209 := by
  unfold tailWord_2474452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125339415745240800792805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60167119220993654401057073 45125339415745240800792805)
  ·
    refine ⟨8461001140452232650148651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45125339415745240800792805 8461001140452232650148651)
    ·
      refine ⟨12691501710678348975222977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461001140452232650148651 12691501710678348975222977)
      ·
        refine ⟨9518626283008761731417233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12691501710678348975222977 9518626283008761731417233)
        ·
          refine ⟨7138969712256571298562925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518626283008761731417233 7138969712256571298562925)
          ·
            refine ⟨2677113642096214236961097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138969712256571298562925 2677113642096214236961097)
            ·
              refine ⟨2007835231572160677720823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677113642096214236961097 2007835231572160677720823)
              ·
                refine ⟨3011752847358241016581235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007835231572160677720823 3011752847358241016581235)
                ·
                  refine ⟨4517629271037361524871853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011752847358241016581235 4517629271037361524871853)
                  ·
                    refine ⟨1694110976639010571826945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4517629271037361524871853 1694110976639010571826945)
                    ·
                      refine ⟨1270583232479257928870209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694110976639010571826945 1270583232479257928870209)
                      ·
                        rfl

theorem cell23_2474452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2474452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474452 prefixEnd_2474452 := by exact prefixLift 2474452
  have htrace : WordTrace (prefixWord ++ tailWord_2474452) baseStart_2474452 baseEnd_2474452 := by
    simpa [prefixWord, tailWord_2474452, baseEnd_2474452] using wordTrace_append hprefix tailTrace_2474452
  have hstable : (prefixWord ++ tailWord_2474452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474452).length < 2 ^ (prefixWord ++ tailWord_2474452).sum := by decide
  have hdescent : baseEnd_2474452 < baseStart_2474452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474464 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_2474464 : Nat := 118140960795 + 2474464 * 2 ^ 59
def prefixEnd_2474464 : Nat := 4983230072969 + 3 ^ 40 * 2474464 * 2
def baseEnd_2474464 : Nat := 1270589394247111881920153

theorem tailTrace_2474464 : CollatzResearch.WordTrace tailWord_2474464 prefixEnd_2474464 1270589394247111881920153 := by
  unfold tailWord_2474464
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125558253723503825511223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60167411004964671767348297 45125558253723503825511223)
  ·
    refine ⟨67688337380585255738266835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125558253723503825511223 67688337380585255738266835)
    ·
      refine ⟨101532506070877883607400253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67688337380585255738266835 101532506070877883607400253)
      ·
        refine ⟨38074689776579206352775095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101532506070877883607400253 38074689776579206352775095)
        ·
          refine ⟨57112034664868809529162643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38074689776579206352775095 57112034664868809529162643)
          ·
            refine ⟨85668051997303214293743965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57112034664868809529162643 85668051997303214293743965)
            ·
              refine ⟨32125519498988705360153987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85668051997303214293743965 32125519498988705360153987)
              ·
                refine ⟨48188279248483058040230981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32125519498988705360153987 48188279248483058040230981)
                ·
                  refine ⟨9035302359090573382543309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48188279248483058040230981 9035302359090573382543309)
                  ·
                    refine ⟨3388238384658965018453741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9035302359090573382543309 3388238384658965018453741)
                    ·
                      refine ⟨1270589394247111881920153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388238384658965018453741 1270589394247111881920153)
                      ·
                        rfl

theorem cell23_2474464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_2474464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474464 prefixEnd_2474464 := by exact prefixLift 2474464
  have htrace : WordTrace (prefixWord ++ tailWord_2474464) baseStart_2474464 baseEnd_2474464 := by
    simpa [prefixWord, tailWord_2474464, baseEnd_2474464] using wordTrace_append hprefix tailTrace_2474464
  have hstable : (prefixWord ++ tailWord_2474464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474464).length < 2 ^ (prefixWord ++ tailWord_2474464).sum := by decide
  have hdescent : baseEnd_2474464 < baseStart_2474464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474471 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 5]
def baseStart_2474471 : Nat := 118140960795 + 2474471 * 2 ^ 59
def prefixEnd_2474471 : Nat := 4983230072969 + 3 ^ 40 * 2474471 * 2
def baseEnd_2474471 : Nat := 141176998734632594948069

theorem tailTrace_2474471 : CollatzResearch.WordTrace tailWord_2474471 prefixEnd_2474471 141176998734632594948069 := by
  unfold tailWord_2474471
  simp only [CollatzResearch.WordTrace]
  refine ⟨90251371818421647846527267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60167581212281098564351511 90251371818421647846527267)
  ·
    refine ⟨135377057727632471769790901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90251371818421647846527267 135377057727632471769790901)
    ·
      refine ⟨12691599161965544228417897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135377057727632471769790901 12691599161965544228417897)
      ·
        refine ⟨9518699371474158171313423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12691599161965544228417897 9518699371474158171313423)
        ·
          refine ⟨14278049057211237256970135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518699371474158171313423 14278049057211237256970135)
          ·
            refine ⟨21417073585816855885455203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14278049057211237256970135 21417073585816855885455203)
            ·
              refine ⟨32125610378725283828182805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21417073585816855885455203 32125610378725283828182805)
              ·
                refine ⟨1505887986502747679446069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32125610378725283828182805 1505887986502747679446069)
                ·
                  refine ⟨141176998734632594948069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505887986502747679446069 141176998734632594948069)
                  ·
                    rfl

theorem cell23_2474471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 5].length) (baseStart_2474471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474471 prefixEnd_2474471 := by exact prefixLift 2474471
  have htrace : WordTrace (prefixWord ++ tailWord_2474471) baseStart_2474471 baseEnd_2474471 := by
    simpa [prefixWord, tailWord_2474471, baseEnd_2474471] using wordTrace_append hprefix tailTrace_2474471
  have hstable : (prefixWord ++ tailWord_2474471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474471).length < 2 ^ (prefixWord ++ tailWord_2474471).sum := by decide
  have hdescent : baseEnd_2474471 < baseStart_2474471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474482 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2474482 : Nat := 118140960795 + 2474482 * 2 ^ 59
def prefixEnd_2474482 : Nat := 4983230072969 + 3 ^ 40 * 2474482 * 2
def baseEnd_2474482 : Nat := 1270598636898892811495071

theorem tailTrace_2474482 : CollatzResearch.WordTrace tailWord_2474482 prefixEnd_2474482 1270598636898892811495071 := by
  unfold tailWord_2474482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562943255345449181294425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60167848680921197816785133 22562943255345449181294425)
  ·
    refine ⟨16922207441509086885970819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22562943255345449181294425 16922207441509086885970819)
    ·
      refine ⟨25383311162263630328956229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16922207441509086885970819 25383311162263630328956229)
      ·
        refine ⟨4759370842924430686679293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25383311162263630328956229 4759370842924430686679293)
        ·
          refine ⟨1784764066096661507504735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4759370842924430686679293 1784764066096661507504735)
          ·
            refine ⟨2677146099144992261257103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784764066096661507504735 2677146099144992261257103)
            ·
              refine ⟨4015719148717488391885655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677146099144992261257103 4015719148717488391885655)
              ·
                refine ⟨6023578723076232587828483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015719148717488391885655 6023578723076232587828483)
                ·
                  refine ⟨9035368084614348881742725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023578723076232587828483 9035368084614348881742725)
                  ·
                    refine ⟨1694131515865190415326761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9035368084614348881742725 1694131515865190415326761)
                    ·
                      refine ⟨1270598636898892811495071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694131515865190415326761 1270598636898892811495071)
                      ·
                        rfl

theorem cell23_2474482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2474482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474482 prefixEnd_2474482 := by exact prefixLift 2474482
  have htrace : WordTrace (prefixWord ++ tailWord_2474482) baseStart_2474482 baseEnd_2474482 := by
    simpa [prefixWord, tailWord_2474482, baseEnd_2474482] using wordTrace_append hprefix tailTrace_2474482
  have hstable : (prefixWord ++ tailWord_2474482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474482).length < 2 ^ (prefixWord ++ tailWord_2474482).sum := by decide
  have hdescent : baseEnd_2474482 < baseStart_2474482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474605 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2474605 : Nat := 118140960795 + 2474605 * 2 ^ 59
def prefixEnd_2474605 : Nat := 4983230072969 + 3 ^ 40 * 2474605 * 2
def baseEnd_2474605 : Nat := 1270661795019395830257005

theorem tailTrace_2474605 : CollatzResearch.WordTrace tailWord_2474605 prefixEnd_2474605 1270661795019395830257005 := by
  unfold tailWord_2474605
  simp only [CollatzResearch.WordTrace]
  refine ⟨90256259199936188731905269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60170839466624125821270179 90256259199936188731905269)
  ·
    refine ⟨8461524299994017693616119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90256259199936188731905269 8461524299994017693616119)
    ·
      refine ⟨12692286449991026540424179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461524299994017693616119 12692286449991026540424179)
      ·
        refine ⟨19038429674986539810636269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12692286449991026540424179 19038429674986539810636269)
        ·
          refine ⟨7139411128119952428988601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19038429674986539810636269 7139411128119952428988601)
          ·
            refine ⟨5354558346089964321741451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7139411128119952428988601 5354558346089964321741451)
            ·
              refine ⟨8031837519134946482612177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354558346089964321741451 8031837519134946482612177)
              ·
                refine ⟨6023878139351209861959133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8031837519134946482612177 6023878139351209861959133)
                ·
                  refine ⟨2258954302256703698234675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6023878139351209861959133 2258954302256703698234675)
                  ·
                    refine ⟨3388431453385055547352013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2258954302256703698234675 3388431453385055547352013)
                    ·
                      refine ⟨1270661795019395830257005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388431453385055547352013 1270661795019395830257005)
                      ·
                        rfl

theorem cell23_2474605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2474605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474605 prefixEnd_2474605 := by exact prefixLift 2474605
  have htrace : WordTrace (prefixWord ++ tailWord_2474605) baseStart_2474605 baseEnd_2474605 := by
    simpa [prefixWord, tailWord_2474605, baseEnd_2474605] using wordTrace_append hprefix tailTrace_2474605
  have hstable : (prefixWord ++ tailWord_2474605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474605).length < 2 ^ (prefixWord ++ tailWord_2474605).sum := by decide
  have hdescent : baseEnd_2474605 < baseStart_2474605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474611 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 8, 2]
def baseStart_2474611 : Nat := 118140960795 + 2474611 * 2 ^ 59
def prefixEnd_2474611 : Nat := 4983230072969 + 3 ^ 40 * 2474611 * 2
def baseEnd_2474611 : Nat := 1270664875903322806781977

theorem tailTrace_2474611 : CollatzResearch.WordTrace tailWord_2474611 prefixEnd_2474611 1270664875903322806781977 := by
  unfold tailWord_2474611
  simp only [CollatzResearch.WordTrace]
  refine ⟨90256478037914451756623687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60170985358609634504415791 90256478037914451756623687)
  ·
    refine ⟨135384717056871677634935531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90256478037914451756623687 135384717056871677634935531)
    ·
      refine ⟨203077075585307516452403297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135384717056871677634935531 203077075585307516452403297)
      ·
        refine ⟨152307806688980637339302473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203077075585307516452403297 152307806688980637339302473)
        ·
          refine ⟨114230855016735478004476855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152307806688980637339302473 114230855016735478004476855)
          ·
            refine ⟨171346282525103217006715283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114230855016735478004476855 171346282525103217006715283)
            ·
              refine ⟨257019423787654825510072925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171346282525103217006715283 257019423787654825510072925)
              ·
                refine ⟨96382283920370559566277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257019423787654825510072925 96382283920370559566277347)
                ·
                  refine ⟨144573425880555839349416021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96382283920370559566277347 144573425880555839349416021)
                  ·
                    refine ⟨1694219834537763742375969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 144573425880555839349416021 1694219834537763742375969)
                    ·
                      refine ⟨1270664875903322806781977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694219834537763742375969 1270664875903322806781977)
                      ·
                        rfl

theorem cell23_2474611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8, 2].length) (baseStart_2474611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474611 prefixEnd_2474611 := by exact prefixLift 2474611
  have htrace : WordTrace (prefixWord ++ tailWord_2474611) baseStart_2474611 baseEnd_2474611 := by
    simpa [prefixWord, tailWord_2474611, baseEnd_2474611] using wordTrace_append hprefix tailTrace_2474611
  have hstable : (prefixWord ++ tailWord_2474611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474611).length < 2 ^ (prefixWord ++ tailWord_2474611).sum := by decide
  have hdescent : baseEnd_2474611 < baseStart_2474611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474631 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2474631 : Nat := 118140960795 + 2474631 * 2 ^ 59
def prefixEnd_2474631 : Nat := 4983230072969 + 3 ^ 40 * 2474631 * 2
def baseEnd_2474631 : Nat := 1270675145516412728531885

theorem tailTrace_2474631 : CollatzResearch.WordTrace tailWord_2474631 prefixEnd_2474631 1270675145516412728531885 := by
  unfold tailWord_2474631
  simp only [CollatzResearch.WordTrace]
  refine ⟨90257207497841995172351747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60171471665227996781567831 90257207497841995172351747)
  ·
    refine ⟨135385811246762992758527621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90257207497841995172351747 135385811246762992758527621)
    ·
      refine ⟨25384839608768061142223929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135385811246762992758527621 25384839608768061142223929)
      ·
        refine ⟨19038629706576045856667947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25384839608768061142223929 19038629706576045856667947)
        ·
          refine ⟨28557944559864068785001921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19038629706576045856667947 28557944559864068785001921)
          ·
            refine ⟨21418458419898051588751441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28557944559864068785001921 21418458419898051588751441)
            ·
              refine ⟨16063843814923538691563581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21418458419898051588751441 16063843814923538691563581)
              ·
                refine ⟨6023941430596327009336343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16063843814923538691563581 6023941430596327009336343)
                ·
                  refine ⟨9035912145894490514004515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023941430596327009336343 9035912145894490514004515)
                  ·
                    refine ⟨13553868218841735771006773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9035912145894490514004515 13553868218841735771006773)
                    ·
                      refine ⟨1270675145516412728531885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13553868218841735771006773 1270675145516412728531885)
                      ·
                        rfl

theorem cell23_2474631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2474631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474631 prefixEnd_2474631 := by exact prefixLift 2474631
  have htrace : WordTrace (prefixWord ++ tailWord_2474631) baseStart_2474631 baseEnd_2474631 := by
    simpa [prefixWord, tailWord_2474631, baseEnd_2474631] using wordTrace_append hprefix tailTrace_2474631
  have hstable : (prefixWord ++ tailWord_2474631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474631).length < 2 ^ (prefixWord ++ tailWord_2474631).sum := by decide
  have hdescent : baseEnd_2474631 < baseStart_2474631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474638 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2474638 : Nat := 118140960795 + 2474638 * 2 ^ 59
def prefixEnd_2474638 : Nat := 4983230072969 + 3 ^ 40 * 2474638 * 2
def baseEnd_2474638 : Nat := 423559579960331400381451

theorem tailTrace_2474638 : CollatzResearch.WordTrace tailWord_2474638 prefixEnd_2474638 423559579960331400381451 := by
  unfold tailWord_2474638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282182851102079420982071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60171641872544423578571045 11282182851102079420982071)
  ·
    refine ⟨16923274276653119131473107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282182851102079420982071 16923274276653119131473107)
    ·
      refine ⟨25384911414979678697209661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16923274276653119131473107 25384911414979678697209661)
      ·
        refine ⟨9519341780617379511453623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25384911414979678697209661 9519341780617379511453623)
        ·
          refine ⟨14279012670926069267180435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519341780617379511453623 14279012670926069267180435)
          ·
            refine ⟨21418519006389103900770653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14279012670926069267180435 21418519006389103900770653)
            ·
              refine ⟨8031944627395913962788995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21418519006389103900770653 8031944627395913962788995)
              ·
                refine ⟨12047916941093870944183493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031944627395913962788995 12047916941093870944183493)
                ·
                  refine ⟨2258984426455100802034405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12047916941093870944183493 2258984426455100802034405)
                  ·
                    refine ⟨423559579960331400381451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2258984426455100802034405 423559579960331400381451)
                    ·
                      rfl

theorem cell23_2474638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2474638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474638 prefixEnd_2474638 := by exact prefixLift 2474638
  have htrace : WordTrace (prefixWord ++ tailWord_2474638) baseStart_2474638 baseEnd_2474638 := by
    simpa [prefixWord, tailWord_2474638, baseEnd_2474638] using wordTrace_append hprefix tailTrace_2474638
  have hstable : (prefixWord ++ tailWord_2474638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474638).length < 2 ^ (prefixWord ++ tailWord_2474638).sum := by decide
  have hdescent : baseEnd_2474638 < baseStart_2474638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474712 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_2474712 : Nat := 118140960795 + 2474712 * 2 ^ 59
def prefixEnd_2474712 : Nat := 4983230072969 + 3 ^ 40 * 2474712 * 2
def baseEnd_2474712 : Nat := 1270716737449426911619013

theorem tailTrace_2474712 : CollatzResearch.WordTrace tailWord_2474712 prefixEnd_2474712 1270716737449426911619013 := by
  unfold tailWord_2474712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45130080905274273003025195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60173441207032364004033593 45130080905274273003025195)
  ·
    refine ⟨67695121357911409504537793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45130080905274273003025195 67695121357911409504537793)
    ·
      refine ⟨50771341018433557128403345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67695121357911409504537793 50771341018433557128403345)
      ·
        refine ⟨38078505763825167846302509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50771341018433557128403345 38078505763825167846302509)
        ·
          refine ⟨14279439661434437942363441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38078505763825167846302509 14279439661434437942363441)
          ·
            refine ⟨10709579746075828456772581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14279439661434437942363441 10709579746075828456772581)
            ·
              refine ⟨2008046202389217835644859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10709579746075828456772581 2008046202389217835644859)
              ·
                refine ⟨3012069303583826753467289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008046202389217835644859 3012069303583826753467289)
                ·
                  refine ⟨2259051977687870065100467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012069303583826753467289 2259051977687870065100467)
                  ·
                    refine ⟨3388577966531805097650701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259051977687870065100467 3388577966531805097650701)
                    ·
                      refine ⟨1270716737449426911619013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388577966531805097650701 1270716737449426911619013)
                      ·
                        rfl

theorem cell23_2474712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_2474712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474712 prefixEnd_2474712 := by exact prefixLift 2474712
  have htrace : WordTrace (prefixWord ++ tailWord_2474712) baseStart_2474712 baseEnd_2474712 := by
    simpa [prefixWord, tailWord_2474712, baseEnd_2474712] using wordTrace_append hprefix tailTrace_2474712
  have hstable : (prefixWord ++ tailWord_2474712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474712).length < 2 ^ (prefixWord ++ tailWord_2474712).sum := by decide
  have hdescent : baseEnd_2474712 < baseStart_2474712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474731 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_2474731 : Nat := 118140960795 + 2474731 * 2 ^ 59
def prefixEnd_2474731 : Nat := 4983230072969 + 3 ^ 40 * 2474731 * 2
def baseEnd_2474731 : Nat := 1270726493581862337281425

theorem tailTrace_2474731 : CollatzResearch.WordTrace tailWord_2474731 prefixEnd_2474731 1270726493581862337281425 := by
  unfold tailWord_2474731
  simp only [CollatzResearch.WordTrace]
  refine ⟨90260854797479712250992047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60173903198319808167328031 90260854797479712250992047)
  ·
    refine ⟨135391282196219568376488071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90260854797479712250992047 135391282196219568376488071)
    ·
      refine ⟨203086923294329352564732107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135391282196219568376488071 203086923294329352564732107)
      ·
        refine ⟨304630384941494028847098161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203086923294329352564732107 304630384941494028847098161)
        ·
          refine ⟨228472788706120521635323621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304630384941494028847098161 228472788706120521635323621)
          ·
            refine ⟨42838647882397597806623179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228472788706120521635323621 42838647882397597806623179)
            ·
              refine ⟨64257971823596396709934769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42838647882397597806623179 64257971823596396709934769)
              ·
                refine ⟨48193478867697297532451077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64257971823596396709934769 48193478867697297532451077)
                ·
                  refine ⟨9036277287693243287334577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48193478867697297532451077 9036277287693243287334577)
                  ·
                    refine ⟨6777207965769932465500933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9036277287693243287334577 6777207965769932465500933)
                    ·
                      refine ⟨1270726493581862337281425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6777207965769932465500933 1270726493581862337281425)
                      ·
                        rfl

theorem cell23_2474731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_2474731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474731 prefixEnd_2474731 := by exact prefixLift 2474731
  have htrace : WordTrace (prefixWord ++ tailWord_2474731) baseStart_2474731 baseEnd_2474731 := by
    simpa [prefixWord, tailWord_2474731, baseEnd_2474731] using wordTrace_append hprefix tailTrace_2474731
  have hstable : (prefixWord ++ tailWord_2474731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474731).length < 2 ^ (prefixWord ++ tailWord_2474731).sum := by decide
  have hdescent : baseEnd_2474731 < baseStart_2474731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474735 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 4, 2]
def baseStart_2474735 : Nat := 118140960795 + 2474735 * 2 ^ 59
def prefixEnd_2474735 : Nat := 4983230072969 + 3 ^ 40 * 2474735 * 2
def baseEnd_2474735 : Nat := 1270728547504480321631407

theorem tailTrace_2474735 : CollatzResearch.WordTrace tailWord_2474735 prefixEnd_2474735 1270728547504480321631407 := by
  unfold tailWord_2474735
  simp only [CollatzResearch.WordTrace]
  refine ⟨90261000689465220934137659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60174000459643480622758439 90261000689465220934137659)
  ·
    refine ⟨135391501034197831401206489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90261000689465220934137659 135391501034197831401206489)
    ·
      refine ⟨101543625775648373550904867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135391501034197831401206489 101543625775648373550904867)
      ·
        refine ⟨152315438663472560326357301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101543625775648373550904867 152315438663472560326357301)
        ·
          refine ⟨14279572374700552530595997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152315438663472560326357301 14279572374700552530595997)
          ·
            refine ⟨5354839640512707198973499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14279572374700552530595997 5354839640512707198973499)
            ·
              refine ⟨8032259460769060798460249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354839640512707198973499 8032259460769060798460249)
              ·
                refine ⟨6024194595576795598845187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032259460769060798460249 6024194595576795598845187)
                ·
                  refine ⟨9036291893365193398267781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6024194595576795598845187 9036291893365193398267781)
                  ·
                    refine ⟨1694304730005973762175209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9036291893365193398267781 1694304730005973762175209)
                    ·
                      refine ⟨1270728547504480321631407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694304730005973762175209 1270728547504480321631407)
                      ·
                        rfl

theorem cell23_2474735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4, 2].length) (baseStart_2474735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474735 prefixEnd_2474735 := by exact prefixLift 2474735
  have htrace : WordTrace (prefixWord ++ tailWord_2474735) baseStart_2474735 baseEnd_2474735 := by
    simpa [prefixWord, tailWord_2474735, baseEnd_2474735] using wordTrace_append hprefix tailTrace_2474735
  have hstable : (prefixWord ++ tailWord_2474735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474735).length < 2 ^ (prefixWord ++ tailWord_2474735).sum := by decide
  have hdescent : baseEnd_2474735 < baseStart_2474735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474738 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2474738 : Nat := 118140960795 + 2474738 * 2 ^ 59
def prefixEnd_2474738 : Nat := 4983230072969 + 3 ^ 40 * 2474738 * 2
def baseEnd_2474738 : Nat := 1270730087946443809893893

theorem tailTrace_2474738 : CollatzResearch.WordTrace tailWord_2474738 prefixEnd_2474738 1270730087946443809893893 := by
  unfold tailWord_2474738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22565277527113588111624217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60174073405636234964331245 22565277527113588111624217)
  ·
    refine ⟨16923958145335191083718163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22565277527113588111624217 16923958145335191083718163)
    ·
      refine ⟨25385937218002786625577245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16923958145335191083718163 25385937218002786625577245)
      ·
        refine ⟨9519726456751044984591467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25385937218002786625577245 9519726456751044984591467)
        ·
          refine ⟨14279589685126567476887201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519726456751044984591467 14279589685126567476887201)
          ·
            refine ⟨10709692263844925607665401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14279589685126567476887201 10709692263844925607665401)
            ·
              refine ⟨8032269197883694205749051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10709692263844925607665401 8032269197883694205749051)
              ·
                refine ⟨12048403796825541308623577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032269197883694205749051 12048403796825541308623577)
                ·
                  refine ⟨9036302847619155981467683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12048403796825541308623577 9036302847619155981467683)
                  ·
                    refine ⟨13554454271428733972201525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9036302847619155981467683 13554454271428733972201525)
                    ·
                      refine ⟨1270730087946443809893893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13554454271428733972201525 1270730087946443809893893)
                      ·
                        rfl

theorem cell23_2474738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2474738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474738 prefixEnd_2474738 := by exact prefixLift 2474738
  have htrace : WordTrace (prefixWord ++ tailWord_2474738) baseStart_2474738 baseEnd_2474738 := by
    simpa [prefixWord, tailWord_2474738, baseEnd_2474738] using wordTrace_append hprefix tailTrace_2474738
  have hstable : (prefixWord ++ tailWord_2474738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474738).length < 2 ^ (prefixWord ++ tailWord_2474738).sum := by decide
  have hdescent : baseEnd_2474738 < baseStart_2474738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474771 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 7]
def baseStart_2474771 : Nat := 118140960795 + 2474771 * 2 ^ 59
def prefixEnd_2474771 : Nat := 4983230072969 + 3 ^ 40 * 2474771 * 2
def baseEnd_2474771 : Nat := 423582344269347393593747

theorem tailTrace_2474771 : CollatzResearch.WordTrace tailWord_2474771 prefixEnd_2474771 423582344269347393593747 := by
  unfold tailWord_2474771
  simp only [CollatzResearch.WordTrace]
  refine ⟨90262313717334799082448167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60174875811556532721632111 90262313717334799082448167)
  ·
    refine ⟨135393470576002198623672251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90262313717334799082448167 135393470576002198623672251)
    ·
      refine ⟨203090205864003297935508377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135393470576002198623672251 203090205864003297935508377)
      ·
        refine ⟨152317654398002473451631283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203090205864003297935508377 152317654398002473451631283)
        ·
          refine ⟨228476481597003710177446925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152317654398002473451631283 228476481597003710177446925)
          ·
            refine ⟨85678680598876391316542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228476481597003710177446925 85678680598876391316542597)
            ·
              refine ⟨16064752612289323371851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85678680598876391316542597 16064752612289323371851737)
              ·
                refine ⟨12048564459216992528888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16064752612289323371851737 12048564459216992528888803)
                ·
                  refine ⟨18072846688825488793333205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12048564459216992528888803 18072846688825488793333205)
                  ·
                    refine ⟨423582344269347393593747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18072846688825488793333205 423582344269347393593747)
                    ·
                      rfl

theorem cell23_2474771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_2474771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474771 prefixEnd_2474771 := by exact prefixLift 2474771
  have htrace : WordTrace (prefixWord ++ tailWord_2474771) baseStart_2474771 baseEnd_2474771 := by
    simpa [prefixWord, tailWord_2474771, baseEnd_2474771] using wordTrace_append hprefix tailTrace_2474771
  have hstable : (prefixWord ++ tailWord_2474771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474771).length < 2 ^ (prefixWord ++ tailWord_2474771).sum := by decide
  have hdescent : baseEnd_2474771 < baseStart_2474771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474808 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2474808 : Nat := 118140960795 + 2474808 * 2 ^ 59
def prefixEnd_2474808 : Nat := 4983230072969 + 3 ^ 40 * 2474808 * 2
def baseEnd_2474808 : Nat := 1270766031592258536018571

theorem tailTrace_2474808 : CollatzResearch.WordTrace tailWord_2474808 prefixEnd_2474808 1270766031592258536018571 := by
  unfold tailWord_2474808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45131831609100377200772539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60175775478800502934363385 45131831609100377200772539)
  ·
    refine ⟨67697747413650565801158809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45131831609100377200772539 67697747413650565801158809)
    ·
      refine ⟨50773310560237924350869107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67697747413650565801158809 50773310560237924350869107)
      ·
        refine ⟨76159965840356886526303661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50773310560237924350869107 76159965840356886526303661)
        ·
          refine ⟨28559987190133832447363873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76159965840356886526303661 28559987190133832447363873)
          ·
            refine ⟨21419990392600374335522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28559987190133832447363873 21419990392600374335522905)
            ·
              refine ⟨16064992794450280751642179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21419990392600374335522905 16064992794450280751642179)
              ·
                refine ⟨24097489191675421127463269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16064992794450280751642179 24097489191675421127463269)
                ·
                  refine ⟨4518279223439141461399363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24097489191675421127463269 4518279223439141461399363)
                  ·
                    refine ⟨6777418835158712192099045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518279223439141461399363 6777418835158712192099045)
                    ·
                      refine ⟨1270766031592258536018571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6777418835158712192099045 1270766031592258536018571)
                      ·
                        rfl

theorem cell23_2474808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2474808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474808 prefixEnd_2474808 := by exact prefixLift 2474808
  have htrace : WordTrace (prefixWord ++ tailWord_2474808) baseStart_2474808 baseEnd_2474808 := by
    simpa [prefixWord, tailWord_2474808, baseEnd_2474808] using wordTrace_append hprefix tailTrace_2474808
  have hstable : (prefixWord ++ tailWord_2474808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474808).length < 2 ^ (prefixWord ++ tailWord_2474808).sum := by decide
  have hdescent : baseEnd_2474808 < baseStart_2474808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474825 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 4, 2]
def baseStart_2474825 : Nat := 118140960795 + 2474825 * 2 ^ 59
def prefixEnd_2474825 : Nat := 4983230072969 + 3 ^ 40 * 2474825 * 2
def baseEnd_2474825 : Nat := 1270774760763384969505993

theorem tailTrace_2474825 : CollatzResearch.WordTrace tailWord_2474825 prefixEnd_2474825 1270774760763384969505993 := by
  unfold tailWord_2474825
  simp only [CollatzResearch.WordTrace]
  refine ⟨90264283259139166304913929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60176188839426110869942619 90264283259139166304913929)
  ·
    refine ⟨67698212444354374728685447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90264283259139166304913929 67698212444354374728685447)
    ·
      refine ⟨101547318666531562093028171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67698212444354374728685447 101547318666531562093028171)
      ·
        refine ⟨152320977999797343139542257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101547318666531562093028171 152320977999797343139542257)
        ·
          refine ⟨114240733499848007354656693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152320977999797343139542257 114240733499848007354656693)
          ·
            refine ⟨10710068765610750689499065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114240733499848007354656693 10710068765610750689499065)
            ·
              refine ⟨8032551574208063017124299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710068765610750689499065 8032551574208063017124299)
              ·
                refine ⟨12048827361312094525686449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032551574208063017124299 12048827361312094525686449)
                ·
                  refine ⟨9036620520984070894264837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12048827361312094525686449 9036620520984070894264837)
                  ·
                    refine ⟨1694366347684513292674657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9036620520984070894264837 1694366347684513292674657)
                    ·
                      refine ⟨1270774760763384969505993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694366347684513292674657 1270774760763384969505993)
                      ·
                        rfl

theorem cell23_2474825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4, 2].length) (baseStart_2474825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474825 prefixEnd_2474825 := by exact prefixLift 2474825
  have htrace : WordTrace (prefixWord ++ tailWord_2474825) baseStart_2474825 baseEnd_2474825 := by
    simpa [prefixWord, tailWord_2474825, baseEnd_2474825] using wordTrace_append hprefix tailTrace_2474825
  have hstable : (prefixWord ++ tailWord_2474825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474825).length < 2 ^ (prefixWord ++ tailWord_2474825).sum := by decide
  have hdescent : baseEnd_2474825 < baseStart_2474825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474909 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_2474909 : Nat := 118140960795 + 2474909 * 2 ^ 59
def prefixEnd_2474909 : Nat := 4983230072969 + 3 ^ 40 * 2474909 * 2
def baseEnd_2474909 : Nat := 1270817893138362640855607

theorem tailTrace_2474909 : CollatzResearch.WordTrace tailWord_2474909 prefixEnd_2474909 1270817893138362640855607 := by
  unfold tailWord_2474909
  simp only [CollatzResearch.WordTrace]
  refine ⟨90267346990834848650971781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60178231327223232433981187 90267346990834848650971781)
  ·
    refine ⟨16925127560781534122057209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90267346990834848650971781 16925127560781534122057209)
    ·
      refine ⟨12693845670586150591542907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16925127560781534122057209 12693845670586150591542907)
      ·
        refine ⟨19040768505879225887314361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12693845670586150591542907 19040768505879225887314361)
        ·
          refine ⟨14280576379409419415485771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19040768505879225887314361 14280576379409419415485771)
          ·
            refine ⟨21420864569114129123228657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14280576379409419415485771 21420864569114129123228657)
            ·
              refine ⟨16065648426835596842421493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21420864569114129123228657 16065648426835596842421493)
              ·
                refine ⟨1506154540015837203977015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16065648426835596842421493 1506154540015837203977015)
                ·
                  refine ⟨2259231810023755805965523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506154540015837203977015 2259231810023755805965523)
                  ·
                    refine ⟨3388847715035633708948285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259231810023755805965523 3388847715035633708948285)
                    ·
                      refine ⟨1270817893138362640855607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388847715035633708948285 1270817893138362640855607)
                      ·
                        rfl

theorem cell23_2474909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_2474909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474909 prefixEnd_2474909 := by exact prefixLift 2474909
  have htrace : WordTrace (prefixWord ++ tailWord_2474909) baseStart_2474909 baseEnd_2474909 := by
    simpa [prefixWord, tailWord_2474909, baseEnd_2474909] using wordTrace_append hprefix tailTrace_2474909
  have hstable : (prefixWord ++ tailWord_2474909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474909).length < 2 ^ (prefixWord ++ tailWord_2474909).sum := by decide
  have hdescent : baseEnd_2474909 < baseStart_2474909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474915 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 4]
def baseStart_2474915 : Nat := 118140960795 + 2474915 * 2 ^ 59
def prefixEnd_2474915 : Nat := 4983230072969 + 3 ^ 40 * 2474915 * 2
def baseEnd_2474915 : Nat := 1270820974022289617380579

theorem tailTrace_2474915 : CollatzResearch.WordTrace tailWord_2474915 prefixEnd_2474915 1270820974022289617380579 := by
  unfold tailWord_2474915
  simp only [CollatzResearch.WordTrace]
  refine ⟨90267565828813111675690199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60178377219208741117126799 90267565828813111675690199)
  ·
    refine ⟨135401348743219667513535299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90267565828813111675690199 135401348743219667513535299)
    ·
      refine ⟨203102023114829501270302949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135401348743219667513535299 203102023114829501270302949)
      ·
        refine ⟨38081629334030531488181803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203102023114829501270302949 38081629334030531488181803)
        ·
          refine ⟨57122444001045797232272705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38081629334030531488181803 57122444001045797232272705)
          ·
            refine ⟨42841833000784347924204529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57122444001045797232272705 42841833000784347924204529)
            ·
              refine ⟨32131374750588260943153397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42841833000784347924204529 32131374750588260943153397)
              ·
                refine ⟨3012316382867649463420631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32131374750588260943153397 3012316382867649463420631)
                ·
                  refine ⟨4518474574301474195130947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012316382867649463420631 4518474574301474195130947)
                  ·
                    refine ⟨6777711861452211292696421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518474574301474195130947 6777711861452211292696421)
                    ·
                      refine ⟨1270820974022289617380579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6777711861452211292696421 1270820974022289617380579)
                      ·
                        rfl

theorem cell23_2474915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_2474915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474915 prefixEnd_2474915 := by exact prefixLift 2474915
  have htrace : WordTrace (prefixWord ++ tailWord_2474915) baseStart_2474915 baseEnd_2474915 := by
    simpa [prefixWord, tailWord_2474915, baseEnd_2474915] using wordTrace_append hprefix tailTrace_2474915
  have hstable : (prefixWord ++ tailWord_2474915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474915).length < 2 ^ (prefixWord ++ tailWord_2474915).sum := by decide
  have hdescent : baseEnd_2474915 < baseStart_2474915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474935 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_2474935 : Nat := 118140960795 + 2474935 * 2 ^ 59
def prefixEnd_2474935 : Nat := 4983230072969 + 3 ^ 40 * 2474935 * 2
def baseEnd_2474935 : Nat := 1270831243635379539130487

theorem tailTrace_2474935 : CollatzResearch.WordTrace tailWord_2474935 prefixEnd_2474935 1270831243635379539130487 := by
  unfold tailWord_2474935
  simp only [CollatzResearch.WordTrace]
  refine ⟨90268295288740655091418259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60178863525827103394278839 90268295288740655091418259)
  ·
    refine ⟨135402442933110982637127389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90268295288740655091418259 135402442933110982637127389)
    ·
      refine ⟨50775916099916618488922771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135402442933110982637127389 50775916099916618488922771)
      ·
        refine ⟨76163874149874927733384157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50775916099916618488922771 76163874149874927733384157)
        ·
          refine ⟨28561452806203097900019059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76163874149874927733384157 28561452806203097900019059)
          ·
            refine ⟨42842179209304646850028589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28561452806203097900019059 42842179209304646850028589)
            ·
              refine ⟨16065817203489242568760721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42842179209304646850028589 16065817203489242568760721)
              ·
                refine ⟨12049362902616931926570541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16065817203489242568760721 12049362902616931926570541)
                ·
                  refine ⟨4518511088481349472463953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12049362902616931926570541 4518511088481349472463953)
                  ·
                    refine ⟨3388883316361012104347965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518511088481349472463953 3388883316361012104347965)
                    ·
                      refine ⟨1270831243635379539130487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388883316361012104347965 1270831243635379539130487)
                      ·
                        rfl

theorem cell23_2474935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_2474935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474935 prefixEnd_2474935 := by exact prefixLift 2474935
  have htrace : WordTrace (prefixWord ++ tailWord_2474935) baseStart_2474935 baseEnd_2474935 := by
    simpa [prefixWord, tailWord_2474935, baseEnd_2474935] using wordTrace_append hprefix tailTrace_2474935
  have hstable : (prefixWord ++ tailWord_2474935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474935).length < 2 ^ (prefixWord ++ tailWord_2474935).sum := by decide
  have hdescent : baseEnd_2474935 < baseStart_2474935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474942 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2474942 : Nat := 118140960795 + 2474942 * 2 ^ 59
def prefixEnd_2474942 : Nat := 4983230072969 + 3 ^ 40 * 2474942 * 2
def baseEnd_2474942 : Nat := 423611612666653670580985

theorem tailTrace_2474942 : CollatzResearch.WordTrace tailWord_2474942 prefixEnd_2474942 423611612666653670580985 := by
  unfold tailWord_2474942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283568824964411910865385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60179033733143530191282053 11283568824964411910865385)
  ·
    refine ⟨8462676618723308933149039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11283568824964411910865385 8462676618723308933149039)
    ·
      refine ⟨12694014928084963399723559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462676618723308933149039 12694014928084963399723559)
      ·
        refine ⟨19041022392127445099585339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694014928084963399723559 19041022392127445099585339)
        ·
          refine ⟨28561533588191167649378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19041022392127445099585339 28561533588191167649378009)
          ·
            refine ⟨21421150191143375737033507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28561533588191167649378009 21421150191143375737033507)
            ·
              refine ⟨32131725286715063605550261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21421150191143375737033507 32131725286715063605550261)
              ·
                refine ⟨3012349245629537213020337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32131725286715063605550261 3012349245629537213020337)
                ·
                  refine ⟨2259261934222152909765253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012349245629537213020337 2259261934222152909765253)
                  ·
                    refine ⟨423611612666653670580985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259261934222152909765253 423611612666653670580985)
                    ·
                      rfl

theorem cell23_2474942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2474942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474942 prefixEnd_2474942 := by exact prefixLift 2474942
  have htrace : WordTrace (prefixWord ++ tailWord_2474942) baseStart_2474942 baseEnd_2474942 := by
    simpa [prefixWord, tailWord_2474942, baseEnd_2474942] using wordTrace_append hprefix tailTrace_2474942
  have hstable : (prefixWord ++ tailWord_2474942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474942).length < 2 ^ (prefixWord ++ tailWord_2474942).sum := by decide
  have hdescent : baseEnd_2474942 < baseStart_2474942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474955 : List Nat := [1, 1, 1, 1, 3, 6, 3, 7]
def baseStart_2474955 : Nat := 118140960795 + 2474955 * 2 ^ 59
def prefixEnd_2474955 : Nat := 4983230072969 + 3 ^ 40 * 2474955 * 2
def baseEnd_2474955 : Nat := 47068204194387757810385

theorem tailTrace_2474955 : CollatzResearch.WordTrace tailWord_2474955 prefixEnd_2474955 47068204194387757810385 := by
  unfold tailWord_2474955
  simp only [CollatzResearch.WordTrace]
  refine ⟨90269024748668198507146319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60179349832445465671430879 90269024748668198507146319)
  ·
    refine ⟨135403537123002297760719479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90269024748668198507146319 135403537123002297760719479)
    ·
      refine ⟨203105305684503446641079219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135403537123002297760719479 203105305684503446641079219)
      ·
        refine ⟨304657958526755169961618829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203105305684503446641079219 304657958526755169961618829)
        ·
          refine ⟨114246734447533188735607061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304657958526755169961618829 114246734447533188735607061)
          ·
            refine ⟨5355315677228118221981581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114246734447533188735607061 5355315677228118221981581)
            ·
              refine ⟨2008243378960544333243093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5355315677228118221981581 2008243378960544333243093)
              ·
                refine ⟨47068204194387757810385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2008243378960544333243093 47068204194387757810385)
                ·
                  rfl

theorem cell23_2474955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 7].length) (baseStart_2474955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474955 prefixEnd_2474955 := by exact prefixLift 2474955
  have htrace : WordTrace (prefixWord ++ tailWord_2474955) baseStart_2474955 baseEnd_2474955 := by
    simpa [prefixWord, tailWord_2474955, baseEnd_2474955] using wordTrace_append hprefix tailTrace_2474955
  have hstable : (prefixWord ++ tailWord_2474955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474955).length < 2 ^ (prefixWord ++ tailWord_2474955).sum := by decide
  have hdescent : baseEnd_2474955 < baseStart_2474955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474962 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2474962 : Nat := 118140960795 + 2474962 * 2 ^ 59
def prefixEnd_2474962 : Nat := 4983230072969 + 3 ^ 40 * 2474962 * 2
def baseEnd_2474962 : Nat := 1270845107613050933492863

theorem tailTrace_2474962 : CollatzResearch.WordTrace tailWord_2474962 prefixEnd_2474962 1270845107613050933492863 := by
  unfold tailWord_2474962
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567320014910709675662785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60179520039761892468434093 22567320014910709675662785)
  ·
    refine ⟨16925490011183032256747089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22567320014910709675662785 16925490011183032256747089)
    ·
      refine ⟨12694117508387274192560317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16925490011183032256747089 12694117508387274192560317)
      ·
        refine ⟨4760294065645227822210119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12694117508387274192560317 4760294065645227822210119)
        ·
          refine ⟨7140441098467841733315179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760294065645227822210119 7140441098467841733315179)
          ·
            refine ⟨10710661647701762599972769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140441098467841733315179 10710661647701762599972769)
            ·
              refine ⟨8032996235776321949979577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710661647701762599972769 8032996235776321949979577)
              ·
                refine ⟨6024747176832241462484683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032996235776321949979577 6024747176832241462484683)
                ·
                  refine ⟨9037120765248362193727025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6024747176832241462484683 9037120765248362193727025)
                  ·
                    refine ⟨6777840573936271645295269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9037120765248362193727025 6777840573936271645295269)
                    ·
                      refine ⟨1270845107613050933492863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6777840573936271645295269 1270845107613050933492863)
                      ·
                        rfl

theorem cell23_2474962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2474962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474962 prefixEnd_2474962 := by exact prefixLift 2474962
  have htrace : WordTrace (prefixWord ++ tailWord_2474962) baseStart_2474962 baseEnd_2474962 := by
    simpa [prefixWord, tailWord_2474962, baseEnd_2474962] using wordTrace_append hprefix tailTrace_2474962
  have hstable : (prefixWord ++ tailWord_2474962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474962).length < 2 ^ (prefixWord ++ tailWord_2474962).sum := by decide
  have hdescent : baseEnd_2474962 < baseStart_2474962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474966 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2474966 : Nat := 118140960795 + 2474966 * 2 ^ 59
def prefixEnd_2474966 : Nat := 4983230072969 + 3 ^ 40 * 2474966 * 2
def baseEnd_2474966 : Nat := 1270847161535668917842845

theorem tailTrace_2474966 : CollatzResearch.WordTrace tailWord_2474966 prefixEnd_2474966 1270847161535668917842845 := by
  unfold tailWord_2474966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641839121976771711612297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60179617301085564923864501 5641839121976771711612297)
  ·
    refine ⟨4231379341482578783709223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5641839121976771711612297 4231379341482578783709223)
    ·
      refine ⟨6347069012223868175563835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231379341482578783709223 6347069012223868175563835)
      ·
        refine ⟨9520603518335802263345753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347069012223868175563835 9520603518335802263345753)
        ·
          refine ⟨7140452638751851697509315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9520603518335802263345753 7140452638751851697509315)
          ·
            refine ⟨10710678958127777546263973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140452638751851697509315 10710678958127777546263973)
            ·
              refine ⟨2008252304648958289924495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10710678958127777546263973 2008252304648958289924495)
              ·
                refine ⟨3012378456973437434886743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008252304648958289924495 3012378456973437434886743)
                ·
                  refine ⟨4518567685460156152330115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012378456973437434886743 4518567685460156152330115)
                  ·
                    refine ⟨6777851528190234228495173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518567685460156152330115 6777851528190234228495173)
                    ·
                      refine ⟨1270847161535668917842845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6777851528190234228495173 1270847161535668917842845)
                      ·
                        rfl

theorem cell23_2474966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2474966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474966 prefixEnd_2474966 := by exact prefixLift 2474966
  have htrace : WordTrace (prefixWord ++ tailWord_2474966) baseStart_2474966 baseEnd_2474966 := by
    simpa [prefixWord, tailWord_2474966, baseEnd_2474966] using wordTrace_append hprefix tailTrace_2474966
  have hstable : (prefixWord ++ tailWord_2474966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474966).length < 2 ^ (prefixWord ++ tailWord_2474966).sum := by decide
  have hdescent : baseEnd_2474966 < baseStart_2474966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474969 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 1, 2, 3]
def baseStart_2474969 : Nat := 118140960795 + 2474969 * 2 ^ 59
def prefixEnd_2474969 : Nat := 4983230072969 + 3 ^ 40 * 2474969 * 2
def baseEnd_2474969 : Nat := 1270848701977632406105331

theorem tailTrace_2474969 : CollatzResearch.WordTrace tailWord_2474969 prefixEnd_2474969 1270848701977632406105331 := by
  unfold tailWord_2474969
  simp only [CollatzResearch.WordTrace]
  refine ⟨90269535370617478898155961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60179690247078319265437307 90269535370617478898155961)
  ·
    refine ⟨67702151527963109173616971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90269535370617478898155961 67702151527963109173616971)
    ·
      refine ⟨101553227291944663760425457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67702151527963109173616971 101553227291944663760425457)
      ·
        refine ⟨76164920468958497820319093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101553227291944663760425457 76164920468958497820319093)
        ·
          refine ⟨7140461293964859170654915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76164920468958497820319093 7140461293964859170654915)
          ·
            refine ⟨10710691940947288755982373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140461293964859170654915 10710691940947288755982373)
            ·
              refine ⟨2008254738927616641746695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10710691940947288755982373 2008254738927616641746695)
              ·
                refine ⟨3012382108391424962620043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008254738927616641746695 3012382108391424962620043)
                ·
                  refine ⟨4518573162587137443930065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012382108391424962620043 4518573162587137443930065)
                  ·
                    refine ⟨3388929871940353082947549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518573162587137443930065 3388929871940353082947549)
                    ·
                      refine ⟨1270848701977632406105331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3388929871940353082947549 1270848701977632406105331)
                      ·
                        rfl

theorem cell23_2474969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_2474969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2474969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2474969 prefixEnd_2474969 := by exact prefixLift 2474969
  have htrace : WordTrace (prefixWord ++ tailWord_2474969) baseStart_2474969 baseEnd_2474969 := by
    simpa [prefixWord, tailWord_2474969, baseEnd_2474969] using wordTrace_append hprefix tailTrace_2474969
  have hstable : (prefixWord ++ tailWord_2474969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474969).length < 2 ^ (prefixWord ++ tailWord_2474969).sum := by decide
  have hdescent : baseEnd_2474969 < baseStart_2474969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475006 : List Nat := [4, 2, 2, 2, 3, 1, 2, 7]
def baseStart_2475006 : Nat := 118140960795 + 2475006 * 2 ^ 59
def prefixEnd_2475006 : Nat := 4983230072969 + 3 ^ 40 * 2475006 * 2
def baseEnd_2475006 : Nat := 47069174102290694864543

theorem tailTrace_2475006 : CollatzResearch.WordTrace tailWord_2475006 prefixEnd_2475006 47069174102290694864543 := by
  unfold tailWord_2475006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283860608935429277156609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60180589914322289478168581 11283860608935429277156609)
  ·
    refine ⟨8462895456701571957867457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11283860608935429277156609 8462895456701571957867457)
    ·
      refine ⟨6347171592526178968400593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8462895456701571957867457 6347171592526178968400593)
      ·
        refine ⟨4760378694394634226300445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6347171592526178968400593 4760378694394634226300445)
        ·
          refine ⟨1785142010397987834862667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4760378694394634226300445 1785142010397987834862667)
          ·
            refine ⟨2677713015596981752294001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785142010397987834862667 2677713015596981752294001)
            ·
              refine ⟨2008284761697736314220501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677713015596981752294001 2008284761697736314220501)
              ·
                refine ⟨47069174102290694864543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2008284761697736314220501 47069174102290694864543)
                ·
                  rfl

theorem cell23_2475006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_2475006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475006 prefixEnd_2475006 := by exact prefixLift 2475006
  have htrace : WordTrace (prefixWord ++ tailWord_2475006) baseStart_2475006 baseEnd_2475006 := by
    simpa [prefixWord, tailWord_2475006, baseEnd_2475006] using wordTrace_append hprefix tailTrace_2475006
  have hstable : (prefixWord ++ tailWord_2475006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475006).length < 2 ^ (prefixWord ++ tailWord_2475006).sum := by decide
  have hdescent : baseEnd_2475006 < baseStart_2475006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475009 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_2475009 : Nat := 118140960795 + 2475009 * 2 ^ 59
def prefixEnd_2475009 : Nat := 4983230072969 + 3 ^ 40 * 2475009 * 2
def baseEnd_2475009 : Nat := 1270869241203812249605147

theorem tailTrace_2475009 : CollatzResearch.WordTrace tailWord_2475009 prefixEnd_2475009 1270869241203812249605147 := by
  unfold tailWord_2475009
  simp only [CollatzResearch.WordTrace]
  refine ⟨90270994290472565729612081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60180662860315043819741387 90270994290472565729612081)
  ·
    refine ⟨67703245717854424297209061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90270994290472565729612081 67703245717854424297209061)
    ·
      refine ⟨12694358572097704555726699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67703245717854424297209061 12694358572097704555726699)
      ·
        refine ⟨19041537858146556833590049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694358572097704555726699 19041537858146556833590049)
        ·
          refine ⟨14281153393609917625192537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19041537858146556833590049 14281153393609917625192537)
          ·
            refine ⟨10710865045207438218894403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14281153393609917625192537 10710865045207438218894403)
            ·
              refine ⟨16066297567811157328341605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10710865045207438218894403 16066297567811157328341605)
              ·
                refine ⟨3012430793964591999064051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16066297567811157328341605 3012430793964591999064051)
                ·
                  refine ⟨4518646190946887998596077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012430793964591999064051 4518646190946887998596077)
                  ·
                    refine ⟨1694492321605082999473529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4518646190946887998596077 1694492321605082999473529)
                    ·
                      refine ⟨1270869241203812249605147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694492321605082999473529 1270869241203812249605147)
                      ·
                        rfl

theorem cell23_2475009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_2475009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475009 prefixEnd_2475009 := by exact prefixLift 2475009
  have htrace : WordTrace (prefixWord ++ tailWord_2475009) baseStart_2475009 baseEnd_2475009 := by
    simpa [prefixWord, tailWord_2475009, baseEnd_2475009] using wordTrace_append hprefix tailTrace_2475009
  have hstable : (prefixWord ++ tailWord_2475009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475009).length < 2 ^ (prefixWord ++ tailWord_2475009).sum := by decide
  have hdescent : baseEnd_2475009 < baseStart_2475009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475039 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 4, 2, 2]
def baseStart_2475039 : Nat := 118140960795 + 2475039 * 2 ^ 59
def prefixEnd_2475039 : Nat := 4983230072969 + 3 ^ 40 * 2475039 * 2
def baseEnd_2475039 : Nat := 1270884645623447132230009

theorem tailTrace_2475039 : CollatzResearch.WordTrace tailWord_2475039 prefixEnd_2475039 1270884645623447132230009 := by
  unfold tailWord_2475039
  simp only [CollatzResearch.WordTrace]
  refine ⟨90272088480363880853204171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60181392320242587235469447 90272088480363880853204171)
  ·
    refine ⟨135408132720545821279806257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90272088480363880853204171 135408132720545821279806257)
    ·
      refine ⟨101556099540409365959854693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135408132720545821279806257 101556099540409365959854693)
      ·
        refine ⟨19041768663826756117472755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101556099540409365959854693 19041768663826756117472755)
        ·
          refine ⟨28562652995740134176209133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19041768663826756117472755 28562652995740134176209133)
          ·
            refine ⟨10710994873402550316078425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28562652995740134176209133 10710994873402550316078425)
            ·
              refine ⟨8033246155051912737058819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710994873402550316078425 8033246155051912737058819)
              ·
                refine ⟨12049869232577869105588229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033246155051912737058819 12049869232577869105588229)
                ·
                  refine ⟨2259350481108350457297793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12049869232577869105588229 2259350481108350457297793)
                  ·
                    refine ⟨1694512860831262842973345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259350481108350457297793 1694512860831262842973345)
                    ·
                      refine ⟨1270884645623447132230009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694512860831262842973345 1270884645623447132230009)
                      ·
                        rfl

theorem cell23_2475039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_2475039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475039 prefixEnd_2475039 := by exact prefixLift 2475039
  have htrace : WordTrace (prefixWord ++ tailWord_2475039) baseStart_2475039 baseEnd_2475039 := by
    simpa [prefixWord, tailWord_2475039, baseEnd_2475039] using wordTrace_append hprefix tailTrace_2475039
  have hstable : (prefixWord ++ tailWord_2475039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475039).length < 2 ^ (prefixWord ++ tailWord_2475039).sum := by decide
  have hdescent : baseEnd_2475039 < baseStart_2475039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475050 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2475050 : Nat := 118140960795 + 2475050 * 2 ^ 59
def prefixEnd_2475050 : Nat := 4983230072969 + 3 ^ 40 * 2475050 * 2
def baseEnd_2475050 : Nat := 1270890293910646589192459

theorem tailTrace_2475050 : CollatzResearch.WordTrace tailWord_2475050 prefixEnd_2475050 1270890293910646589192459 := by
  unfold tailWord_2475050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568122420831007432963651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60181659788882686487903069 22568122420831007432963651)
  ·
    refine ⟨33852183631246511149445477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22568122420831007432963651 33852183631246511149445477)
    ·
      refine ⟨6347284430858720840521027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33852183631246511149445477 6347284430858720840521027)
      ·
        refine ⟨9520926646288081260781541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347284430858720840521027 9520926646288081260781541)
        ·
          refine ⟨1785173746179015236396539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9520926646288081260781541 1785173746179015236396539)
          ·
            refine ⟨2677760619268522854594809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785173746179015236396539 2677760619268522854594809)
            ·
              refine ⟨2008320464451392140946107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677760619268522854594809 2008320464451392140946107)
              ·
                refine ⟨3012480696677088211419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008320464451392140946107 3012480696677088211419161)
                ·
                  refine ⟨2259360522507816158564371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012480696677088211419161 2259360522507816158564371)
                  ·
                    refine ⟨3389040783761724237846557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259360522507816158564371 3389040783761724237846557)
                    ·
                      refine ⟨1270890293910646589192459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3389040783761724237846557 1270890293910646589192459)
                      ·
                        rfl

theorem cell23_2475050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2475050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475050 prefixEnd_2475050 := by exact prefixLift 2475050
  have htrace : WordTrace (prefixWord ++ tailWord_2475050) baseStart_2475050 baseEnd_2475050 := by
    simpa [prefixWord, tailWord_2475050, baseEnd_2475050] using wordTrace_append hprefix tailTrace_2475050
  have hstable : (prefixWord ++ tailWord_2475050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475050).length < 2 ^ (prefixWord ++ tailWord_2475050).sum := by decide
  have hdescent : baseEnd_2475050 < baseStart_2475050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475055 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_2475055 : Nat := 118140960795 + 2475055 * 2 ^ 59
def prefixEnd_2475055 : Nat := 4983230072969 + 3 ^ 40 * 2475055 * 2
def baseEnd_2475055 : Nat := 1270892861313919069629935

theorem tailTrace_2475055 : CollatzResearch.WordTrace tailWord_2475055 prefixEnd_2475055 1270892861313919069629935 := by
  unfold tailWord_2475055
  simp only [CollatzResearch.WordTrace]
  refine ⟨90272672048305915585786619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60181781365537277057191079 90272672048305915585786619)
  ·
    refine ⟨135409008072458873378679929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90272672048305915585786619 135409008072458873378679929)
    ·
      refine ⟨101556756054344155034009947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135409008072458873378679929 101556756054344155034009947)
      ·
        refine ⟨152335134081516232551014921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101556756054344155034009947 152335134081516232551014921)
        ·
          refine ⟨114251350561137174413261191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152335134081516232551014921 114251350561137174413261191)
          ·
            refine ⟨171377025841705761619891787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114251350561137174413261191 171377025841705761619891787)
            ·
              refine ⟨257065538762558642429837681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171377025841705761619891787 257065538762558642429837681)
              ·
                refine ⟨192799154071918981822378261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257065538762558642429837681 192799154071918981822378261)
                ·
                  refine ⟨9037460347121202272923981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192799154071918981822378261 9037460347121202272923981)
                  ·
                    refine ⟨3389047630170450852346493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9037460347121202272923981 3389047630170450852346493)
                    ·
                      refine ⟨1270892861313919069629935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3389047630170450852346493 1270892861313919069629935)
                      ·
                        rfl

theorem cell23_2475055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_2475055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475055 prefixEnd_2475055 := by exact prefixLift 2475055
  have htrace : WordTrace (prefixWord ++ tailWord_2475055) baseStart_2475055 baseEnd_2475055 := by
    simpa [prefixWord, tailWord_2475055, baseEnd_2475055] using wordTrace_append hprefix tailTrace_2475055
  have hstable : (prefixWord ++ tailWord_2475055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475055).length < 2 ^ (prefixWord ++ tailWord_2475055).sum := by decide
  have hdescent : baseEnd_2475055 < baseStart_2475055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475092 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2475092 : Nat := 118140960795 + 2475092 * 2 ^ 59
def prefixEnd_2475092 : Nat := 4983230072969 + 3 ^ 40 * 2475092 * 2
def baseEnd_2475092 : Nat := 423637286699378474955755

theorem tailTrace_2475092 : CollatzResearch.WordTrace tailWord_2475092 prefixEnd_2475092 423637286699378474955755 := by
  unfold tailWord_2475092
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137010774585935452441765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60182681032781247269922353 45137010774585935452441765)
  ·
    refine ⟨8463189520234862897332831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45137010774585935452441765 8463189520234862897332831)
    ·
      refine ⟨12694784280352294345999247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463189520234862897332831 12694784280352294345999247)
      ·
        refine ⟨19042176420528441518998871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694784280352294345999247 19042176420528441518998871)
        ·
          refine ⟨28563264630792662278498307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19042176420528441518998871 28563264630792662278498307)
          ·
            refine ⟨42844896946188993417747461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28563264630792662278498307 42844896946188993417747461)
            ·
              refine ⟨8033418177410436265827649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42844896946188993417747461 8033418177410436265827649)
              ·
                refine ⟨6025063633057827199370737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8033418177410436265827649 6025063633057827199370737)
                ·
                  refine ⟨4518797724793370399528053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025063633057827199370737 4518797724793370399528053)
                  ·
                    refine ⟨423637286699378474955755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4518797724793370399528053 423637286699378474955755)
                    ·
                      rfl

theorem cell23_2475092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2475092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475092 prefixEnd_2475092 := by exact prefixLift 2475092
  have htrace : WordTrace (prefixWord ++ tailWord_2475092) baseStart_2475092 baseEnd_2475092 := by
    simpa [prefixWord, tailWord_2475092, baseEnd_2475092] using wordTrace_append hprefix tailTrace_2475092
  have hstable : (prefixWord ++ tailWord_2475092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475092).length < 2 ^ (prefixWord ++ tailWord_2475092).sum := by decide
  have hdescent : baseEnd_2475092 < baseStart_2475092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475095 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2475095 : Nat := 118140960795 + 2475095 * 2 ^ 59
def prefixEnd_2475095 : Nat := 4983230072969 + 3 ^ 40 * 2475095 * 2
def baseEnd_2475095 : Nat := 1270913400540098913129751

theorem tailTrace_2475095 : CollatzResearch.WordTrace tailWord_2475095 prefixEnd_2475095 1270913400540098913129751 := by
  unfold tailWord_2475095
  simp only [CollatzResearch.WordTrace]
  refine ⟨90274130968161002417242739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60182753978774001611495159 90274130968161002417242739)
  ·
    refine ⟨135411196452241503625864109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90274130968161002417242739 135411196452241503625864109)
    ·
      refine ⟨50779198669590563859699041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135411196452241503625864109 50779198669590563859699041)
      ·
        refine ⟨38084399002192922894774281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50779198669590563859699041 38084399002192922894774281)
        ·
          refine ⟨28563299251644692171080711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38084399002192922894774281 28563299251644692171080711)
          ·
            refine ⟨42844948877467038256621067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28563299251644692171080711 42844948877467038256621067)
            ·
              refine ⟨64267423316200557384931601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42844948877467038256621067 64267423316200557384931601)
              ·
                refine ⟨48200567487150418038698701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64267423316200557384931601 48200567487150418038698701)
                ·
                  refine ⟨18075212807681406764512013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48200567487150418038698701 18075212807681406764512013)
                  ·
                    refine ⟨6778204802880527536692005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18075212807681406764512013 6778204802880527536692005)
                    ·
                      refine ⟨1270913400540098913129751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6778204802880527536692005 1270913400540098913129751)
                      ·
                        rfl

theorem cell23_2475095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2475095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475095 prefixEnd_2475095 := by exact prefixLift 2475095
  have htrace : WordTrace (prefixWord ++ tailWord_2475095) baseStart_2475095 baseEnd_2475095 := by
    simpa [prefixWord, tailWord_2475095, baseEnd_2475095] using wordTrace_append hprefix tailTrace_2475095
  have hstable : (prefixWord ++ tailWord_2475095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475095).length < 2 ^ (prefixWord ++ tailWord_2475095).sum := by decide
  have hdescent : baseEnd_2475095 < baseStart_2475095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475132 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_2475132 : Nat := 118140960795 + 2475132 * 2 ^ 59
def prefixEnd_2475132 : Nat := 4983230072969 + 3 ^ 40 * 2475132 * 2
def baseEnd_2475132 : Nat := 1270932399324315268367081

theorem tailTrace_2475132 : CollatzResearch.WordTrace tailWord_2475132 prefixEnd_2475132 1270932399324315268367081 := by
  unfold tailWord_2475132
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137740234513478868169825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60183653646017971824226433 45137740234513478868169825)
  ·
    refine ⟨33853305175885109151127369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45137740234513478868169825 33853305175885109151127369)
    ·
      refine ⟨25389978881913831863345527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33853305175885109151127369 25389978881913831863345527)
      ·
        refine ⟨38084968322870747795018291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25389978881913831863345527 38084968322870747795018291)
        ·
          refine ⟨57127452484306121692527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38084968322870747795018291 57127452484306121692527437)
          ·
            refine ⟨21422794681614795634697789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57127452484306121692527437 21422794681614795634697789)
            ·
              refine ⟨8033548005605548363011671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21422794681614795634697789 8033548005605548363011671)
              ·
                refine ⟨12050322008408322544517507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033548005605548363011671 12050322008408322544517507)
                ·
                  refine ⟨18075483012612483816776261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12050322008408322544517507 18075483012612483816776261)
                  ·
                    refine ⟨3389153064864840715645549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18075483012612483816776261 3389153064864840715645549)
                    ·
                      refine ⟨1270932399324315268367081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3389153064864840715645549 1270932399324315268367081)
                      ·
                        rfl

theorem cell23_2475132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_2475132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475132 prefixEnd_2475132 := by exact prefixLift 2475132
  have htrace : WordTrace (prefixWord ++ tailWord_2475132) baseStart_2475132 baseEnd_2475132 := by
    simpa [prefixWord, tailWord_2475132, baseEnd_2475132] using wordTrace_append hprefix tailTrace_2475132
  have hstable : (prefixWord ++ tailWord_2475132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475132).length < 2 ^ (prefixWord ++ tailWord_2475132).sum := by decide
  have hdescent : baseEnd_2475132 < baseStart_2475132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475155 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_2475155 : Nat := 118140960795 + 2475155 * 2 ^ 59
def prefixEnd_2475155 : Nat := 4983230072969 + 3 ^ 40 * 2475155 * 2
def baseEnd_2475155 : Nat := 1270944209379368678379475

theorem tailTrace_2475155 : CollatzResearch.WordTrace tailWord_2475155 prefixEnd_2475155 1270944209379368678379475 := by
  unfold tailWord_2475155
  simp only [CollatzResearch.WordTrace]
  refine ⟨90276319347943632664426919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60184212898629088442951279 90276319347943632664426919)
  ·
    refine ⟨135414479021915448996640379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90276319347943632664426919 135414479021915448996640379)
    ·
      refine ⟨203121718532873173494960569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135414479021915448996640379 203121718532873173494960569)
      ·
        refine ⟨152341288899654880121220427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203121718532873173494960569 152341288899654880121220427)
        ·
          refine ⟨228511933349482320181830641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152341288899654880121220427 228511933349482320181830641)
          ·
            refine ⟨171383950012111740136372981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228511933349482320181830641 171383950012111740136372981)
            ·
              refine ⟨16067245313635475637784967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171383950012111740136372981 16067245313635475637784967)
              ·
                refine ⟨24100867970453213456677451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16067245313635475637784967 24100867970453213456677451)
                ·
                  refine ⟨36151301955679820185016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24100867970453213456677451 36151301955679820185016177)
                  ·
                    refine ⟨27113476466759865138762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36151301955679820185016177 27113476466759865138762133)
                    ·
                      refine ⟨1270944209379368678379475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27113476466759865138762133 1270944209379368678379475)
                      ·
                        rfl

theorem cell23_2475155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_2475155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475155 prefixEnd_2475155 := by exact prefixLift 2475155
  have htrace : WordTrace (prefixWord ++ tailWord_2475155) baseStart_2475155 baseEnd_2475155 := by
    simpa [prefixWord, tailWord_2475155, baseEnd_2475155] using wordTrace_append hprefix tailTrace_2475155
  have hstable : (prefixWord ++ tailWord_2475155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475155).length < 2 ^ (prefixWord ++ tailWord_2475155).sum := by decide
  have hdescent : baseEnd_2475155 < baseStart_2475155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475169 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 6]
def baseStart_2475169 : Nat := 118140960795 + 2475169 * 2 ^ 59
def prefixEnd_2475169 : Nat := 4983230072969 + 3 ^ 40 * 2475169 * 2
def baseEnd_2475169 : Nat := 141216822012059069289379

theorem tailTrace_2475169 : CollatzResearch.WordTrace tailWord_2475169 prefixEnd_2475169 141216822012059069289379 := by
  unfold tailWord_2475169
  simp only [CollatzResearch.WordTrace]
  refine ⟨90276829969892913055436561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60184553313261942036957707 90276829969892913055436561)
  ·
    refine ⟨67707622477419684791577421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90276829969892913055436561 67707622477419684791577421)
    ·
      refine ⟨25390358429032381796841533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67707622477419684791577421 25390358429032381796841533)
      ·
        refine ⟨9521384410887143173815575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25390358429032381796841533 9521384410887143173815575)
        ·
          refine ⟨14282076616330714760723363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521384410887143173815575 14282076616330714760723363)
          ·
            refine ⟨21423114924496072141085045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14282076616330714760723363 21423114924496072141085045)
            ·
              refine ⟨2008417024171506763226723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21423114924496072141085045 2008417024171506763226723)
              ·
                refine ⟨3012625536257260144840085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008417024171506763226723 3012625536257260144840085)
                ·
                  refine ⟨141216822012059069289379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3012625536257260144840085 141216822012059069289379)
                  ·
                    rfl

theorem cell23_2475169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_2475169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475169 prefixEnd_2475169 := by exact prefixLift 2475169
  have htrace : WordTrace (prefixWord ++ tailWord_2475169) baseStart_2475169 baseEnd_2475169 := by
    simpa [prefixWord, tailWord_2475169, baseEnd_2475169] using wordTrace_append hprefix tailTrace_2475169
  have hstable : (prefixWord ++ tailWord_2475169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475169).length < 2 ^ (prefixWord ++ tailWord_2475169).sum := by decide
  have hdescent : baseEnd_2475169 < baseStart_2475169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475220 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 6]
def baseStart_2475220 : Nat := 118140960795 + 2475220 * 2 ^ 59
def prefixEnd_2475220 : Nat := 4983230072969 + 3 ^ 40 * 2475220 * 2
def baseEnd_2475220 : Nat := 141219731735767880451853

theorem tailTrace_2475220 : CollatzResearch.WordTrace tailWord_2475220 prefixEnd_2475220 141219731735767880451853 := by
  unfold tailWord_2475220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45139345046354074382771557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60185793395138765843695409 45139345046354074382771557)
  ·
    refine ⟨8463627196191388946769667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45139345046354074382771557 8463627196191388946769667)
    ·
      refine ⟨12695440794287083420154501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463627196191388946769667 12695440794287083420154501)
      ·
        refine ⟨2380395148928828141278969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12695440794287083420154501 2380395148928828141278969)
        ·
          refine ⟨1785296361696621105959227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380395148928828141278969 1785296361696621105959227)
          ·
            refine ⟨2677944542544931658938841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785296361696621105959227 2677944542544931658938841)
            ·
              refine ⟨2008458406908698744204131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677944542544931658938841 2008458406908698744204131)
              ·
                refine ⟨3012687610363048116306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008458406908698744204131 3012687610363048116306197)
                ·
                  refine ⟨141219731735767880451853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3012687610363048116306197 141219731735767880451853)
                  ·
                    rfl

theorem cell23_2475220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_2475220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475220 prefixEnd_2475220 := by exact prefixLift 2475220
  have htrace : WordTrace (prefixWord ++ tailWord_2475220) baseStart_2475220 baseEnd_2475220 := by
    simpa [prefixWord, tailWord_2475220, baseEnd_2475220] using wordTrace_append hprefix tailTrace_2475220
  have hstable : (prefixWord ++ tailWord_2475220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475220).length < 2 ^ (prefixWord ++ tailWord_2475220).sum := by decide
  have hdescent : baseEnd_2475220 < baseStart_2475220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475232 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2475232 : Nat := 118140960795 + 2475232 * 2 ^ 59
def prefixEnd_2475232 : Nat := 4983230072969 + 3 ^ 40 * 2475232 * 2
def baseEnd_2475232 : Nat := 1270983747389764877116621

theorem tailTrace_2475232 : CollatzResearch.WordTrace tailWord_2475232 prefixEnd_2475232 1270983747389764877116621 := by
  unfold tailWord_2475232
  simp only [CollatzResearch.WordTrace]
  refine ⟨45139563884332337407489975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60186085179109783209986633 45139563884332337407489975)
  ·
    refine ⟨67709345826498506111234963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45139563884332337407489975 67709345826498506111234963)
    ·
      refine ⟨101564018739747759166852445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67709345826498506111234963 101564018739747759166852445)
      ·
        refine ⟨38086507027405409687569667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101564018739747759166852445 38086507027405409687569667)
        ·
          refine ⟨57129760541108114531354501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38086507027405409687569667 57129760541108114531354501)
          ·
            refine ⟨10711830101457771474628969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57129760541108114531354501 10711830101457771474628969)
            ·
              refine ⟨8033872576093328605971727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711830101457771474628969 8033872576093328605971727)
              ·
                refine ⟨12050808864139992908957591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033872576093328605971727 12050808864139992908957591)
                ·
                  refine ⟨18076213296209989363436387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12050808864139992908957591 18076213296209989363436387)
                  ·
                    refine ⟨27114319944314984045154581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18076213296209989363436387 27114319944314984045154581)
                    ·
                      refine ⟨1270983747389764877116621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27114319944314984045154581 1270983747389764877116621)
                      ·
                        rfl

theorem cell23_2475232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2475232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475232 prefixEnd_2475232 := by exact prefixLift 2475232
  have htrace : WordTrace (prefixWord ++ tailWord_2475232) baseStart_2475232 baseEnd_2475232 := by
    simpa [prefixWord, tailWord_2475232, baseEnd_2475232] using wordTrace_append hprefix tailTrace_2475232
  have hstable : (prefixWord ++ tailWord_2475232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475232).length < 2 ^ (prefixWord ++ tailWord_2475232).sum := by decide
  have hdescent : baseEnd_2475232 < baseStart_2475232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475236 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_2475236 : Nat := 118140960795 + 2475236 * 2 ^ 59
def prefixEnd_2475236 : Nat := 4983230072969 + 3 ^ 40 * 2475236 * 2
def baseEnd_2475236 : Nat := 1270985801312382861466603

theorem tailTrace_2475236 : CollatzResearch.WordTrace tailWord_2475236 prefixEnd_2475236 1270985801312382861466603 := by
  unfold tailWord_2475236
  simp only [CollatzResearch.WordTrace]
  refine ⟨45139636830325091749062781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60186182440433455665417041 45139636830325091749062781)
  ·
    refine ⟨16927363811371909405898543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45139636830325091749062781 16927363811371909405898543)
    ·
      refine ⟨25391045717057864108847815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16927363811371909405898543 25391045717057864108847815)
      ·
        refine ⟨38086568575586796163271723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25391045717057864108847815 38086568575586796163271723)
        ·
          refine ⟨57129852863380194244907585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38086568575586796163271723 57129852863380194244907585)
          ·
            refine ⟨42847389647535145683680689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57129852863380194244907585 42847389647535145683680689)
            ·
              refine ⟨32135542235651359262760517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42847389647535145683680689 32135542235651359262760517)
              ·
                refine ⟨6025414169184629861767597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32135542235651359262760517 6025414169184629861767597)
                ·
                  refine ⟨2259530313444236198162849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6025414169184629861767597 2259530313444236198162849)
                  ·
                    refine ⟨1694647735083177148622137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259530313444236198162849 1694647735083177148622137)
                    ·
                      refine ⟨1270985801312382861466603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694647735083177148622137 1270985801312382861466603)
                      ·
                        rfl

theorem cell23_2475236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_2475236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475236 prefixEnd_2475236 := by exact prefixLift 2475236
  have htrace : WordTrace (prefixWord ++ tailWord_2475236) baseStart_2475236 baseEnd_2475236 := by
    simpa [prefixWord, tailWord_2475236, baseEnd_2475236] using wordTrace_append hprefix tailTrace_2475236
  have hstable : (prefixWord ++ tailWord_2475236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475236).length < 2 ^ (prefixWord ++ tailWord_2475236).sum := by decide
  have hdescent : baseEnd_2475236 < baseStart_2475236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475242 : List Nat := [3, 1, 3, 1, 1, 3, 2, 9]
def baseStart_2475242 : Nat := 118140960795 + 2475242 * 2 ^ 59
def prefixEnd_2475242 : Nat := 4983230072969 + 3 ^ 40 * 2475242 * 2
def baseEnd_2475242 : Nat := 47073662303567031036725

theorem tailTrace_2475242 : CollatzResearch.WordTrace tailWord_2475242 prefixEnd_2475242 47073662303567031036725 := by
  unfold tailWord_2475242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22569873124657111630710995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60186328332418964348562653 22569873124657111630710995)
  ·
    refine ⟨33854809686985667446066493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22569873124657111630710995 33854809686985667446066493)
    ·
      refine ⟨12695553632619625292274935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33854809686985667446066493 12695553632619625292274935)
      ·
        refine ⟨19043330448929437938412403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12695553632619625292274935 19043330448929437938412403)
        ·
          refine ⟨28564995673394156907618605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19043330448929437938412403 28564995673394156907618605)
          ·
            refine ⟨10711873377522808840356977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28564995673394156907618605 10711873377522808840356977)
            ·
              refine ⟨8033905033142106630267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711873377522808840356977 8033905033142106630267733)
              ·
                refine ⟨47073662303567031036725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8033905033142106630267733 47073662303567031036725)
                ·
                  rfl

theorem cell23_2475242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_2475242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475242 prefixEnd_2475242 := by exact prefixLift 2475242
  have htrace : WordTrace (prefixWord ++ tailWord_2475242) baseStart_2475242 baseEnd_2475242 := by
    simpa [prefixWord, tailWord_2475242, baseEnd_2475242] using wordTrace_append hprefix tailTrace_2475242
  have hstable : (prefixWord ++ tailWord_2475242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475242).length < 2 ^ (prefixWord ++ tailWord_2475242).sum := by decide
  have hdescent : baseEnd_2475242 < baseStart_2475242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475312 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2475312 : Nat := 118140960795 + 2475312 * 2 ^ 59
def prefixEnd_2475312 : Nat := 4983230072969 + 3 ^ 40 * 2475312 * 2
def baseEnd_2475312 : Nat := 1271024825842124564116253

theorem tailTrace_2475312 : CollatzResearch.WordTrace tailWord_2475312 prefixEnd_2475312 1271024825842124564116253 := by
  unfold tailWord_2475312
  simp only [CollatzResearch.WordTrace]
  refine ⟨45141022804187424238946095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60188030405583232318594793 45141022804187424238946095)
  ·
    refine ⟨67711534206281136358419143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45141022804187424238946095 67711534206281136358419143)
    ·
      refine ⟨101567301309421704537628715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67711534206281136358419143 101567301309421704537628715)
      ·
        refine ⟨152350951964132556806443073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101567301309421704537628715 152350951964132556806443073)
        ·
          refine ⟨114263213973099417604832305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152350951964132556806443073 114263213973099417604832305)
          ·
            refine ⟨85697410479824563203624229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114263213973099417604832305 85697410479824563203624229)
            ·
              refine ⟨16068264464967105600679543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85697410479824563203624229 16068264464967105600679543)
              ·
                refine ⟨24102396697450658401019315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16068264464967105600679543 24102396697450658401019315)
                ·
                  refine ⟨36153595046175987601528973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24102396697450658401019315 36153595046175987601528973)
                  ·
                    refine ⟨13557598142315995350573365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36153595046175987601528973 13557598142315995350573365)
                    ·
                      refine ⟨1271024825842124564116253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13557598142315995350573365 1271024825842124564116253)
                      ·
                        rfl

theorem cell23_2475312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2475312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475312 prefixEnd_2475312 := by exact prefixLift 2475312
  have htrace : WordTrace (prefixWord ++ tailWord_2475312) baseStart_2475312 baseEnd_2475312 := by
    simpa [prefixWord, tailWord_2475312, baseEnd_2475312] using wordTrace_append hprefix tailTrace_2475312
  have hstable : (prefixWord ++ tailWord_2475312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475312).length < 2 ^ (prefixWord ++ tailWord_2475312).sum := by decide
  have hdescent : baseEnd_2475312 < baseStart_2475312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475313 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_2475313 : Nat := 118140960795 + 2475313 * 2 ^ 59
def prefixEnd_2475313 : Nat := 4983230072969 + 3 ^ 40 * 2475313 * 2
def baseEnd_2475313 : Nat := 1271025339322779060203749

theorem tailTrace_2475313 : CollatzResearch.WordTrace tailWord_2475313 prefixEnd_2475313 1271025339322779060203749 := by
  unfold tailWord_2475313
  simp only [CollatzResearch.WordTrace]
  refine ⟨90282082081371225648678593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60188054720914150432452395 90282082081371225648678593)
  ·
    refine ⟨67711561561028419236508945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90282082081371225648678593 67711561561028419236508945)
    ·
      refine ⟨50783671170771314427381709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67711561561028419236508945 50783671170771314427381709)
      ·
        refine ⟨19043876689039242910268141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50783671170771314427381709 19043876689039242910268141)
        ·
          refine ⟨7141453758389716091350553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19043876689039242910268141 7141453758389716091350553)
          ·
            refine ⟨5356090318792287068512915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7141453758389716091350553 5356090318792287068512915)
            ·
              refine ⟨8034135478188430602769373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356090318792287068512915 8034135478188430602769373)
              ·
                refine ⟨3012800804320661476038515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8034135478188430602769373 3012800804320661476038515)
                ·
                  refine ⟨4519201206480992214057773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012800804320661476038515 4519201206480992214057773)
                  ·
                    refine ⟨1694700452430372080271665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4519201206480992214057773 1694700452430372080271665)
                    ·
                      refine ⟨1271025339322779060203749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694700452430372080271665 1271025339322779060203749)
                      ·
                        rfl

theorem cell23_2475313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_2475313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475313 prefixEnd_2475313 := by exact prefixLift 2475313
  have htrace : WordTrace (prefixWord ++ tailWord_2475313) baseStart_2475313 baseEnd_2475313 := by
    simpa [prefixWord, tailWord_2475313, baseEnd_2475313] using wordTrace_append hprefix tailTrace_2475313
  have hstable : (prefixWord ++ tailWord_2475313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475313).length < 2 ^ (prefixWord ++ tailWord_2475313).sum := by decide
  have hdescent : baseEnd_2475313 < baseStart_2475313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475349 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 7]
def baseStart_2475349 : Nat := 118140960795 + 2475349 * 2 ^ 59
def prefixEnd_2475349 : Nat := 4983230072969 + 3 ^ 40 * 2475349 * 2
def baseEnd_2475349 : Nat := 141227091625148991039287

theorem tailTrace_2475349 : CollatzResearch.WordTrace tailWord_2475349 prefixEnd_2475349 141227091625148991039287 := by
  unfold tailWord_2475349
  simp only [CollatzResearch.WordTrace]
  refine ⟨90283395109240803796989101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60188930072827202531326067 90283395109240803796989101)
  ·
    refine ⟨33856273165965301423870913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90283395109240803796989101 33856273165965301423870913)
    ·
      refine ⟨25392204874473976067903185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33856273165965301423870913 25392204874473976067903185)
      ·
        refine ⟨19044153655855482050927389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25392204874473976067903185 19044153655855482050927389)
        ·
          refine ⟨7141557620945805769097771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19044153655855482050927389 7141557620945805769097771)
          ·
            refine ⟨10712336431418708653646657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141557620945805769097771 10712336431418708653646657)
            ·
              refine ⟨8034252323564031490234993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10712336431418708653646657 8034252323564031490234993)
              ·
                refine ⟨6025689242673023617676245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8034252323564031490234993 6025689242673023617676245)
                ·
                  refine ⟨141227091625148991039287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6025689242673023617676245 141227091625148991039287)
                  ·
                    rfl

theorem cell23_2475349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_2475349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475349 prefixEnd_2475349 := by exact prefixLift 2475349
  have htrace : WordTrace (prefixWord ++ tailWord_2475349) baseStart_2475349 baseEnd_2475349 := by
    simpa [prefixWord, tailWord_2475349, baseEnd_2475349] using wordTrace_append hprefix tailTrace_2475349
  have hstable : (prefixWord ++ tailWord_2475349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475349).length < 2 ^ (prefixWord ++ tailWord_2475349).sum := by decide
  have hdescent : baseEnd_2475349 < baseStart_2475349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475389 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2475389 : Nat := 118140960795 + 2475389 * 2 ^ 59
def prefixEnd_2475389 : Nat := 4983230072969 + 3 ^ 40 * 2475389 * 2
def baseEnd_2475389 : Nat := 1271064363852520762853399

theorem tailTrace_2475389 : CollatzResearch.WordTrace tailWord_2475389 prefixEnd_2475389 1271064363852520762853399 := by
  unfold tailWord_2475389
  simp only [CollatzResearch.WordTrace]
  refine ⟨90284854029095890628445221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60189902686063927085630147 90284854029095890628445221)
  ·
    refine ⟨16928410130455479492833479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90284854029095890628445221 16928410130455479492833479)
    ·
      refine ⟨25392615195683219239250219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16928410130455479492833479 25392615195683219239250219)
      ·
        refine ⟨38088922793524828858875329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25392615195683219239250219 38088922793524828858875329)
        ·
          refine ⟨28566692095143621644156497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38088922793524828858875329 28566692095143621644156497)
          ·
            refine ⟨21425019071357716233117373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28566692095143621644156497 21425019071357716233117373)
            ·
              refine ⟨8034382151759143587419015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21425019071357716233117373 8034382151759143587419015)
              ·
                refine ⟨12051573227638715381128523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034382151759143587419015 12051573227638715381128523)
                ·
                  refine ⟨18077359841458073071692785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12051573227638715381128523 18077359841458073071692785)
                  ·
                    refine ⟨13558019881093554803769589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18077359841458073071692785 13558019881093554803769589)
                    ·
                      refine ⟨1271064363852520762853399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13558019881093554803769589 1271064363852520762853399)
                      ·
                        rfl

theorem cell23_2475389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2475389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475389 prefixEnd_2475389 := by exact prefixLift 2475389
  have htrace : WordTrace (prefixWord ++ tailWord_2475389) baseStart_2475389 baseEnd_2475389 := by
    simpa [prefixWord, tailWord_2475389, baseEnd_2475389] using wordTrace_append hprefix tailTrace_2475389
  have hstable : (prefixWord ++ tailWord_2475389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475389).length < 2 ^ (prefixWord ++ tailWord_2475389).sum := by decide
  have hdescent : baseEnd_2475389 < baseStart_2475389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475394 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2475394 : Nat := 118140960795 + 2475394 * 2 ^ 59
def prefixEnd_2475394 : Nat := 4983230072969 + 3 ^ 40 * 2475394 * 2
def baseEnd_2475394 : Nat := 1271066931255793243290877

theorem tailTrace_2475394 : CollatzResearch.WordTrace tailWord_2475394 prefixEnd_2475394 1271066931255793243290877 := by
  unfold tailWord_2475394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571259098519444120594309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60190024262718517654918157 22571259098519444120594309)
  ·
    refine ⟨4232111080972395772611433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22571259098519444120594309 4232111080972395772611433)
    ·
      refine ⟨3174083310729296829458575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4232111080972395772611433 3174083310729296829458575)
      ·
        refine ⟨4761124966093945244187863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174083310729296829458575 4761124966093945244187863)
        ·
          refine ⟨7141687449140917866281795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761124966093945244187863 7141687449140917866281795)
          ·
            refine ⟨10712531173711376799422693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141687449140917866281795 10712531173711376799422693)
            ·
              refine ⟨2008599595070883149891755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10712531173711376799422693 2008599595070883149891755)
              ·
                refine ⟨3012899392606324724837633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008599595070883149891755 3012899392606324724837633)
                ·
                  refine ⟨2259674544454743543628225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012899392606324724837633 2259674544454743543628225)
                  ·
                    refine ⟨1694755908341057657721169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259674544454743543628225 1694755908341057657721169)
                    ·
                      refine ⟨1271066931255793243290877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694755908341057657721169 1271066931255793243290877)
                      ·
                        rfl

theorem cell23_2475394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2475394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475394 prefixEnd_2475394 := by exact prefixLift 2475394
  have htrace : WordTrace (prefixWord ++ tailWord_2475394) baseStart_2475394 baseEnd_2475394 := by
    simpa [prefixWord, tailWord_2475394, baseEnd_2475394] using wordTrace_append hprefix tailTrace_2475394
  have hstable : (prefixWord ++ tailWord_2475394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475394).length < 2 ^ (prefixWord ++ tailWord_2475394).sum := by decide
  have hdescent : baseEnd_2475394 < baseStart_2475394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475436 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2475436 : Nat := 118140960795 + 2475436 * 2 ^ 59
def prefixEnd_2475436 : Nat := 4983230072969 + 3 ^ 40 * 2475436 * 2
def baseEnd_2475436 : Nat := 1271088497443282078965683

theorem tailTrace_2475436 : CollatzResearch.WordTrace tailWord_2475436 prefixEnd_2475436 1271088497443282078965683 := by
  unfold tailWord_2475436
  simp only [CollatzResearch.WordTrace]
  refine ⟨45143284129962808827703081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60191045506617078436937441 45143284129962808827703081)
  ·
    refine ⟨33857463097472106620777311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45143284129962808827703081 33857463097472106620777311)
    ·
      refine ⟨50786194646208159931165967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33857463097472106620777311 50786194646208159931165967)
      ·
        refine ⟨76179291969312239896748951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50786194646208159931165967 76179291969312239896748951)
        ·
          refine ⟨114268937953968359845123427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76179291969312239896748951 114268937953968359845123427)
          ·
            refine ⟨171403406930952539767685141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114268937953968359845123427 171403406930952539767685141)
            ·
              refine ⟨8034534699888400301610241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171403406930952539767685141 8034534699888400301610241)
              ·
                refine ⟨6025901024916300226207681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8034534699888400301610241 6025901024916300226207681)
                ·
                  refine ⟨4519425768687225169655761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025901024916300226207681 4519425768687225169655761)
                  ·
                    refine ⟨3389569326515418877241821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519425768687225169655761 3389569326515418877241821)
                    ·
                      refine ⟨1271088497443282078965683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3389569326515418877241821 1271088497443282078965683)
                      ·
                        rfl

theorem cell23_2475436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2475436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475436 prefixEnd_2475436 := by exact prefixLift 2475436
  have htrace : WordTrace (prefixWord ++ tailWord_2475436) baseStart_2475436 baseEnd_2475436 := by
    simpa [prefixWord, tailWord_2475436, baseEnd_2475436] using wordTrace_append hprefix tailTrace_2475436
  have hstable : (prefixWord ++ tailWord_2475436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475436).length < 2 ^ (prefixWord ++ tailWord_2475436).sum := by decide
  have hdescent : baseEnd_2475436 < baseStart_2475436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475516 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2475516 : Nat := 118140960795 + 2475516 * 2 ^ 59
def prefixEnd_2475516 : Nat := 4983230072969 + 3 ^ 40 * 2475516 * 2
def baseEnd_2475516 : Nat := 423709858631880588655105

theorem tailTrace_2475516 : CollatzResearch.WordTrace tailWord_2475516 prefixEnd_2475516 423709858631880588655105 := by
  unfold tailWord_2475516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45144743049817895659159201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60192990733090527545545601 45144743049817895659159201)
  ·
    refine ⟨33858557287363421744369401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45144743049817895659159201 33858557287363421744369401)
    ·
      refine ⟨25393917965522566308277051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33858557287363421744369401 25393917965522566308277051)
      ·
        refine ⟨38090876948283849462415577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25393917965522566308277051 38090876948283849462415577)
        ·
          refine ⟨28568157711212887096811683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38090876948283849462415577 28568157711212887096811683)
          ·
            refine ⟨42852236566819330645217525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28568157711212887096811683 42852236566819330645217525)
            ·
              refine ⟨4017397178139312247989143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42852236566819330645217525 4017397178139312247989143)
              ·
                refine ⟨6026095767208968371983715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017397178139312247989143 6026095767208968371983715)
                ·
                  refine ⟨9039143650813452557975573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6026095767208968371983715 9039143650813452557975573)
                  ·
                    refine ⟨423709858631880588655105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9039143650813452557975573 423709858631880588655105)
                    ·
                      rfl

theorem cell23_2475516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2475516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475516 prefixEnd_2475516 := by exact prefixLift 2475516
  have htrace : WordTrace (prefixWord ++ tailWord_2475516) baseStart_2475516 baseEnd_2475516 := by
    simpa [prefixWord, tailWord_2475516, baseEnd_2475516] using wordTrace_append hprefix tailTrace_2475516
  have hstable : (prefixWord ++ tailWord_2475516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475516).length < 2 ^ (prefixWord ++ tailWord_2475516).sum := by decide
  have hdescent : baseEnd_2475516 < baseStart_2475516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475523 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 5, 2, 2]
def baseStart_2475523 : Nat := 118140960795 + 2475523 * 2 ^ 59
def prefixEnd_2475523 : Nat := 4983230072969 + 3 ^ 40 * 2475523 * 2
def baseEnd_2475523 : Nat := 1271133170260223238577783

theorem tailTrace_2475523 : CollatzResearch.WordTrace tailWord_2475523 prefixEnd_2475523 1271133170260223238577783 := by
  unfold tailWord_2475523
  simp only [CollatzResearch.WordTrace]
  refine ⟨90289741410610431513823223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60193160940406954342548815 90289741410610431513823223)
  ·
    refine ⟨135434612115915647270734835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90289741410610431513823223 135434612115915647270734835)
    ·
      refine ⟨203151918173873470906102253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135434612115915647270734835 203151918173873470906102253)
      ·
        refine ⟨76181969315202551589788345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203151918173873470906102253 76181969315202551589788345)
        ·
          refine ⟨57136476986401913692341259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76181969315202551589788345 57136476986401913692341259)
          ·
            refine ⟨85704715479602870538511889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57136476986401913692341259 85704715479602870538511889)
            ·
              refine ⟨64278536609702152903883917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85704715479602870538511889 64278536609702152903883917)
              ·
                refine ⟨24104451228638307338956469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64278536609702152903883917 24104451228638307338956469)
                ·
                  refine ⟨2259792302684841313027169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24104451228638307338956469 2259792302684841313027169)
                  ·
                    refine ⟨1694844227013630984770377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259792302684841313027169 1694844227013630984770377)
                    ·
                      refine ⟨1271133170260223238577783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694844227013630984770377 1271133170260223238577783)
                      ·
                        rfl

theorem cell23_2475523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_2475523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475523 prefixEnd_2475523 := by exact prefixLift 2475523
  have htrace : WordTrace (prefixWord ++ tailWord_2475523) baseStart_2475523 baseEnd_2475523 := by
    simpa [prefixWord, tailWord_2475523, baseEnd_2475523] using wordTrace_append hprefix tailTrace_2475523
  have hstable : (prefixWord ++ tailWord_2475523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475523).length < 2 ^ (prefixWord ++ tailWord_2475523).sum := by decide
  have hdescent : baseEnd_2475523 < baseStart_2475523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475529 : List Nat := [1, 2, 1, 1, 3, 1, 5, 9]
def baseStart_2475529 : Nat := 118140960795 + 2475529 * 2 ^ 59
def prefixEnd_2475529 : Nat := 4983230072969 + 3 ^ 40 * 2475529 * 2
def baseEnd_2475529 : Nat := 47079120412746304263065

theorem tailTrace_2475529 : CollatzResearch.WordTrace tailWord_2475529 prefixEnd_2475529 47079120412746304263065 := by
  unfold tailWord_2475529
  simp only [CollatzResearch.WordTrace]
  refine ⟨90289960248588694538541641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60193306832392463025694427 90289960248588694538541641)
  ·
    refine ⟨67717470186441520903906231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90289960248588694538541641 67717470186441520903906231)
    ·
      refine ⟨101576205279662281355859347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67717470186441520903906231 101576205279662281355859347)
      ·
        refine ⟨152364307919493422033789021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101576205279662281355859347 152364307919493422033789021)
        ·
          refine ⟨57136615469810033262670883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152364307919493422033789021 57136615469810033262670883)
          ·
            refine ⟨85704923204715049894006325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57136615469810033262670883 85704923204715049894006325)
            ·
              refine ⟨8034836550442035927563093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85704923204715049894006325 8034836550442035927563093)
              ·
                refine ⟨47079120412746304263065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8034836550442035927563093 47079120412746304263065)
                ·
                  rfl

theorem cell23_2475529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 9].length) (baseStart_2475529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475529 prefixEnd_2475529 := by exact prefixLift 2475529
  have htrace : WordTrace (prefixWord ++ tailWord_2475529) baseStart_2475529 baseEnd_2475529 := by
    simpa [prefixWord, tailWord_2475529, baseEnd_2475529] using wordTrace_append hprefix tailTrace_2475529
  have hstable : (prefixWord ++ tailWord_2475529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475529).length < 2 ^ (prefixWord ++ tailWord_2475529).sum := by decide
  have hdescent : baseEnd_2475529 < baseStart_2475529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475534 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2475534 : Nat := 118140960795 + 2475534 * 2 ^ 59
def prefixEnd_2475534 : Nat := 4983230072969 + 3 ^ 40 * 2475534 * 2
def baseEnd_2475534 : Nat := 1271138818547422695540233

theorem tailTrace_2475534 : CollatzResearch.WordTrace tailWord_2475534 prefixEnd_2475534 1271138818547422695540233 := by
  unfold tailWord_2475534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11286267826696322549059207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60193428409047053594982437 11286267826696322549059207)
  ·
    refine ⟨16929401740044483823588811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11286267826696322549059207 16929401740044483823588811)
    ·
      refine ⟨25394102610066725735383217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16929401740044483823588811 25394102610066725735383217)
      ·
        refine ⟨19045576957550044301537413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25394102610066725735383217 19045576957550044301537413)
        ·
          refine ⟨3571045679540633306538265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19045576957550044301537413 3571045679540633306538265)
          ·
            refine ⟨2678284259655474979903699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3571045679540633306538265 2678284259655474979903699)
            ·
              refine ⟨4017426389483212469855549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678284259655474979903699 4017426389483212469855549)
              ·
                refine ⟨1506534896056204676195831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4017426389483212469855549 1506534896056204676195831)
                ·
                  refine ⟨2259802344084307014293747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506534896056204676195831 2259802344084307014293747)
                  ·
                    refine ⟨3389703516126460521440621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259802344084307014293747 3389703516126460521440621)
                    ·
                      refine ⟨1271138818547422695540233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3389703516126460521440621 1271138818547422695540233)
                      ·
                        rfl

theorem cell23_2475534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2475534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475534 prefixEnd_2475534 := by exact prefixLift 2475534
  have htrace : WordTrace (prefixWord ++ tailWord_2475534) baseStart_2475534 baseEnd_2475534 := by
    simpa [prefixWord, tailWord_2475534, baseEnd_2475534] using wordTrace_append hprefix tailTrace_2475534
  have hstable : (prefixWord ++ tailWord_2475534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475534).length < 2 ^ (prefixWord ++ tailWord_2475534).sum := by decide
  have hdescent : baseEnd_2475534 < baseStart_2475534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475574 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2475574 : Nat := 118140960795 + 2475574 * 2 ^ 59
def prefixEnd_2475574 : Nat := 4983230072969 + 3 ^ 40 * 2475574 * 2
def baseEnd_2475574 : Nat := 1271159357773602539040049

theorem tailTrace_2475574 : CollatzResearch.WordTrace tailWord_2475574 prefixEnd_2475574 1271159357773602539040049 := by
  unfold tailWord_2475574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5643225095839104201495611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60194401022283778149286517 5643225095839104201495611)
  ·
    refine ⟨8464837643758656302243417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5643225095839104201495611 8464837643758656302243417)
    ·
      refine ⟨6348628232818992226682563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8464837643758656302243417 6348628232818992226682563)
      ·
        refine ⟨9522942349228488340023845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348628232818992226682563 9522942349228488340023845)
        ·
          refine ⟨1785551690480341563754471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9522942349228488340023845 1785551690480341563754471)
          ·
            refine ⟨2678327535720512345631707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785551690480341563754471 2678327535720512345631707)
            ·
              refine ⟨4017491303580768518447561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678327535720512345631707 4017491303580768518447561)
              ·
                refine ⟨3013118477685576388835671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017491303580768518447561 3013118477685576388835671)
                ·
                  refine ⟨4519677716528364583253507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013118477685576388835671 4519677716528364583253507)
                  ·
                    refine ⟨6779516574792546874880261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519677716528364583253507 6779516574792546874880261)
                    ·
                      refine ⟨1271159357773602539040049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6779516574792546874880261 1271159357773602539040049)
                      ·
                        rfl

theorem cell23_2475574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2475574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475574 prefixEnd_2475574 := by exact prefixLift 2475574
  have htrace : WordTrace (prefixWord ++ tailWord_2475574) baseStart_2475574 baseEnd_2475574 := by
    simpa [prefixWord, tailWord_2475574, baseEnd_2475574] using wordTrace_append hprefix tailTrace_2475574
  have hstable : (prefixWord ++ tailWord_2475574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475574).length < 2 ^ (prefixWord ++ tailWord_2475574).sum := by decide
  have hdescent : baseEnd_2475574 < baseStart_2475574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475673 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 5, 2]
def baseStart_2475673 : Nat := 118140960795 + 2475673 * 2 ^ 59
def prefixEnd_2475673 : Nat := 4983230072969 + 3 ^ 40 * 2475673 * 2
def baseEnd_2475673 : Nat := 1271210192358397651702093

theorem tailTrace_2475673 : CollatzResearch.WordTrace tailWord_2475673 prefixEnd_2475673 1271210192358397651702093 := by
  unfold tailWord_2475673
  simp only [CollatzResearch.WordTrace]
  refine ⟨90295212360067007131783673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60196808240044671421189115 90295212360067007131783673)
  ·
    refine ⟨67721409270050255348837755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90295212360067007131783673 67721409270050255348837755)
    ·
      refine ⟨101582113905075383023256633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67721409270050255348837755 101582113905075383023256633)
      ·
        refine ⟨76186585428806537267442475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101582113905075383023256633 76186585428806537267442475)
        ·
          refine ⟨114279878143209805901163713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76186585428806537267442475 114279878143209805901163713)
          ·
            refine ⟨85709908607407354425872785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114279878143209805901163713 85709908607407354425872785)
            ·
              refine ⟨64282431455555515819404589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85709908607407354425872785 64282431455555515819404589)
              ·
                refine ⟨24105911795833318432276721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64282431455555515819404589 24105911795833318432276721)
                ·
                  refine ⟨18079433846874988824207541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24105911795833318432276721 18079433846874988824207541)
                  ·
                    refine ⟨1694946923144530202269457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18079433846874988824207541 1694946923144530202269457)
                    ·
                      refine ⟨1271210192358397651702093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1694946923144530202269457 1271210192358397651702093)
                      ·
                        rfl

theorem cell23_2475673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_2475673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475673 prefixEnd_2475673 := by exact prefixLift 2475673
  have htrace : WordTrace (prefixWord ++ tailWord_2475673) baseStart_2475673 baseEnd_2475673 := by
    simpa [prefixWord, tailWord_2475673, baseEnd_2475673] using wordTrace_append hprefix tailTrace_2475673
  have hstable : (prefixWord ++ tailWord_2475673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475673).length < 2 ^ (prefixWord ++ tailWord_2475673).sum := by decide
  have hdescent : baseEnd_2475673 < baseStart_2475673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475703 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2475703 : Nat := 118140960795 + 2475703 * 2 ^ 59
def prefixEnd_2475703 : Nat := 4983230072969 + 3 ^ 40 * 2475703 * 2
def baseEnd_2475703 : Nat := 1271225596778032534326955

theorem tailTrace_2475703 : CollatzResearch.WordTrace tailWord_2475703 prefixEnd_2475703 1271225596778032534326955 := by
  unfold tailWord_2475703
  simp only [CollatzResearch.WordTrace]
  refine ⟨90296306549958322255375763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60197537699972214836917175 90296306549958322255375763)
  ·
    refine ⟨135444459824937483383063645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90296306549958322255375763 135444459824937483383063645)
    ·
      refine ⟨50791672434351556268648867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135444459824937483383063645 50791672434351556268648867)
      ·
        refine ⟨76187508651527334402973301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50791672434351556268648867 76187508651527334402973301)
        ·
          refine ⟨7142578936080687600278747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76187508651527334402973301 7142578936080687600278747)
          ·
            refine ⟨10713868404121031400418121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142578936080687600278747 10713868404121031400418121)
            ·
              refine ⟨8035401303090773550313591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10713868404121031400418121 8035401303090773550313591)
              ·
                refine ⟨12053101954636160325470387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035401303090773550313591 12053101954636160325470387)
                ·
                  refine ⟨18079652931954240488205581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12053101954636160325470387 18079652931954240488205581)
                  ·
                    refine ⟨6779869849482840183077093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18079652931954240488205581 6779869849482840183077093)
                    ·
                      refine ⟨1271225596778032534326955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6779869849482840183077093 1271225596778032534326955)
                      ·
                        rfl

theorem cell23_2475703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2475703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475703 prefixEnd_2475703 := by exact prefixLift 2475703
  have htrace : WordTrace (prefixWord ++ tailWord_2475703) baseStart_2475703 baseEnd_2475703 := by
    simpa [prefixWord, tailWord_2475703, baseEnd_2475703] using wordTrace_append hprefix tailTrace_2475703
  have hstable : (prefixWord ++ tailWord_2475703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475703).length < 2 ^ (prefixWord ++ tailWord_2475703).sum := by decide
  have hdescent : baseEnd_2475703 < baseStart_2475703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475743 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 6]
def baseStart_2475743 : Nat := 118140960795 + 2475743 * 2 ^ 59
def prefixEnd_2475743 : Nat := 4983230072969 + 3 ^ 40 * 2475743 * 2
def baseEnd_2475743 : Nat := 141249570667134708647419

theorem tailTrace_2475743 : CollatzResearch.WordTrace tailWord_2475743 prefixEnd_2475743 141249570667134708647419 := by
  unfold tailWord_2475743
  simp only [CollatzResearch.WordTrace]
  refine ⟨90297765469813409086831883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60198510313208939391221255 90297765469813409086831883)
  ·
    refine ⟨135446648204720113630247825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90297765469813409086831883 135446648204720113630247825)
    ·
      refine ⟨101584986153540085222685869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135446648204720113630247825 101584986153540085222685869)
      ·
        refine ⟨38094369807577531958507201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101584986153540085222685869 38094369807577531958507201)
        ·
          refine ⟨28570777355683148968880401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38094369807577531958507201 28570777355683148968880401)
          ·
            refine ⟨21428083016762361726660301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28570777355683148968880401 21428083016762361726660301)
            ·
              refine ⟨8035531131285885647497613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21428083016762361726660301 8035531131285885647497613)
              ·
                refine ⟨3013324174232207117811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8035531131285885647497613 3013324174232207117811605)
                ·
                  refine ⟨141249570667134708647419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3013324174232207117811605 141249570667134708647419)
                  ·
                    rfl

theorem cell23_2475743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 6].length) (baseStart_2475743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475743 prefixEnd_2475743 := by exact prefixLift 2475743
  have htrace : WordTrace (prefixWord ++ tailWord_2475743) baseStart_2475743 baseEnd_2475743 := by
    simpa [prefixWord, tailWord_2475743, baseEnd_2475743] using wordTrace_append hprefix tailTrace_2475743
  have hstable : (prefixWord ++ tailWord_2475743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475743).length < 2 ^ (prefixWord ++ tailWord_2475743).sum := by decide
  have hdescent : baseEnd_2475743 < baseStart_2475743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475757 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2475757 : Nat := 118140960795 + 2475757 * 2 ^ 59
def prefixEnd_2475757 : Nat := 4983230072969 + 3 ^ 40 * 2475757 * 2
def baseEnd_2475757 : Nat := 1271253324733375323051707

theorem tailTrace_2475757 : CollatzResearch.WordTrace tailWord_2475757 prefixEnd_2475757 1271253324733375323051707 := by
  unfold tailWord_2475757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90298276091762689477841525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60198850727841792985227683 90298276091762689477841525)
  ·
    refine ⟨8465463383602752138547643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90298276091762689477841525 8465463383602752138547643)
    ·
      refine ⟨12698195075404128207821465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8465463383602752138547643 12698195075404128207821465)
      ·
        refine ⟨9523646306553096155866099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12698195075404128207821465 9523646306553096155866099)
        ·
          refine ⟨14285469459829644233799149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523646306553096155866099 14285469459829644233799149)
          ·
            refine ⟨5357051047436116587674681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14285469459829644233799149 5357051047436116587674681)
            ·
              refine ⟨4017788285577087440756011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5357051047436116587674681 4017788285577087440756011)
              ·
                refine ⟨6026682428365631161134017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017788285577087440756011 6026682428365631161134017)
                ·
                  refine ⟨4520011821274223370850513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026682428365631161134017 4520011821274223370850513)
                  ·
                    refine ⟨3390008865955667528137885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520011821274223370850513 3390008865955667528137885)
                    ·
                      refine ⟨1271253324733375323051707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390008865955667528137885 1271253324733375323051707)
                      ·
                        rfl

theorem cell23_2475757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2475757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475757 prefixEnd_2475757 := by exact prefixLift 2475757
  have htrace : WordTrace (prefixWord ++ tailWord_2475757) baseStart_2475757 baseEnd_2475757 := by
    simpa [prefixWord, tailWord_2475757, baseEnd_2475757] using wordTrace_append hprefix tailTrace_2475757
  have hstable : (prefixWord ++ tailWord_2475757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475757).length < 2 ^ (prefixWord ++ tailWord_2475757).sum := by decide
  have hdescent : baseEnd_2475757 < baseStart_2475757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475810 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2475810 : Nat := 118140960795 + 2475810 * 2 ^ 59
def prefixEnd_2475810 : Nat := 4983230072969 + 3 ^ 40 * 2475810 * 2
def baseEnd_2475810 : Nat := 1271280539208063615688963

theorem tailTrace_2475810 : CollatzResearch.WordTrace tailWord_2475810 prefixEnd_2475810 1271280539208063615688963 := by
  unfold tailWord_2475810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575052290142669882380221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60200139440380453019680589 22575052290142669882380221)
  ·
    refine ⟨8465644608803501205892583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22575052290142669882380221 8465644608803501205892583)
    ·
      refine ⟨12698466913205251808838875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8465644608803501205892583 12698466913205251808838875)
      ·
        refine ⟨19047700369807877713258313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12698466913205251808838875 19047700369807877713258313)
        ·
          refine ⟨14285775277355908284943735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19047700369807877713258313 14285775277355908284943735)
          ·
            refine ⟨21428662916033862427415603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14285775277355908284943735 21428662916033862427415603)
            ·
              refine ⟨32142994374050793641123405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21428662916033862427415603 32142994374050793641123405)
              ·
                refine ⟨12053622890269047615421277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32142994374050793641123405 12053622890269047615421277)
                ·
                  refine ⟨4520108583850892855782979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12053622890269047615421277 4520108583850892855782979)
                  ·
                    refine ⟨6780162875776339283674469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520108583850892855782979 6780162875776339283674469)
                    ·
                      refine ⟨1271280539208063615688963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6780162875776339283674469 1271280539208063615688963)
                      ·
                        rfl

theorem cell23_2475810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2475810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475810 prefixEnd_2475810 := by exact prefixLift 2475810
  have htrace : WordTrace (prefixWord ++ tailWord_2475810) baseStart_2475810 baseEnd_2475810 := by
    simpa [prefixWord, tailWord_2475810, baseEnd_2475810] using wordTrace_append hprefix tailTrace_2475810
  have hstable : (prefixWord ++ tailWord_2475810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475810).length < 2 ^ (prefixWord ++ tailWord_2475810).sum := by decide
  have hdescent : baseEnd_2475810 < baseStart_2475810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475827 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 4]
def baseStart_2475827 : Nat := 118140960795 + 2475827 * 2 ^ 59
def prefixEnd_2475827 : Nat := 4983230072969 + 3 ^ 40 * 2475827 * 2
def baseEnd_2475827 : Nat := 1271289268379190049176385

theorem tailTrace_2475827 : CollatzResearch.WordTrace tailWord_2475827 prefixEnd_2475827 1271289268379190049176385 := by
  unfold tailWord_2475827
  simp only [CollatzResearch.WordTrace]
  refine ⟨90300829201509091432889735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60200552801006060955259823 90300829201509091432889735)
  ·
    refine ⟨135451243802263637149334603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90300829201509091432889735 135451243802263637149334603)
    ·
      refine ⟨203176865703395455724001905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135451243802263637149334603 203176865703395455724001905)
      ·
        refine ⟨152382649277546591793001429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203176865703395455724001905 152382649277546591793001429)
        ·
          refine ⟨3571468342442498245148471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 152382649277546591793001429 3571468342442498245148471)
          ·
            refine ⟨5357202513663747367722707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571468342442498245148471 5357202513663747367722707)
            ·
              refine ⟨8035803770495621051584061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357202513663747367722707 8035803770495621051584061)
              ·
                refine ⟨3013426413935857894344023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8035803770495621051584061 3013426413935857894344023)
                ·
                  refine ⟨4520139620903786841516035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013426413935857894344023 4520139620903786841516035)
                  ·
                    refine ⟨6780209431355680262274053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520139620903786841516035 6780209431355680262274053)
                    ·
                      refine ⟨1271289268379190049176385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6780209431355680262274053 1271289268379190049176385)
                      ·
                        rfl

theorem cell23_2475827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_2475827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475827 prefixEnd_2475827 := by exact prefixLift 2475827
  have htrace : WordTrace (prefixWord ++ tailWord_2475827) baseStart_2475827 baseEnd_2475827 := by
    simpa [prefixWord, tailWord_2475827, baseEnd_2475827] using wordTrace_append hprefix tailTrace_2475827
  have hstable : (prefixWord ++ tailWord_2475827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475827).length < 2 ^ (prefixWord ++ tailWord_2475827).sum := by decide
  have hdescent : baseEnd_2475827 < baseStart_2475827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475837 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2475837 : Nat := 118140960795 + 2475837 * 2 ^ 59
def prefixEnd_2475837 : Nat := 4983230072969 + 3 ^ 40 * 2475837 * 2
def baseEnd_2475837 : Nat := 423764801061911670017113

theorem tailTrace_2475837 : CollatzResearch.WordTrace tailWord_2475837 prefixEnd_2475837 423764801061911670017113 := by
  unfold tailWord_2475837
  simp only [CollatzResearch.WordTrace]
  refine ⟨90301193931472863140753765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60200795954315242093835843 90301193931472863140753765)
  ·
    refine ⟨16931473862151161838891331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90301193931472863140753765 16931473862151161838891331)
    ·
      refine ⟨25397210793226742758336997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16931473862151161838891331 25397210793226742758336997)
      ·
        refine ⟨4761977023730014267188187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25397210793226742758336997 4761977023730014267188187)
        ·
          refine ⟨7142965535595021400782281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761977023730014267188187 7142965535595021400782281)
          ·
            refine ⟨5357224151696266050586711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7142965535595021400782281 5357224151696266050586711)
            ·
              refine ⟨8035836227544399075880067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357224151696266050586711 8035836227544399075880067)
              ·
                refine ⟨12053754341316598613820101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035836227544399075880067 12053754341316598613820101)
                ·
                  refine ⟨2260078938996862240091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12053754341316598613820101 2260078938996862240091269)
                  ·
                    refine ⟨423764801061911670017113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260078938996862240091269 423764801061911670017113)
                    ·
                      rfl

theorem cell23_2475837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2475837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475837 prefixEnd_2475837 := by exact prefixLift 2475837
  have htrace : WordTrace (prefixWord ++ tailWord_2475837) baseStart_2475837 baseEnd_2475837 := by
    simpa [prefixWord, tailWord_2475837, baseEnd_2475837] using wordTrace_append hprefix tailTrace_2475837
  have hstable : (prefixWord ++ tailWord_2475837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475837).length < 2 ^ (prefixWord ++ tailWord_2475837).sum := by decide
  have hdescent : baseEnd_2475837 < baseStart_2475837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475857 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_2475857 : Nat := 118140960795 + 2475857 * 2 ^ 59
def prefixEnd_2475857 : Nat := 4983230072969 + 3 ^ 40 * 2475857 * 2
def baseEnd_2475857 : Nat := 1271304672798824931801247

theorem tailTrace_2475857 : CollatzResearch.WordTrace tailWord_2475857 prefixEnd_2475857 1271304672798824931801247 := by
  unfold tailWord_2475857
  simp only [CollatzResearch.WordTrace]
  refine ⟨90301923391400406556481825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60201282260933604370987883 90301923391400406556481825)
  ·
    refine ⟨67726442543550304917361369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90301923391400406556481825 67726442543550304917361369)
    ·
      refine ⟨50794831907662728688021027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67726442543550304917361369 50794831907662728688021027)
      ·
        refine ⟨76192247861494093032031541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50794831907662728688021027 76192247861494093032031541)
        ·
          refine ⟨7143023237015071221752957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76192247861494093032031541 7143023237015071221752957)
          ·
            refine ⟨2678633713880651708157359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7143023237015071221752957 2678633713880651708157359)
            ·
              refine ⟨4017950570820977562236039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678633713880651708157359 4017950570820977562236039)
              ·
                refine ⟨6026925856231466343354059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017950570820977562236039 6026925856231466343354059)
                ·
                  refine ⟨9040388784347199515031089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6026925856231466343354059 9040388784347199515031089)
                  ·
                    refine ⟨6780291588260399636273317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9040388784347199515031089 6780291588260399636273317)
                    ·
                      refine ⟨1271304672798824931801247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6780291588260399636273317 1271304672798824931801247)
                      ·
                        rfl

theorem cell23_2475857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_2475857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475857 prefixEnd_2475857 := by exact prefixLift 2475857
  have htrace : WordTrace (prefixWord ++ tailWord_2475857) baseStart_2475857 baseEnd_2475857 := by
    simpa [prefixWord, tailWord_2475857, baseEnd_2475857] using wordTrace_append hprefix tailTrace_2475857
  have hstable : (prefixWord ++ tailWord_2475857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475857).length < 2 ^ (prefixWord ++ tailWord_2475857).sum := by decide
  have hdescent : baseEnd_2475857 < baseStart_2475857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475873 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2475873 : Nat := 118140960795 + 2475873 * 2 ^ 59
def prefixEnd_2475873 : Nat := 4983230072969 + 3 ^ 40 * 2475873 * 2
def baseEnd_2475873 : Nat := 1271312888489296869201173

theorem tailTrace_2475873 : CollatzResearch.WordTrace tailWord_2475873 prefixEnd_2475873 1271312888489296869201173 := by
  unfold tailWord_2475873
  simp only [CollatzResearch.WordTrace]
  refine ⟨90302506959342441289064273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60201671306228294192709515 90302506959342441289064273)
  ·
    refine ⟨67726880219506830966798205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90302506959342441289064273 67726880219506830966798205)
    ·
      refine ⟨25397580082315061612549327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67726880219506830966798205 25397580082315061612549327)
      ·
        refine ⟨38096370123472592418823991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25397580082315061612549327 38096370123472592418823991)
        ·
          refine ⟨57144555185208888628235987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38096370123472592418823991 57144555185208888628235987)
          ·
            refine ⟨85716832777813332942353981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57144555185208888628235987 85716832777813332942353981)
            ·
              refine ⟨32143812291679999853382743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85716832777813332942353981 32143812291679999853382743)
              ·
                refine ⟨48215718437519999780074115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32143812291679999853382743 48215718437519999780074115)
                ·
                  refine ⟨72323577656279999670111173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48215718437519999780074115 72323577656279999670111173)
                  ·
                    refine ⟨13560670810552499938145845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72323577656279999670111173 13560670810552499938145845)
                    ·
                      refine ⟨1271312888489296869201173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13560670810552499938145845 1271312888489296869201173)
                      ·
                        rfl

theorem cell23_2475873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2475873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475873 prefixEnd_2475873 := by exact prefixLift 2475873
  have htrace : WordTrace (prefixWord ++ tailWord_2475873) baseStart_2475873 baseEnd_2475873 := by
    simpa [prefixWord, tailWord_2475873, baseEnd_2475873] using wordTrace_append hprefix tailTrace_2475873
  have hstable : (prefixWord ++ tailWord_2475873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475873).length < 2 ^ (prefixWord ++ tailWord_2475873).sum := by decide
  have hdescent : baseEnd_2475873 < baseStart_2475873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475883 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_2475883 : Nat := 118140960795 + 2475883 * 2 ^ 59
def prefixEnd_2475883 : Nat := 4983230072969 + 3 ^ 40 * 2475883 * 2
def baseEnd_2475883 : Nat := 1271318023295841830076127

theorem tailTrace_2475883 : CollatzResearch.WordTrace tailWord_2475883 prefixEnd_2475883 1271318023295841830076127 := by
  unfold tailWord_2475883
  simp only [CollatzResearch.WordTrace]
  refine ⟨90302871689306212996928303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60201914459537475331285535 90302871689306212996928303)
  ·
    refine ⟨135454307533959319495392455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90302871689306212996928303 135454307533959319495392455)
    ·
      refine ⟨203181461300938979243088683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135454307533959319495392455 203181461300938979243088683)
      ·
        refine ⟨304772191951408468864633025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203181461300938979243088683 304772191951408468864633025)
        ·
          refine ⟨228579143963556351648474769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304772191951408468864633025 228579143963556351648474769)
          ·
            refine ⟨171434357972667263736356077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228579143963556351648474769 171434357972667263736356077)
            ·
              refine ⟨64287884239750223901133529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171434357972667263736356077 64287884239750223901133529)
              ·
                refine ⟨48215913179812667925850147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64287884239750223901133529 48215913179812667925850147)
                ·
                  refine ⟨72323869769719001888775221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48215913179812667925850147 72323869769719001888775221)
                  ·
                    refine ⟨6780362790911156427072677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72323869769719001888775221 6780362790911156427072677)
                    ·
                      refine ⟨1271318023295841830076127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6780362790911156427072677 1271318023295841830076127)
                      ·
                        rfl

theorem cell23_2475883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_2475883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475883 prefixEnd_2475883 := by exact prefixLift 2475883
  have htrace : WordTrace (prefixWord ++ tailWord_2475883) baseStart_2475883 baseEnd_2475883 := by
    simpa [prefixWord, tailWord_2475883, baseEnd_2475883] using wordTrace_append hprefix tailTrace_2475883
  have hstable : (prefixWord ++ tailWord_2475883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475883).length < 2 ^ (prefixWord ++ tailWord_2475883).sum := by decide
  have hdescent : baseEnd_2475883 < baseStart_2475883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475903 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2475903 : Nat := 118140960795 + 2475903 * 2 ^ 59
def prefixEnd_2475903 : Nat := 4983230072969 + 3 ^ 40 * 2475903 * 2
def baseEnd_2475903 : Nat := 1271328292908931751826035

theorem tailTrace_2475903 : CollatzResearch.WordTrace tailWord_2475903 prefixEnd_2475903 1271328292908931751826035 := by
  unfold tailWord_2475903
  simp only [CollatzResearch.WordTrace]
  refine ⟨90303601149233756412656363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60202400766155837608437575 90303601149233756412656363)
  ·
    refine ⟨135455401723850634618984545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90303601149233756412656363 135455401723850634618984545)
    ·
      refine ⟨101591551292887975964238409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135455401723850634618984545 101591551292887975964238409)
      ·
        refine ⟨76193663469665981973178807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101591551292887975964238409 76193663469665981973178807)
        ·
          refine ⟨114290495204498972959768211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76193663469665981973178807 114290495204498972959768211)
          ·
            refine ⟨171435742806748459439652317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114290495204498972959768211 171435742806748459439652317)
            ·
              refine ⟨64288403552530672289869619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171435742806748459439652317 64288403552530672289869619)
              ·
                refine ⟨96432605328796008434804429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64288403552530672289869619 96432605328796008434804429)
                ·
                  refine ⟨36162226998298503163051661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96432605328796008434804429 36162226998298503163051661)
                  ·
                    refine ⟨13560835124361938686144373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36162226998298503163051661 13560835124361938686144373)
                    ·
                      refine ⟨1271328292908931751826035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13560835124361938686144373 1271328292908931751826035)
                      ·
                        rfl

theorem cell23_2475903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2475903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475903 prefixEnd_2475903 := by exact prefixLift 2475903
  have htrace : WordTrace (prefixWord ++ tailWord_2475903) baseStart_2475903 baseEnd_2475903 := by
    simpa [prefixWord, tailWord_2475903, baseEnd_2475903] using wordTrace_append hprefix tailTrace_2475903
  have hstable : (prefixWord ++ tailWord_2475903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475903).length < 2 ^ (prefixWord ++ tailWord_2475903).sum := by decide
  have hdescent : baseEnd_2475903 < baseStart_2475903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475938 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_2475938 : Nat := 118140960795 + 2475938 * 2 ^ 59
def prefixEnd_2475938 : Nat := 4983230072969 + 3 ^ 40 * 2475938 * 2
def baseEnd_2475938 : Nat := 1271346264731839114888375

theorem tailTrace_2475938 : CollatzResearch.WordTrace tailWord_2475938 prefixEnd_2475938 1271346264731839114888375 := by
  unfold tailWord_2475938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576219426026739347545117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60203251802737971593453645 22576219426026739347545117)
  ·
    refine ⟨8466082284760027255329419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22576219426026739347545117 8466082284760027255329419)
    ·
      refine ⟨12699123427140040882994129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8466082284760027255329419 12699123427140040882994129)
      ·
        refine ⟨9524342570355030662245597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12699123427140040882994129 9524342570355030662245597)
        ·
          refine ⟨3571628463883136498342099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9524342570355030662245597 3571628463883136498342099)
          ·
            refine ⟨5357442695824704747513149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571628463883136498342099 5357442695824704747513149)
            ·
              refine ⟨2009041010934264280317431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5357442695824704747513149 2009041010934264280317431)
              ·
                refine ⟨3013561516401396420476147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009041010934264280317431 3013561516401396420476147)
                ·
                  refine ⟨4520342274602094630714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013561516401396420476147 4520342274602094630714221)
                  ·
                    refine ⟨1695128352975785486517833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4520342274602094630714221 1695128352975785486517833)
                    ·
                      refine ⟨1271346264731839114888375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695128352975785486517833 1271346264731839114888375)
                      ·
                        rfl

theorem cell23_2475938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_2475938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475938 prefixEnd_2475938 := by exact prefixLift 2475938
  have htrace : WordTrace (prefixWord ++ tailWord_2475938) baseStart_2475938 baseEnd_2475938 := by
    simpa [prefixWord, tailWord_2475938, baseEnd_2475938] using wordTrace_append hprefix tailTrace_2475938
  have hstable : (prefixWord ++ tailWord_2475938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475938).length < 2 ^ (prefixWord ++ tailWord_2475938).sum := by decide
  have hdescent : baseEnd_2475938 < baseStart_2475938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475964 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2475964 : Nat := 118140960795 + 2475964 * 2 ^ 59
def prefixEnd_2475964 : Nat := 4983230072969 + 3 ^ 40 * 2475964 * 2
def baseEnd_2475964 : Nat := 1271359615228856013163255

theorem tailTrace_2475964 : CollatzResearch.WordTrace tailWord_2475964 prefixEnd_2475964 1271359615228856013163255 := by
  unfold tailWord_2475964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45152913001006381915313473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60203884001341842553751297 45152913001006381915313473)
  ·
    refine ⟨33864684750754786436485105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45152913001006381915313473 33864684750754786436485105)
    ·
      refine ⟨25398513563066089827363829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33864684750754786436485105 25398513563066089827363829)
      ·
        refine ⟨2381110646537445921315359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25398513563066089827363829 2381110646537445921315359)
        ·
          refine ⟨3571665969806168881973039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381110646537445921315359 3571665969806168881973039)
          ·
            refine ⟨5357498954709253322959559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571665969806168881973039 5357498954709253322959559)
            ·
              refine ⟨8036248432063879984439339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357498954709253322959559 8036248432063879984439339)
              ·
                refine ⟨12054372648095819976659009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036248432063879984439339 12054372648095819976659009)
                ·
                  refine ⟨9040779486071864982494257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12054372648095819976659009 9040779486071864982494257)
                  ·
                    refine ⟨6780584614553898736870693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9040779486071864982494257 6780584614553898736870693)
                    ·
                      refine ⟨1271359615228856013163255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6780584614553898736870693 1271359615228856013163255)
                      ·
                        rfl

theorem cell23_2475964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2475964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2475964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2475964 prefixEnd_2475964 := by exact prefixLift 2475964
  have htrace : WordTrace (prefixWord ++ tailWord_2475964) baseStart_2475964 baseEnd_2475964 := by
    simpa [prefixWord, tailWord_2475964, baseEnd_2475964] using wordTrace_append hprefix tailTrace_2475964
  have hstable : (prefixWord ++ tailWord_2475964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475964).length < 2 ^ (prefixWord ++ tailWord_2475964).sum := by decide
  have hdescent : baseEnd_2475964 < baseStart_2475964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476002 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2476002 : Nat := 118140960795 + 2476002 * 2 ^ 59
def prefixEnd_2476002 : Nat := 4983230072969 + 3 ^ 40 * 2476002 * 2
def baseEnd_2476002 : Nat := 1271379127493726864488081

theorem tailTrace_2476002 : CollatzResearch.WordTrace tailWord_2476002 prefixEnd_2476002 1271379127493726864488081 := by
  unfold tailWord_2476002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576802993968774080127565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60204807983916730880340173 22576802993968774080127565)
  ·
    refine ⟨8466301122738290280047837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22576802993968774080127565 8466301122738290280047837)
    ·
      refine ⟨3174862921026858855017939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8466301122738290280047837 3174862921026858855017939)
      ·
        refine ⟨4762294381540288282526909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174862921026858855017939 4762294381540288282526909)
        ·
          refine ⟨1785860393077608105947591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4762294381540288282526909 1785860393077608105947591)
          ·
            refine ⟨2678790589616412158921387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785860393077608105947591 2678790589616412158921387)
            ·
              refine ⟨4018185884424618238382081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678790589616412158921387 4018185884424618238382081)
              ·
                refine ⟨3013639413318463678786561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018185884424618238382081 3013639413318463678786561)
                ·
                  refine ⟨2260229559988847759089921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3013639413318463678786561 2260229559988847759089921)
                  ·
                    refine ⟨1695172169991635819317441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260229559988847759089921 1695172169991635819317441)
                    ·
                      refine ⟨1271379127493726864488081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695172169991635819317441 1271379127493726864488081)
                      ·
                        rfl

theorem cell23_2476002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2476002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476002 prefixEnd_2476002 := by exact prefixLift 2476002
  have htrace : WordTrace (prefixWord ++ tailWord_2476002) baseStart_2476002 baseEnd_2476002 := by
    simpa [prefixWord, tailWord_2476002, baseEnd_2476002] using wordTrace_append hprefix tailTrace_2476002
  have hstable : (prefixWord ++ tailWord_2476002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476002).length < 2 ^ (prefixWord ++ tailWord_2476002).sum := by decide
  have hdescent : baseEnd_2476002 < baseStart_2476002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476068 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_2476068 : Nat := 118140960795 + 2476068 * 2 ^ 59
def prefixEnd_2476068 : Nat := 4983230072969 + 3 ^ 40 * 2476068 * 2
def baseEnd_2476068 : Nat := 423804339072307868754259

theorem tailTrace_2476068 : CollatzResearch.WordTrace tailWord_2476068 prefixEnd_2476068 423804339072307868754259 := by
  unfold tailWord_2476068
  simp only [CollatzResearch.WordTrace]
  refine ⟨45154809596817994796206429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60206412795757326394941905 45154809596817994796206429)
  ·
    refine ⟨16933053598806748048577411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45154809596817994796206429 16933053598806748048577411)
    ·
      refine ⟨25399580398210122072866117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16933053598806748048577411 25399580398210122072866117)
      ·
        refine ⟨4762421324664397888662397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25399580398210122072866117 4762421324664397888662397)
        ·
          refine ⟨1785907996749149208248399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4762421324664397888662397 1785907996749149208248399)
          ·
            refine ⟨2678861995123723812372599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785907996749149208248399 2678861995123723812372599)
            ·
              refine ⟨4018292992685585718558899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678861995123723812372599 4018292992685585718558899)
              ·
                refine ⟨6027439489028378577838349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018292992685585718558899 6027439489028378577838349)
                ·
                  refine ⟨2260289808385641966689381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6027439489028378577838349 2260289808385641966689381)
                  ·
                    refine ⟨423804339072307868754259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260289808385641966689381 423804339072307868754259)
                    ·
                      rfl

theorem cell23_2476068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_2476068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476068 prefixEnd_2476068 := by exact prefixLift 2476068
  have htrace : WordTrace (prefixWord ++ tailWord_2476068) baseStart_2476068 baseEnd_2476068 := by
    simpa [prefixWord, tailWord_2476068, baseEnd_2476068] using wordTrace_append hprefix tailTrace_2476068
  have hstable : (prefixWord ++ tailWord_2476068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476068).length < 2 ^ (prefixWord ++ tailWord_2476068).sum := by decide
  have hdescent : baseEnd_2476068 < baseStart_2476068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476120 : List Nat := [2, 1, 2, 2, 1, 15]
def baseStart_2476120 : Nat := 118140960795 + 2476120 * 2 ^ 59
def prefixEnd_2476120 : Nat := 4983230072969 + 3 ^ 40 * 2476120 * 2
def baseEnd_2476120 : Nat := 5232262214859907007459

theorem tailTrace_2476120 : CollatzResearch.WordTrace tailWord_2476120 prefixEnd_2476120 5232262214859907007459 := by
  unfold tailWord_2476120
  simp only [CollatzResearch.WordTrace]
  refine ⟨45155757894723801236652907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60207677192965068315537209 45155757894723801236652907)
  ·
    refine ⟨67733636842085701854979361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45155757894723801236652907 67733636842085701854979361)
    ·
      refine ⟨50800227631564276391234521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67733636842085701854979361 50800227631564276391234521)
      ·
        refine ⟨38100170723673207293425891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50800227631564276391234521 38100170723673207293425891)
        ·
          refine ⟨57150256085509810940138837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38100170723673207293425891 57150256085509810940138837)
          ·
            refine ⟨5232262214859907007459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 57150256085509810940138837 5232262214859907007459)
            ·
              rfl

theorem cell23_2476120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 15].length) (baseStart_2476120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476120 prefixEnd_2476120 := by exact prefixLift 2476120
  have htrace : WordTrace (prefixWord ++ tailWord_2476120) baseStart_2476120 baseEnd_2476120 := by
    simpa [prefixWord, tailWord_2476120, baseEnd_2476120] using wordTrace_append hprefix tailTrace_2476120
  have hstable : (prefixWord ++ tailWord_2476120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476120).length < 2 ^ (prefixWord ++ tailWord_2476120).sum := by decide
  have hdescent : baseEnd_2476120 < baseStart_2476120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476125 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2476125 : Nat := 118140960795 + 2476125 * 2 ^ 59
def prefixEnd_2476125 : Nat := 4983230072969 + 3 ^ 40 * 2476125 * 2
def baseEnd_2476125 : Nat := 1271442285614229883250015

theorem tailTrace_2476125 : CollatzResearch.WordTrace tailWord_2476125 prefixEnd_2476125 1271442285614229883250015 := by
  unfold tailWord_2476125
  simp only [CollatzResearch.WordTrace]
  refine ⟨90311698154429488327237829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60207798769619658884825219 90311698154429488327237829)
  ·
    refine ⟨16933443403955529061357093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90311698154429488327237829 16933443403955529061357093)
    ·
      refine ⟨3175020638241661699004455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16933443403955529061357093 3175020638241661699004455)
      ·
        refine ⟨4762530957362492548506683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175020638241661699004455 4762530957362492548506683)
        ·
          refine ⟨7143796436043738822760025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762530957362492548506683 7143796436043738822760025)
          ·
            refine ⟨5357847327032804117070019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7143796436043738822760025 5357847327032804117070019)
            ·
              refine ⟨8036770990549206175605029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357847327032804117070019 8036770990549206175605029)
              ·
                refine ⟨1506894560727976157925943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8036770990549206175605029 1506894560727976157925943)
                ·
                  refine ⟨2260341841091964236888915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506894560727976157925943 2260341841091964236888915)
                  ·
                    refine ⟨3390512761637946355333373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2260341841091964236888915 3390512761637946355333373)
                    ·
                      refine ⟨1271442285614229883250015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390512761637946355333373 1271442285614229883250015)
                      ·
                        rfl

theorem cell23_2476125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2476125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476125 prefixEnd_2476125 := by exact prefixLift 2476125
  have htrace : WordTrace (prefixWord ++ tailWord_2476125) baseStart_2476125 baseEnd_2476125 := by
    simpa [prefixWord, tailWord_2476125, baseEnd_2476125] using wordTrace_append hprefix tailTrace_2476125
  have hstable : (prefixWord ++ tailWord_2476125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476125).length < 2 ^ (prefixWord ++ tailWord_2476125).sum := by decide
  have hdescent : baseEnd_2476125 < baseStart_2476125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476144 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_2476144 : Nat := 118140960795 + 2476144 * 2 ^ 59
def prefixEnd_2476144 : Nat := 4983230072969 + 3 ^ 40 * 2476144 * 2
def baseEnd_2476144 : Nat := 1271452041746665308912427

theorem tailTrace_2476144 : CollatzResearch.WordTrace tailWord_2476144 prefixEnd_2476144 1271452041746665308912427 := by
  unfold tailWord_2476144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45156195570680327286089743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60208260760907103048119657 45156195570680327286089743)
  ·
    refine ⟨67734293356020490929134615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45156195570680327286089743 67734293356020490929134615)
    ·
      refine ⟨101601440034030736393701923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67734293356020490929134615 101601440034030736393701923)
      ·
        refine ⟨152402160051046104590552885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101601440034030736393701923 152402160051046104590552885)
        ·
          refine ⟨14287702504785572305364333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152402160051046104590552885 14287702504785572305364333)
          ·
            refine ⟨5357888439294589614511625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14287702504785572305364333 5357888439294589614511625)
            ·
              refine ⟨4018416329470942210883719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5357888439294589614511625 4018416329470942210883719)
              ·
                refine ⟨6027624494206413316325579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018416329470942210883719 6027624494206413316325579)
                ·
                  refine ⟨9041436741309619974488369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027624494206413316325579 9041436741309619974488369)
                  ·
                    refine ⟨6781077555982214980866277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9041436741309619974488369 6781077555982214980866277)
                    ·
                      refine ⟨1271452041746665308912427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6781077555982214980866277 1271452041746665308912427)
                      ·
                        rfl

theorem cell23_2476144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_2476144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476144 prefixEnd_2476144 := by exact prefixLift 2476144
  have htrace : WordTrace (prefixWord ++ tailWord_2476144) baseStart_2476144 baseEnd_2476144 := by
    simpa [prefixWord, tailWord_2476144, baseEnd_2476144] using wordTrace_append hprefix tailTrace_2476144
  have hstable : (prefixWord ++ tailWord_2476144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476144).length < 2 ^ (prefixWord ++ tailWord_2476144).sum := by decide
  have hdescent : baseEnd_2476144 < baseStart_2476144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476164 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2476164 : Nat := 118140960795 + 2476164 * 2 ^ 59
def prefixEnd_2476164 : Nat := 4983230072969 + 3 ^ 40 * 2476164 * 2
def baseEnd_2476164 : Nat := 1271462311359755230662335

theorem tailTrace_2476164 : CollatzResearch.WordTrace tailWord_2476164 prefixEnd_2476164 1271462311359755230662335 := by
  unfold tailWord_2476164
  simp only [CollatzResearch.WordTrace]
  refine ⟨45156560300644098993953773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60208747067525465325271697 45156560300644098993953773)
  ·
    refine ⟨16933710112741537122732665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45156560300644098993953773 16933710112741537122732665)
    ·
      refine ⟨12700282584556152842049499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16933710112741537122732665 12700282584556152842049499)
      ·
        refine ⟨19050423876834229263074249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12700282584556152842049499 19050423876834229263074249)
        ·
          refine ⟨14287817907625671947305687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19050423876834229263074249 14287817907625671947305687)
          ·
            refine ⟨21431726861438507920958531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287817907625671947305687 21431726861438507920958531)
            ·
              refine ⟨32147590292157761881437797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21431726861438507920958531 32147590292157761881437797)
              ·
                refine ⟨6027673179779580352769587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32147590292157761881437797 6027673179779580352769587)
                ·
                  refine ⟨9041509769669370529154381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027673179779580352769587 9041509769669370529154381)
                  ·
                    refine ⟨3390566163626013948432893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9041509769669370529154381 3390566163626013948432893)
                    ·
                      refine ⟨1271462311359755230662335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390566163626013948432893 1271462311359755230662335)
                      ·
                        rfl

theorem cell23_2476164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2476164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476164 prefixEnd_2476164 := by exact prefixLift 2476164
  have htrace : WordTrace (prefixWord ++ tailWord_2476164) baseStart_2476164 baseEnd_2476164 := by
    simpa [prefixWord, tailWord_2476164, baseEnd_2476164] using wordTrace_append hprefix tailTrace_2476164
  have hstable : (prefixWord ++ tailWord_2476164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476164).length < 2 ^ (prefixWord ++ tailWord_2476164).sum := by decide
  have hdescent : baseEnd_2476164 < baseStart_2476164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476165 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_2476165 : Nat := 118140960795 + 2476165 * 2 ^ 59
def prefixEnd_2476165 : Nat := 4983230072969 + 3 ^ 40 * 2476165 * 2
def baseEnd_2476165 : Nat := 1271462824840409726749831

theorem tailTrace_2476165 : CollatzResearch.WordTrace tailWord_2476165 prefixEnd_2476165 1271462824840409726749831 := by
  unfold tailWord_2476165
  simp only [CollatzResearch.WordTrace]
  refine ⟨90313157074284575158693949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60208771382856383439129299 90313157074284575158693949)
  ·
    refine ⟨33867433902856715684510231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90313157074284575158693949 33867433902856715684510231)
    ·
      refine ⟨50801150854285073526765347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33867433902856715684510231 50801150854285073526765347)
      ·
        refine ⟨76201726281427610290148021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50801150854285073526765347 76201726281427610290148021)
        ·
          refine ⟨7143911838883838464701377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76201726281427610290148021 7143911838883838464701377)
          ·
            refine ⟨5357933879162878848526033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7143911838883838464701377 5357933879162878848526033)
            ·
              refine ⟨4018450409372159136394525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5357933879162878848526033 4018450409372159136394525)
              ·
                refine ⟨1506918903514559676147947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4018450409372159136394525 1506918903514559676147947)
                ·
                  refine ⟨2260378355271839514221921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506918903514559676147947 2260378355271839514221921)
                  ·
                    refine ⟨1695283766453879635666441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260378355271839514221921 1695283766453879635666441)
                    ·
                      refine ⟨1271462824840409726749831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695283766453879635666441 1271462824840409726749831)
                      ·
                        rfl

theorem cell23_2476165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_2476165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476165 prefixEnd_2476165 := by exact prefixLift 2476165
  have htrace : WordTrace (prefixWord ++ tailWord_2476165) baseStart_2476165 baseEnd_2476165 := by
    simpa [prefixWord, tailWord_2476165, baseEnd_2476165] using wordTrace_append hprefix tailTrace_2476165
  have hstable : (prefixWord ++ tailWord_2476165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476165).length < 2 ^ (prefixWord ++ tailWord_2476165).sum := by decide
  have hdescent : baseEnd_2476165 < baseStart_2476165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476168 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2476168 : Nat := 118140960795 + 2476168 * 2 ^ 59
def prefixEnd_2476168 : Nat := 4983230072969 + 3 ^ 40 * 2476168 * 2
def baseEnd_2476168 : Nat := 1271464365282373215012317

theorem tailTrace_2476168 : CollatzResearch.WordTrace tailWord_2476168 prefixEnd_2476168 1271464365282373215012317 := by
  unfold tailWord_2476168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45156633246636853335526579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60208844328849137780702105 45156633246636853335526579)
  ·
    refine ⟨67734949869955280003289869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45156633246636853335526579 67734949869955280003289869)
    ·
      refine ⟨25400606201233230001233701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67734949869955280003289869 25400606201233230001233701)
      ·
        refine ⟨4762613662731230625231319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25400606201233230001233701 4762613662731230625231319)
        ·
          refine ⟨7143920494096845937846979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762613662731230625231319 7143920494096845937846979)
          ·
            refine ⟨10715880741145268906770469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143920494096845937846979 10715880741145268906770469)
            ·
              refine ⟨2009227638964737920019463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10715880741145268906770469 2009227638964737920019463)
              ·
                refine ⟨3013841458447106880029195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009227638964737920019463 3013841458447106880029195)
                ·
                  refine ⟨4520762187670660320043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013841458447106880029195 4520762187670660320043793)
                  ·
                    refine ⟨3390571640752995240032845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520762187670660320043793 3390571640752995240032845)
                    ·
                      refine ⟨1271464365282373215012317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390571640752995240032845 1271464365282373215012317)
                      ·
                        rfl

theorem cell23_2476168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2476168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476168 prefixEnd_2476168 := by exact prefixLift 2476168
  have htrace : WordTrace (prefixWord ++ tailWord_2476168) baseStart_2476168 baseEnd_2476168 := by
    simpa [prefixWord, tailWord_2476168, baseEnd_2476168] using wordTrace_append hprefix tailTrace_2476168
  have hstable : (prefixWord ++ tailWord_2476168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476168).length < 2 ^ (prefixWord ++ tailWord_2476168).sum := by decide
  have hdescent : baseEnd_2476168 < baseStart_2476168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476197 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_2476197 : Nat := 118140960795 + 2476197 * 2 ^ 59
def prefixEnd_2476197 : Nat := 4983230072969 + 3 ^ 40 * 2476197 * 2
def baseEnd_2476197 : Nat := 423826418740451200516561

theorem tailTrace_2476197 : CollatzResearch.WordTrace tailWord_2476197 prefixEnd_2476197 423826418740451200516561 := by
  unfold tailWord_2476197
  simp only [CollatzResearch.WordTrace]
  refine ⟨90314324210168644623858845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60209549473445763082572563 90314324210168644623858845)
  ·
    refine ⟨33867871578813241733947067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90314324210168644623858845 33867871578813241733947067)
    ·
      refine ⟨50801807368219862600920601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33867871578813241733947067 50801807368219862600920601)
      ·
        refine ⟨38101355526164896950690451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50801807368219862600920601 38101355526164896950690451)
        ·
          refine ⟨57152033289247345426035677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38101355526164896950690451 57152033289247345426035677)
          ·
            refine ⟨21432012483467754534763379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57152033289247345426035677 21432012483467754534763379)
            ·
              refine ⟨32148018725201631802145069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21432012483467754534763379 32148018725201631802145069)
              ·
                refine ⟨12055507021950611925804401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32148018725201631802145069 12055507021950611925804401)
                ·
                  refine ⟨9041630266462958944353301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12055507021950611925804401 9041630266462958944353301)
                  ·
                    refine ⟨423826418740451200516561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9041630266462958944353301 423826418740451200516561)
                    ·
                      rfl

theorem cell23_2476197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_2476197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476197 prefixEnd_2476197 := by exact prefixLift 2476197
  have htrace : WordTrace (prefixWord ++ tailWord_2476197) baseStart_2476197 baseEnd_2476197 := by
    simpa [prefixWord, tailWord_2476197, baseEnd_2476197] using wordTrace_append hprefix tailTrace_2476197
  have hstable : (prefixWord ++ tailWord_2476197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476197).length < 2 ^ (prefixWord ++ tailWord_2476197).sum := by decide
  have hdescent : baseEnd_2476197 < baseStart_2476197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476207 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_2476207 : Nat := 118140960795 + 2476207 * 2 ^ 59
def prefixEnd_2476207 : Nat := 4983230072969 + 3 ^ 40 * 2476207 * 2
def baseEnd_2476207 : Nat := 1271484391027898562424637

theorem tailTrace_2476207 : CollatzResearch.WordTrace tailWord_2476207 prefixEnd_2476207 1271484391027898562424637 := by
  unfold tailWord_2476207
  simp only [CollatzResearch.WordTrace]
  refine ⟨90314688940132416331722875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60209792626754944221148583 90314688940132416331722875)
  ·
    refine ⟨135472033410198624497584313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90314688940132416331722875 135472033410198624497584313)
    ·
      refine ⟨101604025057648968373188235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135472033410198624497584313 101604025057648968373188235)
      ·
        refine ⟨152406037586473452559782353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101604025057648968373188235 152406037586473452559782353)
        ·
          refine ⟨114304528189855089419836765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152406037586473452559782353 114304528189855089419836765)
          ·
            refine ⟨42864198071195658532438787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114304528189855089419836765 42864198071195658532438787)
            ·
              refine ⟨64296297106793487798658181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42864198071195658532438787 64296297106793487798658181)
              ·
                refine ⟨12055555707523778962248409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64296297106793487798658181 12055555707523778962248409)
                ·
                  refine ⟨9041666780642834221686307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12055555707523778962248409 9041666780642834221686307)
                  ·
                    refine ⟨13562500170964251332529461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9041666780642834221686307 13562500170964251332529461)
                    ·
                      refine ⟨1271484391027898562424637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13562500170964251332529461 1271484391027898562424637)
                      ·
                        rfl

theorem cell23_2476207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_2476207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476207 prefixEnd_2476207 := by exact prefixLift 2476207
  have htrace : WordTrace (prefixWord ++ tailWord_2476207) baseStart_2476207 baseEnd_2476207 := by
    simpa [prefixWord, tailWord_2476207, baseEnd_2476207] using wordTrace_append hprefix tailTrace_2476207
  have hstable : (prefixWord ++ tailWord_2476207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476207).length < 2 ^ (prefixWord ++ tailWord_2476207).sum := by decide
  have hdescent : baseEnd_2476207 < baseStart_2476207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476224 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_2476224 : Nat := 118140960795 + 2476224 * 2 ^ 59
def prefixEnd_2476224 : Nat := 4983230072969 + 3 ^ 40 * 2476224 * 2
def baseEnd_2476224 : Nat := 1271493120199024995912059

theorem tailTrace_2476224 : CollatzResearch.WordTrace tailWord_2476224 prefixEnd_2476224 1271493120199024995912059 := by
  unfold tailWord_2476224
  simp only [CollatzResearch.WordTrace]
  refine ⟨45157654490535414117545863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60210205987380552156727817 45157654490535414117545863)
  ·
    refine ⟨67736481735803121176318795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45157654490535414117545863 67736481735803121176318795)
    ·
      refine ⟨101604722603704681764478193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67736481735803121176318795 101604722603704681764478193)
      ·
        refine ⟨76203541952778511323358645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101604722603704681764478193 76203541952778511323358645)
        ·
          refine ⟨7144082058072985436564873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76203541952778511323358645 7144082058072985436564873)
          ·
            refine ⟨5358061543554739077423655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144082058072985436564873 5358061543554739077423655)
            ·
              refine ⟨8037092315332108616135483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358061543554739077423655 8037092315332108616135483)
              ·
                refine ⟨12055638472998162924203225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037092315332108616135483 12055638472998162924203225)
                ·
                  refine ⟨9041728854748622193152419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12055638472998162924203225 9041728854748622193152419)
                  ·
                    refine ⟨13562593282122933289728629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9041728854748622193152419 13562593282122933289728629)
                    ·
                      refine ⟨1271493120199024995912059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13562593282122933289728629 1271493120199024995912059)
                      ·
                        rfl

theorem cell23_2476224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_2476224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476224 prefixEnd_2476224 := by exact prefixLift 2476224
  have htrace : WordTrace (prefixWord ++ tailWord_2476224) baseStart_2476224 baseEnd_2476224 := by
    simpa [prefixWord, tailWord_2476224, baseEnd_2476224] using wordTrace_append hprefix tailTrace_2476224
  have hstable : (prefixWord ++ tailWord_2476224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476224).length < 2 ^ (prefixWord ++ tailWord_2476224).sum := by decide
  have hdescent : baseEnd_2476224 < baseStart_2476224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476238 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_2476238 : Nat := 118140960795 + 2476238 * 2 ^ 59
def prefixEnd_2476238 : Nat := 4983230072969 + 3 ^ 40 * 2476238 * 2
def baseEnd_2476238 : Nat := 1271500308928187941136995

theorem tailTrace_2476238 : CollatzResearch.WordTrace tailWord_2476238 prefixEnd_2476238 1271500308928187941136995 := by
  unfold tailWord_2476238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289477450377513578262671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60210546402013405750734245 11289477450377513578262671)
  ·
    refine ⟨16934216175566270367394007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289477450377513578262671 16934216175566270367394007)
    ·
      refine ⟨25401324263349405551091011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16934216175566270367394007 25401324263349405551091011)
      ·
        refine ⟨38101986395024108326636517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25401324263349405551091011 38101986395024108326636517)
        ·
          refine ⟨7144122449067020311244347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38101986395024108326636517 7144122449067020311244347)
          ·
            refine ⟨10716183673600530466866521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144122449067020311244347 10716183673600530466866521)
            ·
              refine ⟨8037137755200397850149891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10716183673600530466866521 8037137755200397850149891)
              ·
                refine ⟨12055706632800596775224837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037137755200397850149891 12055706632800596775224837)
                ·
                  refine ⟨2260444993650111895354657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12055706632800596775224837 2260444993650111895354657)
                  ·
                    refine ⟨1695333745237583921515993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260444993650111895354657 1695333745237583921515993)
                    ·
                      refine ⟨1271500308928187941136995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695333745237583921515993 1271500308928187941136995)
                      ·
                        rfl

theorem cell23_2476238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_2476238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476238 prefixEnd_2476238 := by exact prefixLift 2476238
  have htrace : WordTrace (prefixWord ++ tailWord_2476238) baseStart_2476238 baseEnd_2476238 := by
    simpa [prefixWord, tailWord_2476238, baseEnd_2476238] using wordTrace_append hprefix tailTrace_2476238
  have hstable : (prefixWord ++ tailWord_2476238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476238).length < 2 ^ (prefixWord ++ tailWord_2476238).sum := by decide
  have hdescent : baseEnd_2476238 < baseStart_2476238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476267 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_2476267 : Nat := 118140960795 + 2476267 * 2 ^ 59
def prefixEnd_2476267 : Nat := 4983230072969 + 3 ^ 40 * 2476267 * 2
def baseEnd_2476267 : Nat := 1271515199867168327674361

theorem tailTrace_2476267 : CollatzResearch.WordTrace tailWord_2476267 prefixEnd_2476267 1271515199867168327674361 := by
  unfold tailWord_2476267
  simp only [CollatzResearch.WordTrace]
  refine ⟨90316877319915046578907055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60211251546610031052604703 90316877319915046578907055)
  ·
    refine ⟨135475315979872569868360583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90316877319915046578907055 135475315979872569868360583)
    ·
      refine ⟨203212973969808854802540875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135475315979872569868360583 203212973969808854802540875)
      ·
        refine ⟨304819460954713282203811313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203212973969808854802540875 304819460954713282203811313)
        ·
          refine ⟨228614595716034961652858485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304819460954713282203811313 228614595716034961652858485)
          ·
            refine ⟨21432618348378277654955483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228614595716034961652858485 21432618348378277654955483)
            ·
              refine ⟨32148927522567416482433225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21432618348378277654955483 32148927522567416482433225)
              ·
                refine ⟨24111695641925562361824919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32148927522567416482433225 24111695641925562361824919)
                ·
                  refine ⟨36167543462888343542737379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24111695641925562361824919 36167543462888343542737379)
                  ·
                    refine ⟨54251315194332515314106069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36167543462888343542737379 54251315194332515314106069)
                    ·
                      refine ⟨1271515199867168327674361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54251315194332515314106069 1271515199867168327674361)
                      ·
                        rfl

theorem cell23_2476267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_2476267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476267 prefixEnd_2476267 := by exact prefixLift 2476267
  have htrace : WordTrace (prefixWord ++ tailWord_2476267) baseStart_2476267 baseEnd_2476267 := by
    simpa [prefixWord, tailWord_2476267, baseEnd_2476267] using wordTrace_append hprefix tailTrace_2476267
  have hstable : (prefixWord ++ tailWord_2476267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476267).length < 2 ^ (prefixWord ++ tailWord_2476267).sum := by decide
  have hdescent : baseEnd_2476267 < baseStart_2476267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476284 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2476284 : Nat := 118140960795 + 2476284 * 2 ^ 59
def prefixEnd_2476284 : Nat := 4983230072969 + 3 ^ 40 * 2476284 * 2
def baseEnd_2476284 : Nat := 1271523929038294761161783

theorem tailTrace_2476284 : CollatzResearch.WordTrace tailWord_2476284 prefixEnd_2476284 1271523929038294761161783 := by
  unfold tailWord_2476284
  simp only [CollatzResearch.WordTrace]
  refine ⟨45158748680426729241137953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60211664907235638988183937 45158748680426729241137953)
  ·
    refine ⟨33869061510320046930853465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45158748680426729241137953 33869061510320046930853465)
    ·
      refine ⟨25401796132740035198140099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33869061510320046930853465 25401796132740035198140099)
      ·
        refine ⟨38102694199110052797210149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25401796132740035198140099 38102694199110052797210149)
        ·
          refine ⟨7144255162333134899476903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38102694199110052797210149 7144255162333134899476903)
          ·
            refine ⟨10716382743499702349215355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144255162333134899476903 10716382743499702349215355)
            ·
              refine ⟨16074574115249553523823033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716382743499702349215355 16074574115249553523823033)
              ·
                refine ⟨12055930586437165142867275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16074574115249553523823033 12055930586437165142867275)
                ·
                  refine ⟨18083895879655747714300913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12055930586437165142867275 18083895879655747714300913)
                  ·
                    refine ⟨13562921909741810785725685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18083895879655747714300913 13562921909741810785725685)
                    ·
                      refine ⟨1271523929038294761161783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13562921909741810785725685 1271523929038294761161783)
                      ·
                        rfl

theorem cell23_2476284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2476284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476284 prefixEnd_2476284 := by exact prefixLift 2476284
  have htrace : WordTrace (prefixWord ++ tailWord_2476284) baseStart_2476284 baseEnd_2476284 := by
    simpa [prefixWord, tailWord_2476284, baseEnd_2476284] using wordTrace_append hprefix tailTrace_2476284
  have hstable : (prefixWord ++ tailWord_2476284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476284).length < 2 ^ (prefixWord ++ tailWord_2476284).sum := by decide
  have hdescent : baseEnd_2476284 < baseStart_2476284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476311 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2476311 : Nat := 118140960795 + 2476311 * 2 ^ 59
def prefixEnd_2476311 : Nat := 4983230072969 + 3 ^ 40 * 2476311 * 2
def baseEnd_2476311 : Nat := 1271537793015966155524159

theorem tailTrace_2476311 : CollatzResearch.WordTrace tailWord_2476311 prefixEnd_2476311 1271537793015966155524159 := by
  unfold tailWord_2476311
  simp only [CollatzResearch.WordTrace]
  refine ⟨90318482131755642093508787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60212321421170428062339191 90318482131755642093508787)
  ·
    refine ⟨135477723197633463140263181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90318482131755642093508787 135477723197633463140263181)
    ·
      refine ⟨50804146199112548677598693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135477723197633463140263181 50804146199112548677598693)
      ·
        refine ⟨9525777412333602877049755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50804146199112548677598693 9525777412333602877049755)
        ·
          refine ⟨14288666118500404315574633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525777412333602877049755 14288666118500404315574633)
          ·
            refine ⟨10716499588875303236680975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14288666118500404315574633 10716499588875303236680975)
            ·
              refine ⟨16074749383312954855021463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716499588875303236680975 16074749383312954855021463)
              ·
                refine ⟨24112124074969432282532195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16074749383312954855021463 24112124074969432282532195)
                ·
                  refine ⟨36168186112454148423798293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24112124074969432282532195 36168186112454148423798293)
                  ·
                    refine ⟨1695383724021288207365545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36168186112454148423798293 1695383724021288207365545)
                    ·
                      refine ⟨1271537793015966155524159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695383724021288207365545 1271537793015966155524159)
                      ·
                        rfl

theorem cell23_2476311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2476311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476311 prefixEnd_2476311 := by exact prefixLift 2476311
  have htrace : WordTrace (prefixWord ++ tailWord_2476311) baseStart_2476311 baseEnd_2476311 := by
    simpa [prefixWord, tailWord_2476311, baseEnd_2476311] using wordTrace_append hprefix tailTrace_2476311
  have hstable : (prefixWord ++ tailWord_2476311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476311).length < 2 ^ (prefixWord ++ tailWord_2476311).sum := by decide
  have hdescent : baseEnd_2476311 < baseStart_2476311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476371 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 6, 3, 2]
def baseStart_2476371 : Nat := 118140960795 + 2476371 * 2 ^ 59
def prefixEnd_2476371 : Nat := 4983230072969 + 3 ^ 40 * 2476371 * 2
def baseEnd_2476371 : Nat := 1271568601855235920773883

theorem tailTrace_2476371 : CollatzResearch.WordTrace tailWord_2476371 prefixEnd_2476371 1271568601855235920773883 := by
  unfold tailWord_2476371
  simp only [CollatzResearch.WordTrace]
  refine ⟨90320670511538272340692967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60213780341025514893795311 90320670511538272340692967)
  ·
    refine ⟨135481005767307408511039451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90320670511538272340692967 135481005767307408511039451)
    ·
      refine ⟨203221508650961112766559177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135481005767307408511039451 203221508650961112766559177)
      ·
        refine ⟨152416131488220834574919383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203221508650961112766559177 152416131488220834574919383)
        ·
          refine ⟨228624197232331251862379075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152416131488220834574919383 228624197232331251862379075)
          ·
            refine ⟨342936295848496877793568613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228624197232331251862379075 342936295848496877793568613)
            ·
              refine ⟨64300555471593164586294115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342936295848496877793568613 64300555471593164586294115)
              ·
                refine ⟨96450833207389746879441173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64300555471593164586294115 96450833207389746879441173)
                ·
                  refine ⟨4521132806596394384973805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96450833207389746879441173 4521132806596394384973805)
                  ·
                    refine ⟨1695424802473647894365177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4521132806596394384973805 1695424802473647894365177)
                    ·
                      refine ⟨1271568601855235920773883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695424802473647894365177 1271568601855235920773883)
                      ·
                        rfl

theorem cell23_2476371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3, 2].length) (baseStart_2476371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476371 prefixEnd_2476371 := by exact prefixLift 2476371
  have htrace : WordTrace (prefixWord ++ tailWord_2476371) baseStart_2476371 baseEnd_2476371 := by
    simpa [prefixWord, tailWord_2476371, baseEnd_2476371] using wordTrace_append hprefix tailTrace_2476371
  have hstable : (prefixWord ++ tailWord_2476371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476371).length < 2 ^ (prefixWord ++ tailWord_2476371).sum := by decide
  have hdescent : baseEnd_2476371 < baseStart_2476371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476388 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_2476388 : Nat := 118140960795 + 2476388 * 2 ^ 59
def prefixEnd_2476388 : Nat := 4983230072969 + 3 ^ 40 * 2476388 * 2
def baseEnd_2476388 : Nat := 1271577331026362354261305

theorem tailTrace_2476388 : CollatzResearch.WordTrace tailWord_2476388 prefixEnd_2476388 1271577331026362354261305 := by
  unfold tailWord_2476388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45160645276238342122030909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60214193701651122829374545 45160645276238342122030909)
  ·
    refine ⟨16935241978589378295761591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45160645276238342122030909 16935241978589378295761591)
    ·
      refine ⟨25402862967884067443642387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16935241978589378295761591 25402862967884067443642387)
      ·
        refine ⟨38104294451826101165463581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25402862967884067443642387 38104294451826101165463581)
        ·
          refine ⟨14289110419434787937048843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38104294451826101165463581 14289110419434787937048843)
          ·
            refine ⟨21433665629152181905573265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14289110419434787937048843 21433665629152181905573265)
            ·
              refine ⟨16075249221864136429179949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21433665629152181905573265 16075249221864136429179949)
              ·
                refine ⟨6028218458199051160942481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16075249221864136429179949 6028218458199051160942481)
                ·
                  refine ⟨4521163843649288370706861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028218458199051160942481 4521163843649288370706861)
                  ·
                    refine ⟨1695436441368483139015073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4521163843649288370706861 1695436441368483139015073)
                    ·
                      refine ⟨1271577331026362354261305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695436441368483139015073 1271577331026362354261305)
                      ·
                        rfl

theorem cell23_2476388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_2476388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476388 prefixEnd_2476388 := by exact prefixLift 2476388
  have htrace : WordTrace (prefixWord ++ tailWord_2476388) baseStart_2476388 baseEnd_2476388 := by
    simpa [prefixWord, tailWord_2476388, baseEnd_2476388] using wordTrace_append hprefix tailTrace_2476388
  have hstable : (prefixWord ++ tailWord_2476388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476388).length < 2 ^ (prefixWord ++ tailWord_2476388).sum := by decide
  have hdescent : baseEnd_2476388 < baseStart_2476388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476405 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2476405 : Nat := 118140960795 + 2476405 * 2 ^ 59
def prefixEnd_2476405 : Nat := 4983230072969 + 3 ^ 40 * 2476405 * 2
def baseEnd_2476405 : Nat := 1271586060197488787748727

theorem tailTrace_2476405 : CollatzResearch.WordTrace tailWord_2476405 prefixEnd_2476405 1271586060197488787748727 := by
  unfold tailWord_2476405
  simp only [CollatzResearch.WordTrace]
  refine ⟨90321910593415096147430669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60214607062276730764953779 90321910593415096147430669)
  ·
    refine ⟨33870716472530661055286501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90321910593415096147430669 33870716472530661055286501)
    ·
      refine ⟨6350759338599498947866219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33870716472530661055286501 6350759338599498947866219)
      ·
        refine ⟨9526139007899248421799329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6350759338599498947866219 9526139007899248421799329)
        ·
          refine ⟨7144604255924436316349497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9526139007899248421799329 7144604255924436316349497)
          ·
            refine ⟨5358453191943327237262123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144604255924436316349497 5358453191943327237262123)
            ·
              refine ⟨8037679787914990855893185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358453191943327237262123 8037679787914990855893185)
              ·
                refine ⟨6028259840936243141919889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8037679787914990855893185 6028259840936243141919889)
                ·
                  refine ⟨4521194880702182356439917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028259840936243141919889 4521194880702182356439917)
                  ·
                    refine ⟨1695448080263318383664969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4521194880702182356439917 1695448080263318383664969)
                    ·
                      refine ⟨1271586060197488787748727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695448080263318383664969 1271586060197488787748727)
                      ·
                        rfl

theorem cell23_2476405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2476405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476405 prefixEnd_2476405 := by exact prefixLift 2476405
  have htrace : WordTrace (prefixWord ++ tailWord_2476405) baseStart_2476405 baseEnd_2476405 := by
    simpa [prefixWord, tailWord_2476405, baseEnd_2476405] using wordTrace_append hprefix tailTrace_2476405
  have hstable : (prefixWord ++ tailWord_2476405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476405).length < 2 ^ (prefixWord ++ tailWord_2476405).sum := by decide
  have hdescent : baseEnd_2476405 < baseStart_2476405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476411 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 4, 4]
def baseStart_2476411 : Nat := 118140960795 + 2476411 * 2 ^ 59
def prefixEnd_2476411 : Nat := 4983230072969 + 3 ^ 40 * 2476411 * 2
def baseEnd_2476411 : Nat := 423863047027138588091233

theorem tailTrace_2476411 : CollatzResearch.WordTrace tailWord_2476411 prefixEnd_2476411 423863047027138588091233 := by
  unfold tailWord_2476411
  simp only [CollatzResearch.WordTrace]
  refine ⟨90322129431393359172149087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60214752954262239448099391 90322129431393359172149087)
  ·
    refine ⟨135483194147090038758223631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90322129431393359172149087 135483194147090038758223631)
    ·
      refine ⟨203224791220635058137335447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135483194147090038758223631 203224791220635058137335447)
      ·
        refine ⟨304837186830952587206003171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203224791220635058137335447 304837186830952587206003171)
        ·
          refine ⟨457255780246428880809004757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304837186830952587206003171 457255780246428880809004757)
          ·
            refine ⟨10716932349525676893961049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 457255780246428880809004757 10716932349525676893961049)
            ·
              refine ⟨8037699262144257670470787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10716932349525676893961049 8037699262144257670470787)
              ·
                refine ⟨12056548893216386505706181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037699262144257670470787 12056548893216386505706181)
                ·
                  refine ⟨2260602917478072469819909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12056548893216386505706181 2260602917478072469819909)
                  ·
                    refine ⟨423863047027138588091233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260602917478072469819909 423863047027138588091233)
                    ·
                      rfl

theorem cell23_2476411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 4].length) (baseStart_2476411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476411 prefixEnd_2476411 := by exact prefixLift 2476411
  have htrace : WordTrace (prefixWord ++ tailWord_2476411) baseStart_2476411 baseEnd_2476411 := by
    simpa [prefixWord, tailWord_2476411, baseEnd_2476411] using wordTrace_append hprefix tailTrace_2476411
  have hstable : (prefixWord ++ tailWord_2476411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476411).length < 2 ^ (prefixWord ++ tailWord_2476411).sum := by decide
  have hdescent : baseEnd_2476411 < baseStart_2476411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476421 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_2476421 : Nat := 118140960795 + 2476421 * 2 ^ 59
def prefixEnd_2476421 : Nat := 4983230072969 + 3 ^ 40 * 2476421 * 2
def baseEnd_2476421 : Nat := 1271594275887960725148653

theorem tailTrace_2476421 : CollatzResearch.WordTrace tailWord_2476421 prefixEnd_2476421 1271594275887960725148653 := by
  unfold tailWord_2476421
  simp only [CollatzResearch.WordTrace]
  refine ⟨90322494161357130880013117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60214996107571420586675411 90322494161357130880013117)
  ·
    refine ⟨33870935310508924080004919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90322494161357130880013117 33870935310508924080004919)
    ·
      refine ⟨50806402965763386120007379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33870935310508924080004919 50806402965763386120007379)
      ·
        refine ⟨76209604448645079180011069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50806402965763386120007379 76209604448645079180011069)
        ·
          refine ⟨28578601668241904692504151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76209604448645079180011069 28578601668241904692504151)
          ·
            refine ⟨42867902502362857038756227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28578601668241904692504151 42867902502362857038756227)
            ·
              refine ⟨64301853753544285558134341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42867902502362857038756227 64301853753544285558134341)
              ·
                refine ⟨12056597578789553542150189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64301853753544285558134341 12056597578789553542150189)
                ·
                  refine ⟨4521224092046082578306321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12056597578789553542150189 4521224092046082578306321)
                  ·
                    refine ⟨3390918069034561933729741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521224092046082578306321 3390918069034561933729741)
                    ·
                      refine ⟨1271594275887960725148653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390918069034561933729741 1271594275887960725148653)
                      ·
                        rfl

theorem cell23_2476421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_2476421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476421 prefixEnd_2476421 := by exact prefixLift 2476421
  have htrace : WordTrace (prefixWord ++ tailWord_2476421) baseStart_2476421 baseEnd_2476421 := by
    simpa [prefixWord, tailWord_2476421, baseEnd_2476421] using wordTrace_append hprefix tailTrace_2476421
  have hstable : (prefixWord ++ tailWord_2476421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476421).length < 2 ^ (prefixWord ++ tailWord_2476421).sum := by decide
  have hdescent : baseEnd_2476421 < baseStart_2476421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476428 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_2476428 : Nat := 118140960795 + 2476428 * 2 ^ 59
def prefixEnd_2476428 : Nat := 4983230072969 + 3 ^ 40 * 2476428 * 2
def baseEnd_2476428 : Nat := 423865956750847399253707

theorem tailTrace_2476428 : CollatzResearch.WordTrace tailWord_2476428 prefixEnd_2476428 423865956750847399253707 := by
  unfold tailWord_2476428
  simp only [CollatzResearch.WordTrace]
  refine ⟨45161374736165885537758969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60215166314887847383678625 45161374736165885537758969)
  ·
    refine ⟨33871031052124414153319227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45161374736165885537758969 33871031052124414153319227)
    ·
      refine ⟨50806546578186621229978841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33871031052124414153319227 50806546578186621229978841)
      ·
        refine ⟨38104909933639965922484131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50806546578186621229978841 38104909933639965922484131)
        ·
          refine ⟨57157364900459948883726197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38104909933639965922484131 57157364900459948883726197)
          ·
            refine ⟨5358502959418120207849331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57157364900459948883726197 5358502959418120207849331)
            ·
              refine ⟨8037754439127180311773997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358502959418120207849331 8037754439127180311773997)
              ·
                refine ⟨3014157914672692616915249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8037754439127180311773997 3014157914672692616915249)
                ·
                  refine ⟨2260618436004519462686437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014157914672692616915249 2260618436004519462686437)
                  ·
                    refine ⟨423865956750847399253707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260618436004519462686437 423865956750847399253707)
                    ·
                      rfl

theorem cell23_2476428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_2476428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476428 prefixEnd_2476428 := by exact prefixLift 2476428
  have htrace : WordTrace (prefixWord ++ tailWord_2476428) baseStart_2476428 baseEnd_2476428 := by
    simpa [prefixWord, tailWord_2476428, baseEnd_2476428] using wordTrace_append hprefix tailTrace_2476428
  have hstable : (prefixWord ++ tailWord_2476428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476428).length < 2 ^ (prefixWord ++ tailWord_2476428).sum := by decide
  have hdescent : baseEnd_2476428 < baseStart_2476428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476451 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3]
def baseStart_2476451 : Nat := 118140960795 + 2476451 * 2 ^ 59
def prefixEnd_2476451 : Nat := 4983230072969 + 3 ^ 40 * 2476451 * 2
def baseEnd_2476451 : Nat := 1271609680307595607773515

theorem tailTrace_2476451 : CollatzResearch.WordTrace tailWord_2476451 prefixEnd_2476451 1271609680307595607773515 := by
  unfold tailWord_2476451
  simp only [CollatzResearch.WordTrace]
  refine ⟨90323588351248446003605207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60215725567498964002403471 90323588351248446003605207)
  ·
    refine ⟨135485382526872669005407811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90323588351248446003605207 135485382526872669005407811)
    ·
      refine ⟨203228073790309003508111717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135485382526872669005407811 203228073790309003508111717)
      ·
        refine ⟨38105263835682938157770947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203228073790309003508111717 38105263835682938157770947)
        ·
          refine ⟨57157895753524407236656421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38105263835682938157770947 57157895753524407236656421)
          ·
            refine ⟨10717105453785826356873079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57157895753524407236656421 10717105453785826356873079)
            ·
              refine ⟨16075658180678739535309619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10717105453785826356873079 16075658180678739535309619)
              ·
                refine ⟨24113487271018109302964429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16075658180678739535309619 24113487271018109302964429)
                ·
                  refine ⟨9042557726631790988611661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24113487271018109302964429 9042557726631790988611661)
                  ·
                    refine ⟨3390959147486921620729373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9042557726631790988611661 3390959147486921620729373)
                    ·
                      refine ⟨1271609680307595607773515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3390959147486921620729373 1271609680307595607773515)
                      ·
                        rfl

theorem cell23_2476451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_2476451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476451 prefixEnd_2476451 := by exact prefixLift 2476451
  have htrace : WordTrace (prefixWord ++ tailWord_2476451) baseStart_2476451 baseEnd_2476451 := by
    simpa [prefixWord, tailWord_2476451, baseEnd_2476451] using wordTrace_append hprefix tailTrace_2476451
  have hstable : (prefixWord ++ tailWord_2476451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476451).length < 2 ^ (prefixWord ++ tailWord_2476451).sum := by decide
  have hdescent : baseEnd_2476451 < baseStart_2476451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476458 : List Nat := [3, 1, 6, 1, 12]
def baseStart_2476458 : Nat := 118140960795 + 2476458 * 2 ^ 59
def prefixEnd_2476458 : Nat := 4983230072969 + 3 ^ 40 * 2476458 * 2
def baseEnd_2476458 : Nat := 1744325479660050864727

theorem tailTrace_2476458 : CollatzResearch.WordTrace tailWord_2476458 prefixEnd_2476458 1744325479660050864727 := by
  unfold tailWord_2476458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22580960915555771549777507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60215895774815390799406685 22580960915555771549777507)
  ·
    refine ⟨33871441373333657324666261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22580960915555771549777507 33871441373333657324666261)
    ·
      refine ⟨1587723814375015187093731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33871441373333657324666261 1587723814375015187093731)
      ·
        refine ⟨2381585721562522780640597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587723814375015187093731 2381585721562522780640597)
        ·
          refine ⟨1744325479660050864727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2381585721562522780640597 1744325479660050864727)
          ·
            rfl

theorem cell23_2476458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 12].length) (baseStart_2476458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476458 prefixEnd_2476458 := by exact prefixLift 2476458
  have htrace : WordTrace (prefixWord ++ tailWord_2476458) baseStart_2476458 baseEnd_2476458 := by
    simpa [prefixWord, tailWord_2476458, baseEnd_2476458] using wordTrace_append hprefix tailTrace_2476458
  have hstable : (prefixWord ++ tailWord_2476458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476458).length < 2 ^ (prefixWord ++ tailWord_2476458).sum := by decide
  have hdescent : baseEnd_2476458 < baseStart_2476458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476464 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2476464 : Nat := 118140960795 + 2476464 * 2 ^ 59
def prefixEnd_2476464 : Nat := 4983230072969 + 3 ^ 40 * 2476464 * 2
def baseEnd_2476464 : Nat := 1271616355556104056910955

theorem tailTrace_2476464 : CollatzResearch.WordTrace tailWord_2476464 prefixEnd_2476464 1271616355556104056910955 := by
  unfold tailWord_2476464
  simp only [CollatzResearch.WordTrace]
  refine ⟨45162031250100674611914223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60216041666800899482552297 45162031250100674611914223)
  ·
    refine ⟨67743046875151011917871335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45162031250100674611914223 67743046875151011917871335)
    ·
      refine ⟨101614570312726517876807003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67743046875151011917871335 101614570312726517876807003)
      ·
        refine ⟨152421855469089776815210505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101614570312726517876807003 152421855469089776815210505)
        ·
          refine ⟨114316391601817332611407879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152421855469089776815210505 114316391601817332611407879)
          ·
            refine ⟨171474587402725998917111819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114316391601817332611407879 171474587402725998917111819)
            ·
              refine ⟨257211881104088998375667729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171474587402725998917111819 257211881104088998375667729)
              ·
                refine ⟨192908910828066748781750797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257211881104088998375667729 192908910828066748781750797)
                ·
                  refine ⟨72340841560525030793156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192908910828066748781750797 72340841560525030793156549)
                  ·
                    refine ⟨13563907792598443273716853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72340841560525030793156549 13563907792598443273716853)
                    ·
                      refine ⟨1271616355556104056910955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13563907792598443273716853 1271616355556104056910955)
                      ·
                        rfl

theorem cell23_2476464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2476464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476464 prefixEnd_2476464 := by exact prefixLift 2476464
  have htrace : WordTrace (prefixWord ++ tailWord_2476464) baseStart_2476464 baseEnd_2476464 := by
    simpa [prefixWord, tailWord_2476464, baseEnd_2476464] using wordTrace_append hprefix tailTrace_2476464
  have hstable : (prefixWord ++ tailWord_2476464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476464).length < 2 ^ (prefixWord ++ tailWord_2476464).sum := by decide
  have hdescent : baseEnd_2476464 < baseStart_2476464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476469 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_2476469 : Nat := 118140960795 + 2476469 * 2 ^ 59
def prefixEnd_2476469 : Nat := 4983230072969 + 3 ^ 40 * 2476469 * 2
def baseEnd_2476469 : Nat := 1271618922959376537348433

theorem tailTrace_2476469 : CollatzResearch.WordTrace tailWord_2476469 prefixEnd_2476469 1271618922959376537348433 := by
  unfold tailWord_2476469
  simp only [CollatzResearch.WordTrace]
  refine ⟨90324244865183235077760461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60216163243455490051840307 90324244865183235077760461)
  ·
    refine ⟨33871591824443713154160173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90324244865183235077760461 33871591824443713154160173)
    ·
      refine ⟨12701846934166392432810065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33871591824443713154160173 12701846934166392432810065)
      ·
        refine ⟨9526385200624794324607549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12701846934166392432810065 9526385200624794324607549)
        ·
          refine ⟨3572394450234297871727831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9526385200624794324607549 3572394450234297871727831)
          ·
            refine ⟨5358591675351446807591747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572394450234297871727831 5358591675351446807591747)
            ·
              refine ⟨8037887513027170211387621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358591675351446807591747 8037887513027170211387621)
              ·
                refine ⟨1507103908692594414635179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8037887513027170211387621 1507103908692594414635179)
                ·
                  refine ⟨2260655863038891621952769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507103908692594414635179 2260655863038891621952769)
                  ·
                    refine ⟨1695491897279168716464577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260655863038891621952769 1695491897279168716464577)
                    ·
                      refine ⟨1271618922959376537348433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695491897279168716464577 1271618922959376537348433)
                      ·
                        rfl

theorem cell23_2476469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_2476469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476469 prefixEnd_2476469 := by exact prefixLift 2476469
  have htrace : WordTrace (prefixWord ++ tailWord_2476469) baseStart_2476469 baseEnd_2476469 := by
    simpa [prefixWord, tailWord_2476469, baseEnd_2476469] using wordTrace_append hprefix tailTrace_2476469
  have hstable : (prefixWord ++ tailWord_2476469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476469).length < 2 ^ (prefixWord ++ tailWord_2476469).sum := by decide
  have hdescent : baseEnd_2476469 < baseStart_2476469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476531 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 7]
def baseStart_2476531 : Nat := 118140960795 + 2476531 * 2 ^ 59
def prefixEnd_2476531 : Nat := 4983230072969 + 3 ^ 40 * 2476531 * 2
def baseEnd_2476531 : Nat := 141294528751106143863683

theorem tailTrace_2476531 : CollatzResearch.WordTrace tailWord_2476531 prefixEnd_2476531 141294528751106143863683 := by
  unfold tailWord_2476531
  simp only [CollatzResearch.WordTrace]
  refine ⟨90326506190958619666517447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60217670793972413111011631 90326506190958619666517447)
  ·
    refine ⟨135489759286437929499776171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90326506190958619666517447 135489759286437929499776171)
    ·
      refine ⟨203234638929656894249664257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135489759286437929499776171 203234638929656894249664257)
      ·
        refine ⟨152425979197242670687248193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203234638929656894249664257 152425979197242670687248193)
        ·
          refine ⟨114319484397932003015436145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152425979197242670687248193 114319484397932003015436145)
          ·
            refine ⟨85739613298449002261577109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114319484397932003015436145 85739613298449002261577109)
            ·
              refine ⟨4019044373364796981011427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85739613298449002261577109 4019044373364796981011427)
              ·
                refine ⟨6028566560047195471517141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019044373364796981011427 6028566560047195471517141)
                ·
                  refine ⟨141294528751106143863683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6028566560047195471517141 141294528751106143863683)
                  ·
                    rfl

theorem cell23_2476531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 7].length) (baseStart_2476531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476531 prefixEnd_2476531 := by exact prefixLift 2476531
  have htrace : WordTrace (prefixWord ++ tailWord_2476531) baseStart_2476531 baseEnd_2476531 := by
    simpa [prefixWord, tailWord_2476531, baseEnd_2476531] using wordTrace_append hprefix tailTrace_2476531
  have hstable : (prefixWord ++ tailWord_2476531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476531).length < 2 ^ (prefixWord ++ tailWord_2476531).sum := by decide
  have hdescent : baseEnd_2476531 < baseStart_2476531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476548 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 7]
def baseStart_2476548 : Nat := 118140960795 + 2476548 * 2 ^ 59
def prefixEnd_2476548 : Nat := 4983230072969 + 3 ^ 40 * 2476548 * 2
def baseEnd_2476548 : Nat := 141295498659009080917841

theorem tailTrace_2476548 : CollatzResearch.WordTrace tailWord_2476548 prefixEnd_2476548 141295498659009080917841 := by
  unfold tailWord_2476548
  simp only [CollatzResearch.WordTrace]
  refine ⟨45163563115948515784943149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60218084154598021046590865 45163563115948515784943149)
  ·
    refine ⟨16936336168480693419353681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45163563115948515784943149 16936336168480693419353681)
    ·
      refine ⟨12702252126360520064515261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16936336168480693419353681 12702252126360520064515261)
      ·
        refine ⟨4763344547385195024193223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12702252126360520064515261 4763344547385195024193223)
        ·
          refine ⟨7145016821077792536289835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763344547385195024193223 7145016821077792536289835)
          ·
            refine ⟨10717525231616688804434753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145016821077792536289835 10717525231616688804434753)
            ·
              refine ⟨8038143923712516603326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10717525231616688804434753 8038143923712516603326065)
              ·
                refine ⟨6028607942784387452494549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8038143923712516603326065 6028607942784387452494549)
                ·
                  refine ⟨141295498659009080917841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6028607942784387452494549 141295498659009080917841)
                  ·
                    rfl

theorem cell23_2476548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_2476548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476548 prefixEnd_2476548 := by exact prefixLift 2476548
  have htrace : WordTrace (prefixWord ++ tailWord_2476548) baseStart_2476548 baseEnd_2476548 := by
    simpa [prefixWord, tailWord_2476548, baseEnd_2476548] using wordTrace_append hprefix tailTrace_2476548
  have hstable : (prefixWord ++ tailWord_2476548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476548).length < 2 ^ (prefixWord ++ tailWord_2476548).sum := by decide
  have hdescent : baseEnd_2476548 < baseStart_2476548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476608 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_2476608 : Nat := 118140960795 + 2476608 * 2 ^ 59
def prefixEnd_2476608 : Nat := 4983230072969 + 3 ^ 40 * 2476608 * 2
def baseEnd_2476608 : Nat := 423896765590117164503431

theorem tailTrace_2476608 : CollatzResearch.WordTrace tailWord_2476608 prefixEnd_2476608 423896765590117164503431 := by
  unfold tailWord_2476608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45164657305839830908535239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60219543074453107878046985 45164657305839830908535239)
  ·
    refine ⟨67746985958759746362802859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45164657305839830908535239 67746985958759746362802859)
    ·
      refine ⟨101620478938139619544204289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67746985958759746362802859 101620478938139619544204289)
      ·
        refine ⟨76215359203604714658153217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101620478938139619544204289 76215359203604714658153217)
        ·
          refine ⟨57161519402703535993614913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76215359203604714658153217 57161519402703535993614913)
          ·
            refine ⟨42871139552027651995211185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57161519402703535993614913 42871139552027651995211185)
            ·
              refine ⟨32153354664020738996408389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42871139552027651995211185 32153354664020738996408389)
              ·
                refine ⟨6028753999503888561826573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32153354664020738996408389 6028753999503888561826573)
                ·
                  refine ⟨2260782749813958210684965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6028753999503888561826573 2260782749813958210684965)
                  ·
                    refine ⟨423896765590117164503431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260782749813958210684965 423896765590117164503431)
                    ·
                      rfl

theorem cell23_2476608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_2476608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476608 prefixEnd_2476608 := by exact prefixLift 2476608
  have htrace : WordTrace (prefixWord ++ tailWord_2476608) baseStart_2476608 baseEnd_2476608 := by
    simpa [prefixWord, tailWord_2476608, baseEnd_2476608] using wordTrace_append hprefix tailTrace_2476608
  have hstable : (prefixWord ++ tailWord_2476608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476608).length < 2 ^ (prefixWord ++ tailWord_2476608).sum := by decide
  have hdescent : baseEnd_2476608 < baseStart_2476608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476611 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_2476611 : Nat := 118140960795 + 2476611 * 2 ^ 59
def prefixEnd_2476611 : Nat := 4983230072969 + 3 ^ 40 * 2476611 * 2
def baseEnd_2476611 : Nat := 1271691837212314981772779

theorem tailTrace_2476611 : CollatzResearch.WordTrace tailWord_2476611 prefixEnd_2476611 1271691837212314981772779 := by
  unfold tailWord_2476611
  simp only [CollatzResearch.WordTrace]
  refine ⟨90329424030668793329429687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60219616020445862219619791 90329424030668793329429687)
  ·
    refine ⟨135494136046003189994144531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90329424030668793329429687 135494136046003189994144531)
    ·
      refine ⟨203241204069004784991216797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135494136046003189994144531 203241204069004784991216797)
      ·
        refine ⟨76215451525876794371706299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203241204069004784991216797 76215451525876794371706299)
        ·
          refine ⟨114323177288815191557559449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76215451525876794371706299 114323177288815191557559449)
          ·
            refine ⟨85742382966611393668169587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114323177288815191557559449 85742382966611393668169587)
            ·
              refine ⟨128613574449917090502254381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85742382966611393668169587 128613574449917090502254381)
              ·
                refine ⟨48230090418718908938345393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128613574449917090502254381 48230090418718908938345393)
                ·
                  refine ⟨36172567814039181703759045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48230090418718908938345393 36172567814039181703759045)
                  ·
                    refine ⟨6782356465132346569454821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36172567814039181703759045 6782356465132346569454821)
                    ·
                      refine ⟨1271691837212314981772779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6782356465132346569454821 1271691837212314981772779)
                      ·
                        rfl

theorem cell23_2476611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_2476611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476611 prefixEnd_2476611 := by exact prefixLift 2476611
  have htrace : WordTrace (prefixWord ++ tailWord_2476611) baseStart_2476611 baseEnd_2476611 := by
    simpa [prefixWord, tailWord_2476611, baseEnd_2476611] using wordTrace_append hprefix tailTrace_2476611
  have hstable : (prefixWord ++ tailWord_2476611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476611).length < 2 ^ (prefixWord ++ tailWord_2476611).sum := by decide
  have hdescent : baseEnd_2476611 < baseStart_2476611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476615 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2476615 : Nat := 118140960795 + 2476615 * 2 ^ 59
def prefixEnd_2476615 : Nat := 4983230072969 + 3 ^ 40 * 2476615 * 2
def baseEnd_2476615 : Nat := 1271693891134932966122761

theorem tailTrace_2476615 : CollatzResearch.WordTrace tailWord_2476615 prefixEnd_2476615 1271693891134932966122761 := by
  unfold tailWord_2476615
  simp only [CollatzResearch.WordTrace]
  refine ⟨90329569922654302012575299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60219713281769534675050199 90329569922654302012575299)
  ·
    refine ⟨135494354883981453018862949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90329569922654302012575299 135494354883981453018862949)
    ·
      refine ⟨25405191540746522441036803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135494354883981453018862949 25405191540746522441036803)
      ·
        refine ⟨38107787311119783661555205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405191540746522441036803 38107787311119783661555205)
        ·
          refine ⟨7145210120834959436541601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38107787311119783661555205 7145210120834959436541601)
          ·
            refine ⟨5358907590626219577406201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7145210120834959436541601 5358907590626219577406201)
            ·
              refine ⟨4019180692969664683054651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5358907590626219577406201 4019180692969664683054651)
              ·
                refine ⟨6028771039454497024581977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019180692969664683054651 6028771039454497024581977)
                ·
                  refine ⟨4521578279590872768436483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028771039454497024581977 4521578279590872768436483)
                  ·
                    refine ⟨6782367419386309152654725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521578279590872768436483 6782367419386309152654725)
                    ·
                      refine ⟨1271693891134932966122761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6782367419386309152654725 1271693891134932966122761)
                      ·
                        rfl

theorem cell23_2476615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2476615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476615 prefixEnd_2476615 := by exact prefixLift 2476615
  have htrace : WordTrace (prefixWord ++ tailWord_2476615) baseStart_2476615 baseEnd_2476615 := by
    simpa [prefixWord, tailWord_2476615, baseEnd_2476615] using wordTrace_append hprefix tailTrace_2476615
  have hstable : (prefixWord ++ tailWord_2476615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476615).length < 2 ^ (prefixWord ++ tailWord_2476615).sum := by decide
  have hdescent : baseEnd_2476615 < baseStart_2476615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476665 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2476665 : Nat := 118140960795 + 2476665 * 2 ^ 59
def prefixEnd_2476665 : Nat := 4983230072969 + 3 ^ 40 * 2476665 * 2
def baseEnd_2476665 : Nat := 1271719565167657770497531

theorem tailTrace_2476665 : CollatzResearch.WordTrace tailWord_2476665 prefixEnd_2476665 1271719565167657770497531 := by
  unfold tailWord_2476665
  simp only [CollatzResearch.WordTrace]
  refine ⟨90331393572473160551895449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60220929048315440367930299 90331393572473160551895449)
  ·
    refine ⟨67748545179354870413921587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90331393572473160551895449 67748545179354870413921587)
    ·
      refine ⟨101622817769032305620882381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67748545179354870413921587 101622817769032305620882381)
      ·
        refine ⟨38108556663387114607830893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101622817769032305620882381 38108556663387114607830893)
        ·
          refine ⟨14290708748770167977936585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38108556663387114607830893 14290708748770167977936585)
          ·
            refine ⟨10718031561577625983452439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14290708748770167977936585 10718031561577625983452439)
            ·
              refine ⟨16077047342366438975178659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10718031561577625983452439 16077047342366438975178659)
              ·
                refine ⟨24115571013549658462767989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16077047342366438975178659 24115571013549658462767989)
                ·
                  refine ⟨2260834782520280480884499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24115571013549658462767989 2260834782520280480884499)
                  ·
                    refine ⟨3391252173780420721326749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2260834782520280480884499 3391252173780420721326749)
                    ·
                      refine ⟨1271719565167657770497531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391252173780420721326749 1271719565167657770497531)
                      ·
                        rfl

theorem cell23_2476665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2476665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476665 prefixEnd_2476665 := by exact prefixLift 2476665
  have htrace : WordTrace (prefixWord ++ tailWord_2476665) baseStart_2476665 baseEnd_2476665 := by
    simpa [prefixWord, tailWord_2476665, baseEnd_2476665] using wordTrace_append hprefix tailTrace_2476665
  have hstable : (prefixWord ++ tailWord_2476665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476665).length < 2 ^ (prefixWord ++ tailWord_2476665).sum := by decide
  have hdescent : baseEnd_2476665 < baseStart_2476665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476668 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2476668 : Nat := 118140960795 + 2476668 * 2 ^ 59
def prefixEnd_2476668 : Nat := 4983230072969 + 3 ^ 40 * 2476668 * 2
def baseEnd_2476668 : Nat := 423907035203207086253339

theorem tailTrace_2476668 : CollatzResearch.WordTrace tailWord_2476668 prefixEnd_2476668 423907035203207086253339 := by
  unfold tailWord_2476668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45165751495731146032127329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60221001994308194709503105 45165751495731146032127329)
  ·
    refine ⟨33874313621798359524095497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45165751495731146032127329 33874313621798359524095497)
    ·
      refine ⟨25405735216348769643071623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33874313621798359524095497 25405735216348769643071623)
      ·
        refine ⟨38108602824523154464607435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405735216348769643071623 38108602824523154464607435)
        ·
          refine ⟨57162904236784731696911153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38108602824523154464607435 57162904236784731696911153)
          ·
            refine ⟨42872178177588548772683365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57162904236784731696911153 42872178177588548772683365)
            ·
              refine ⟨8038533408297852894878131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42872178177588548772683365 8038533408297852894878131)
              ·
                refine ⟨12057800112446779342317197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038533408297852894878131 12057800112446779342317197)
                ·
                  refine ⟨4521675042167542253368949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12057800112446779342317197 4521675042167542253368949)
                  ·
                    refine ⟨423907035203207086253339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4521675042167542253368949 423907035203207086253339)
                    ·
                      rfl

theorem cell23_2476668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2476668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476668 prefixEnd_2476668 := by exact prefixLift 2476668
  have htrace : WordTrace (prefixWord ++ tailWord_2476668) baseStart_2476668 baseEnd_2476668 := by
    simpa [prefixWord, tailWord_2476668, baseEnd_2476668] using wordTrace_append hprefix tailTrace_2476668
  have hstable : (prefixWord ++ tailWord_2476668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476668).length < 2 ^ (prefixWord ++ tailWord_2476668).sum := by decide
  have hdescent : baseEnd_2476668 < baseStart_2476668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476669 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_2476669 : Nat := 118140960795 + 2476669 * 2 ^ 59
def prefixEnd_2476669 : Nat := 4983230072969 + 3 ^ 40 * 2476669 * 2
def baseEnd_2476669 : Nat := 1271721619090275754847513

theorem tailTrace_2476669 : CollatzResearch.WordTrace tailWord_2476669 prefixEnd_2476669 1271721619090275754847513 := by
  unfold tailWord_2476669
  simp only [CollatzResearch.WordTrace]
  refine ⟨90331539464458669235041061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60221026309639112823360707 90331539464458669235041061)
  ·
    refine ⟨16937163649586000481570199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90331539464458669235041061 16937163649586000481570199)
    ·
      refine ⟨25405745474379000722355299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16937163649586000481570199 25405745474379000722355299)
      ·
        refine ⟨38108618211568501083532949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405745474379000722355299 38108618211568501083532949)
        ·
          refine ⟨1786341478667273488290607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38108618211568501083532949 1786341478667273488290607)
          ·
            refine ⟨2679512218000910232435911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786341478667273488290607 2679512218000910232435911)
            ·
              refine ⟨4019268327001365348653867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679512218000910232435911 4019268327001365348653867)
              ·
                refine ⟨6028902490502048022980801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019268327001365348653867 6028902490502048022980801)
                ·
                  refine ⟨4521676867876536017235601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028902490502048022980801 4521676867876536017235601)
                  ·
                    refine ⟨3391257650907402012926701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521676867876536017235601 3391257650907402012926701)
                    ·
                      refine ⟨1271721619090275754847513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391257650907402012926701 1271721619090275754847513)
                      ·
                        rfl

theorem cell23_2476669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_2476669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476669 prefixEnd_2476669 := by exact prefixLift 2476669
  have htrace : WordTrace (prefixWord ++ tailWord_2476669) baseStart_2476669 baseEnd_2476669 := by
    simpa [prefixWord, tailWord_2476669, baseEnd_2476669] using wordTrace_append hprefix tailTrace_2476669
  have hstable : (prefixWord ++ tailWord_2476669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476669).length < 2 ^ (prefixWord ++ tailWord_2476669).sum := by decide
  have hdescent : baseEnd_2476669 < baseStart_2476669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476776 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2476776 : Nat := 118140960795 + 2476776 * 2 ^ 59
def prefixEnd_2476776 : Nat := 4983230072969 + 3 ^ 40 * 2476776 * 2
def baseEnd_2476776 : Nat := 1271776561520306836209521

theorem tailTrace_2476776 : CollatzResearch.WordTrace tailWord_2476776 prefixEnd_2476776 1271776561520306836209521 := by
  unfold tailWord_2476776
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167721037535513254593091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60223628050047351006124121 45167721037535513254593091)
  ·
    refine ⟨67751581556303269881889637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45167721037535513254593091 67751581556303269881889637)
    ·
      refine ⟨12703421541806863102854307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67751581556303269881889637 12703421541806863102854307)
      ·
        refine ⟨19055132312710294654281461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12703421541806863102854307 19055132312710294654281461)
        ·
          refine ⟨1786418654316590123838887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19055132312710294654281461 1786418654316590123838887)
          ·
            refine ⟨2679627981474885185758331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786418654316590123838887 2679627981474885185758331)
            ·
              refine ⟨4019441972212327778637497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679627981474885185758331 4019441972212327778637497)
              ·
                refine ⟨3014581479159245833978123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019441972212327778637497 3014581479159245833978123)
                ·
                  refine ⟨4521872218738868750967185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014581479159245833978123 4521872218738868750967185)
                  ·
                    refine ⟨3391404164054151563225389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521872218738868750967185 3391404164054151563225389)
                    ·
                      refine ⟨1271776561520306836209521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391404164054151563225389 1271776561520306836209521)
                      ·
                        rfl

theorem cell23_2476776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2476776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476776 prefixEnd_2476776 := by exact prefixLift 2476776
  have htrace : WordTrace (prefixWord ++ tailWord_2476776) baseStart_2476776 baseEnd_2476776 := by
    simpa [prefixWord, tailWord_2476776, baseEnd_2476776] using wordTrace_append hprefix tailTrace_2476776
  have hstable : (prefixWord ++ tailWord_2476776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476776).length < 2 ^ (prefixWord ++ tailWord_2476776).sum := by decide
  have hdescent : baseEnd_2476776 < baseStart_2476776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476778 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2476778 : Nat := 118140960795 + 2476778 * 2 ^ 59
def prefixEnd_2476778 : Nat := 4983230072969 + 3 ^ 40 * 2476778 * 2
def baseEnd_2476778 : Nat := 1271777588481615828384511

theorem tailTrace_2476778 : CollatzResearch.WordTrace tailWord_2476778 prefixEnd_2476778 1271777588481615828384511 := by
  unfold tailWord_2476778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22583878755265945212689747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60223676680709187233839325 22583878755265945212689747)
  ·
    refine ⟨33875818132898917819034621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22583878755265945212689747 33875818132898917819034621)
    ·
      refine ⟨12703431799837094182137983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33875818132898917819034621 12703431799837094182137983)
      ·
        refine ⟨19055147699755641273206975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12703431799837094182137983 19055147699755641273206975)
        ·
          refine ⟨28582721549633461909810463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19055147699755641273206975 28582721549633461909810463)
          ·
            refine ⟨42874082324450192864715695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28582721549633461909810463 42874082324450192864715695)
            ·
              refine ⟨64311123486675289297073543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42874082324450192864715695 64311123486675289297073543)
              ·
                refine ⟨96466685230012933945610315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64311123486675289297073543 96466685230012933945610315)
                ·
                  refine ⟨144700027845019400918415473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96466685230012933945610315 144700027845019400918415473)
                  ·
                    refine ⟨108525020883764550688811605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144700027845019400918415473 108525020883764550688811605)
                    ·
                      refine ⟨1271777588481615828384511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 108525020883764550688811605 1271777588481615828384511)
                      ·
                        rfl

theorem cell23_2476778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2476778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476778 prefixEnd_2476778 := by exact prefixLift 2476778
  have htrace : WordTrace (prefixWord ++ tailWord_2476778) baseStart_2476778 baseEnd_2476778 := by
    simpa [prefixWord, tailWord_2476778, baseEnd_2476778] using wordTrace_append hprefix tailTrace_2476778
  have hstable : (prefixWord ++ tailWord_2476778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476778).length < 2 ^ (prefixWord ++ tailWord_2476778).sum := by decide
  have hdescent : baseEnd_2476778 < baseStart_2476778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476885 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2476885 : Nat := 118140960795 + 2476885 * 2 ^ 59
def prefixEnd_2476885 : Nat := 4983230072969 + 3 ^ 40 * 2476885 * 2
def baseEnd_2476885 : Nat := 1271832530911646909746519

theorem tailTrace_2476885 : CollatzResearch.WordTrace tailWord_2476885 prefixEnd_2476885 1271832530911646909746519 := by
  unfold tailWord_2476885
  simp only [CollatzResearch.WordTrace]
  refine ⟨90339417631676138124904109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60226278421117425416602739 90339417631676138124904109)
  ·
    refine ⟨33877281611878551796839041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90339417631676138124904109 33877281611878551796839041)
    ·
      refine ⟨25407961208908913847629281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33877281611878551796839041 25407961208908913847629281)
      ·
        refine ⟨19055970906681685385721961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25407961208908913847629281 19055970906681685385721961)
        ·
          refine ⟨14291978180011264039291471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19055970906681685385721961 14291978180011264039291471)
          ·
            refine ⟨21437967270016896058937207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14291978180011264039291471 21437967270016896058937207)
            ·
              refine ⟨32156950905025344088405811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21437967270016896058937207 32156950905025344088405811)
              ·
                refine ⟨48235426357538016132608717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32156950905025344088405811 48235426357538016132608717)
                ·
                  refine ⟨18088284884076756049728269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48235426357538016132608717 18088284884076756049728269)
                  ·
                    refine ⟨6783106831528783518648101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18088284884076756049728269 6783106831528783518648101)
                    ·
                      refine ⟨1271832530911646909746519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6783106831528783518648101 1271832530911646909746519)
                      ·
                        rfl

theorem cell23_2476885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2476885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476885 prefixEnd_2476885 := by exact prefixLift 2476885
  have htrace : WordTrace (prefixWord ++ tailWord_2476885) baseStart_2476885 baseEnd_2476885 := by
    simpa [prefixWord, tailWord_2476885, baseEnd_2476885] using wordTrace_append hprefix tailTrace_2476885
  have hstable : (prefixWord ++ tailWord_2476885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476885).length < 2 ^ (prefixWord ++ tailWord_2476885).sum := by decide
  have hdescent : baseEnd_2476885 < baseStart_2476885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476925 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 8]
def baseStart_2476925 : Nat := 118140960795 + 2476925 * 2 ^ 59
def prefixEnd_2476925 : Nat := 4983230072969 + 3 ^ 40 * 2476925 * 2
def baseEnd_2476925 : Nat := 141317007793091861471815

theorem tailTrace_2476925 : CollatzResearch.WordTrace tailWord_2476925 prefixEnd_2476925 141317007793091861471815 := by
  unfold tailWord_2476925
  simp only [CollatzResearch.WordTrace]
  refine ⟨90340876551531224956360229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60227251034354149970906819 90340876551531224956360229)
  ·
    refine ⟨16938914353412104679317543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90340876551531224956360229 16938914353412104679317543)
    ·
      refine ⟨25408371530118157018976315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16938914353412104679317543 25408371530118157018976315)
      ·
        refine ⟨38112557295177235528464473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25408371530118157018976315 38112557295177235528464473)
        ·
          refine ⟨28584417971382926646348355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38112557295177235528464473 28584417971382926646348355)
          ·
            refine ⟨42876626957074389969522533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28584417971382926646348355 42876626957074389969522533)
            ·
              refine ⟨8039367554451448119285475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42876626957074389969522533 8039367554451448119285475)
              ·
                refine ⟨12059051331677172178928213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8039367554451448119285475 12059051331677172178928213)
                ·
                  refine ⟨141317007793091861471815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12059051331677172178928213 141317007793091861471815)
                  ·
                    rfl

theorem cell23_2476925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_2476925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476925 prefixEnd_2476925 := by exact prefixLift 2476925
  have htrace : WordTrace (prefixWord ++ tailWord_2476925) baseStart_2476925 baseEnd_2476925 := by
    simpa [prefixWord, tailWord_2476925, baseEnd_2476925] using wordTrace_append hprefix tailTrace_2476925
  have hstable : (prefixWord ++ tailWord_2476925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476925).length < 2 ^ (prefixWord ++ tailWord_2476925).sum := by decide
  have hdescent : baseEnd_2476925 < baseStart_2476925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476956 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2476956 : Nat := 118140960795 + 2476956 * 2 ^ 59
def prefixEnd_2476956 : Nat := 4983230072969 + 3 ^ 40 * 2476956 * 2
def baseEnd_2476956 : Nat := 1271868988038116131958693

theorem tailTrace_2476956 : CollatzResearch.WordTrace tailWord_2476956 prefixEnd_2476956 1271868988038116131958693 := by
  unfold tailWord_2476956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45171003607209458625369361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60228004809612611500492481 45171003607209458625369361)
  ·
    refine ⟨33878252705407093969027021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45171003607209458625369361 33878252705407093969027021)
    ·
      refine ⟨12704344764527660238385133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33878252705407093969027021 12704344764527660238385133)
      ·
        refine ⟨4764129286697872589394425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12704344764527660238385133 4764129286697872589394425)
        ·
          refine ⟨3573096965023404442045819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764129286697872589394425 3573096965023404442045819)
          ·
            refine ⟨5359645447535106663068729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573096965023404442045819 5359645447535106663068729)
            ·
              refine ⟨4019734085651329997301547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359645447535106663068729 4019734085651329997301547)
              ·
                refine ⟨6029601128476994995952321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019734085651329997301547 6029601128476994995952321)
                ·
                  refine ⟨4522200846357746246964241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029601128476994995952321 4522200846357746246964241)
                  ·
                    refine ⟨3391650634768309685223181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522200846357746246964241 3391650634768309685223181)
                    ·
                      refine ⟨1271868988038116131958693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391650634768309685223181 1271868988038116131958693)
                      ·
                        rfl

theorem cell23_2476956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2476956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476956 prefixEnd_2476956 := by exact prefixLift 2476956
  have htrace : WordTrace (prefixWord ++ tailWord_2476956) baseStart_2476956 baseEnd_2476956 := by
    simpa [prefixWord, tailWord_2476956, baseEnd_2476956] using wordTrace_append hprefix tailTrace_2476956
  have hstable : (prefixWord ++ tailWord_2476956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476956).length < 2 ^ (prefixWord ++ tailWord_2476956).sum := by decide
  have hdescent : baseEnd_2476956 < baseStart_2476956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476980 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2476980 : Nat := 118140960795 + 2476980 * 2 ^ 59
def prefixEnd_2476980 : Nat := 4983230072969 + 3 ^ 40 * 2476980 * 2
def baseEnd_2476980 : Nat := 423960437191274679352861

theorem tailTrace_2476980 : CollatzResearch.WordTrace tailWord_2476980 prefixEnd_2476980 423960437191274679352861 := by
  unfold tailWord_2476980
  simp only [CollatzResearch.WordTrace]
  refine ⟨45171441283165984674806197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60228588377554646233074929 45171441283165984674806197)
  ·
    refine ⟨4234822620296811063263081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45171441283165984674806197 4234822620296811063263081)
    ·
      refine ⟨3176116965222608297447311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4234822620296811063263081 3176116965222608297447311)
      ·
        refine ⟨4764175447833912446170967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176116965222608297447311 4764175447833912446170967)
        ·
          refine ⟨7146263171750868669256451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764175447833912446170967 7146263171750868669256451)
          ·
            refine ⟨10719394757626303003884677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146263171750868669256451 10719394757626303003884677)
            ·
              refine ⟨2009886517054931813228377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10719394757626303003884677 2009886517054931813228377)
              ·
                refine ⟨1507414887791198859921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009886517054931813228377 1507414887791198859921283)
                ·
                  refine ⟨2261122331686798289881925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507414887791198859921283 2261122331686798289881925)
                  ·
                    refine ⟨423960437191274679352861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261122331686798289881925 423960437191274679352861)
                    ·
                      rfl

theorem cell23_2476980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2476980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476980 prefixEnd_2476980 := by exact prefixLift 2476980
  have htrace : WordTrace (prefixWord ++ tailWord_2476980) baseStart_2476980 baseEnd_2476980 := by
    simpa [prefixWord, tailWord_2476980, baseEnd_2476980] using wordTrace_append hprefix tailTrace_2476980
  have hstable : (prefixWord ++ tailWord_2476980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476980).length < 2 ^ (prefixWord ++ tailWord_2476980).sum := by decide
  have hdescent : baseEnd_2476980 < baseStart_2476980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476986 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_2476986 : Nat := 118140960795 + 2476986 * 2 ^ 59
def prefixEnd_2476986 : Nat := 4983230072969 + 3 ^ 40 * 2476986 * 2
def baseEnd_2476986 : Nat := 1271884392457751014583555

theorem tailTrace_2476986 : CollatzResearch.WordTrace tailWord_2476986 prefixEnd_2476986 1271884392457751014583555 := by
  unfold tailWord_2476986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22585775351077558093582703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60228734269540154916220541 22585775351077558093582703)
  ·
    refine ⟨33878663026616337140374055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22585775351077558093582703 33878663026616337140374055)
    ·
      refine ⟨50817994539924505710561083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33878663026616337140374055 50817994539924505710561083)
      ·
        refine ⟨76226991809886758565841625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50817994539924505710561083 76226991809886758565841625)
        ·
          refine ⟨57170243857415068924381219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76226991809886758565841625 57170243857415068924381219)
          ·
            refine ⟨85755365786122603386571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57170243857415068924381219 85755365786122603386571829)
            ·
              refine ⟨8039565542448994067491109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85755365786122603386571829 8039565542448994067491109)
              ·
                refine ⟨1507418539209186387654583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8039565542448994067491109 1507418539209186387654583)
                ·
                  refine ⟨2261127808813779581481875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507418539209186387654583 2261127808813779581481875)
                  ·
                    refine ⟨3391691713220669372222813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261127808813779581481875 3391691713220669372222813)
                    ·
                      refine ⟨1271884392457751014583555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391691713220669372222813 1271884392457751014583555)
                      ·
                        rfl

theorem cell23_2476986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_2476986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476986 prefixEnd_2476986 := by exact prefixLift 2476986
  have htrace : WordTrace (prefixWord ++ tailWord_2476986) baseStart_2476986 baseEnd_2476986 := by
    simpa [prefixWord, tailWord_2476986, baseEnd_2476986] using wordTrace_append hprefix tailTrace_2476986
  have hstable : (prefixWord ++ tailWord_2476986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476986).length < 2 ^ (prefixWord ++ tailWord_2476986).sum := by decide
  have hdescent : baseEnd_2476986 < baseStart_2476986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476992 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_2476992 : Nat := 118140960795 + 2476992 * 2 ^ 59
def prefixEnd_2476992 : Nat := 4983230072969 + 3 ^ 40 * 2476992 * 2
def baseEnd_2476992 : Nat := 1271887473341677991108527

theorem tailTrace_2476992 : CollatzResearch.WordTrace tailWord_2476992 prefixEnd_2476992 1271887473341677991108527 := by
  unfold tailWord_2476992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45171660121144247699524615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60228880161525663599366153 45171660121144247699524615)
  ·
    refine ⟨67757490181716371549286923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45171660121144247699524615 67757490181716371549286923)
    ·
      refine ⟨101636235272574557323930385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67757490181716371549286923 101636235272574557323930385)
      ·
        refine ⟨76227176454430917992947789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101636235272574557323930385 76227176454430917992947789)
        ·
          refine ⟨28585191170411594247355421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76227176454430917992947789 28585191170411594247355421)
          ·
            refine ⟨10719446688904347842758283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28585191170411594247355421 10719446688904347842758283)
            ·
              refine ⟨16079170033356521764137425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719446688904347842758283 16079170033356521764137425)
              ·
                refine ⟨12059377525017391323103069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16079170033356521764137425 12059377525017391323103069)
                ·
                  refine ⟨4522266571881521746163651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12059377525017391323103069 4522266571881521746163651)
                  ·
                    refine ⟨6783399857822282619245477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522266571881521746163651 6783399857822282619245477)
                    ·
                      refine ⟨1271887473341677991108527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6783399857822282619245477 1271887473341677991108527)
                      ·
                        rfl

theorem cell23_2476992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_2476992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476992 prefixEnd_2476992 := by exact prefixLift 2476992
  have htrace : WordTrace (prefixWord ++ tailWord_2476992) baseStart_2476992 baseEnd_2476992 := by
    simpa [prefixWord, tailWord_2476992, baseEnd_2476992] using wordTrace_append hprefix tailTrace_2476992
  have hstable : (prefixWord ++ tailWord_2476992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476992).length < 2 ^ (prefixWord ++ tailWord_2476992).sum := by decide
  have hdescent : baseEnd_2476992 < baseStart_2476992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477002 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_2477002 : Nat := 118140960795 + 2477002 * 2 ^ 59
def prefixEnd_2477002 : Nat := 4983230072969 + 3 ^ 40 * 2477002 * 2
def baseEnd_2477002 : Nat := 423964202716074317327827

theorem tailTrace_2477002 : CollatzResearch.WordTrace tailWord_2477002 prefixEnd_2477002 423964202716074317327827 := by
  unfold tailWord_2477002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22585921243063066776728315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60229123314834844737942173 22585921243063066776728315)
  ·
    refine ⟨33878881864594600165092473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22585921243063066776728315 33878881864594600165092473)
    ·
      refine ⟨25409161398445950123819355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33878881864594600165092473 25409161398445950123819355)
      ·
        refine ⟨38113742097668925185729033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25409161398445950123819355 38113742097668925185729033)
        ·
          refine ⟨28585306573251693889296775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38113742097668925185729033 28585306573251693889296775)
          ·
            refine ⟨42877959859877540833945163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28585306573251693889296775 42877959859877540833945163)
            ·
              refine ⟨64316939789816311250917745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42877959859877540833945163 64316939789816311250917745)
              ·
                refine ⟨48237704842362233438188309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64316939789816311250917745 48237704842362233438188309)
                ·
                  refine ⟨2261142414485729692415077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48237704842362233438188309 2261142414485729692415077)
                  ·
                    refine ⟨423964202716074317327827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261142414485729692415077 423964202716074317327827)
                    ·
                      rfl

theorem cell23_2477002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_2477002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477002 prefixEnd_2477002 := by exact prefixLift 2477002
  have htrace : WordTrace (prefixWord ++ tailWord_2477002) baseStart_2477002 baseEnd_2477002 := by
    simpa [prefixWord, tailWord_2477002, baseEnd_2477002] using wordTrace_append hprefix tailTrace_2477002
  have hstable : (prefixWord ++ tailWord_2477002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477002).length < 2 ^ (prefixWord ++ tailWord_2477002).sum := by decide
  have hdescent : baseEnd_2477002 < baseStart_2477002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477013 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2477013 : Nat := 118140960795 + 2477013 * 2 ^ 59
def prefixEnd_2477013 : Nat := 4983230072969 + 3 ^ 40 * 2477013 * 2
def baseEnd_2477013 : Nat := 1271898256435422408945931

theorem tailTrace_2477013 : CollatzResearch.WordTrace tailWord_2477013 prefixEnd_2477013 1271898256435422408945931 := by
  unfold tailWord_2477013
  simp only [CollatzResearch.WordTrace]
  refine ⟨90344086175212415985563693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60229390783474943990375795 90344086175212415985563693)
  ·
    refine ⟨33879032315704655994586385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90344086175212415985563693 33879032315704655994586385)
    ·
      refine ⟨25409274236778491995939789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33879032315704655994586385 25409274236778491995939789)
      ·
        refine ⟨9528477838791934498477421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25409274236778491995939789 9528477838791934498477421)
        ·
          refine ⟨3573179189546975436929033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9528477838791934498477421 3573179189546975436929033)
          ·
            refine ⟨2679884392160231577696775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573179189546975436929033 2679884392160231577696775)
            ·
              refine ⟨4019826588240347366545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679884392160231577696775 4019826588240347366545163)
              ·
                refine ⟨6029739882360521049817745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019826588240347366545163 6029739882360521049817745)
                ·
                  refine ⟨4522304911770390787363309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029739882360521049817745 4522304911770390787363309)
                  ·
                    refine ⟨1695864341913896545261241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4522304911770390787363309 1695864341913896545261241)
                    ·
                      refine ⟨1271898256435422408945931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695864341913896545261241 1271898256435422408945931)
                      ·
                        rfl

theorem cell23_2477013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2477013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477013 prefixEnd_2477013 := by exact prefixLift 2477013
  have htrace : WordTrace (prefixWord ++ tailWord_2477013) baseStart_2477013 baseEnd_2477013 := by
    simpa [prefixWord, tailWord_2477013, baseEnd_2477013] using wordTrace_append hprefix tailTrace_2477013
  have hstable : (prefixWord ++ tailWord_2477013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477013).length < 2 ^ (prefixWord ++ tailWord_2477013).sum := by decide
  have hdescent : baseEnd_2477013 < baseStart_2477013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477023 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 1, 5]
def baseStart_2477023 : Nat := 118140960795 + 2477023 * 2 ^ 59
def prefixEnd_2477023 : Nat := 4983230072969 + 3 ^ 40 * 2477023 * 2
def baseEnd_2477023 : Nat := 423967797080655789940295

theorem tailTrace_2477023 : CollatzResearch.WordTrace tailWord_2477023 prefixEnd_2477023 423967797080655789940295 := by
  unfold tailWord_2477023
  simp only [CollatzResearch.WordTrace]
  refine ⟨90344450905176187693427723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60229633936784125128951815 90344450905176187693427723)
  ·
    refine ⟨135516676357764281540141585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90344450905176187693427723 135516676357764281540141585)
    ·
      refine ⟨101637507268323211155106189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135516676357764281540141585 101637507268323211155106189)
      ·
        refine ⟨38114065225621204183164821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101637507268323211155106189 38114065225621204183164821)
        ·
          refine ⟨1786596807450993946085851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38114065225621204183164821 1786596807450993946085851)
          ·
            refine ⟨2679895211176490919128777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786596807450993946085851 2679895211176490919128777)
            ·
              refine ⟨2009921408382368189346583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679895211176490919128777 2009921408382368189346583)
              ·
                refine ⟨3014882112573552284019875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009921408382368189346583 3014882112573552284019875)
                ·
                  refine ⟨4522323168860328426029813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014882112573552284019875 4522323168860328426029813)
                  ·
                    refine ⟨423967797080655789940295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4522323168860328426029813 423967797080655789940295)
                    ·
                      rfl

theorem cell23_2477023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_2477023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477023 prefixEnd_2477023 := by exact prefixLift 2477023
  have htrace : WordTrace (prefixWord ++ tailWord_2477023) baseStart_2477023 baseEnd_2477023 := by
    simpa [prefixWord, tailWord_2477023, baseEnd_2477023] using wordTrace_append hprefix tailTrace_2477023
  have hstable : (prefixWord ++ tailWord_2477023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477023).length < 2 ^ (prefixWord ++ tailWord_2477023).sum := by decide
  have hdescent : baseEnd_2477023 < baseStart_2477023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477035 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_2477035 : Nat := 118140960795 + 2477035 * 2 ^ 59
def prefixEnd_2477035 : Nat := 4983230072969 + 3 ^ 40 * 2477035 * 2
def baseEnd_2477035 : Nat := 1271909553009821322870829

theorem tailTrace_2477035 : CollatzResearch.WordTrace tailWord_2477035 prefixEnd_2477035 1271909553009821322870829 := by
  unfold tailWord_2477035
  simp only [CollatzResearch.WordTrace]
  refine ⟨90344888581132713742864559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60229925720755142495243039 90344888581132713742864559)
  ·
    refine ⟨135517332871699070614296839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90344888581132713742864559 135517332871699070614296839)
    ·
      refine ⟨203275999307548605921445259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135517332871699070614296839 203275999307548605921445259)
      ·
        refine ⟨304913998961322908882167889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203275999307548605921445259 304913998961322908882167889)
        ·
          refine ⟨228685499220992181661625917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304913998961322908882167889 228685499220992181661625917)
          ·
            refine ⟨85757062207872068123109719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228685499220992181661625917 85757062207872068123109719)
            ·
              refine ⟨128635593311808102184664579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85757062207872068123109719 128635593311808102184664579)
              ·
                refine ⟨192953389967712153276996869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128635593311808102184664579 192953389967712153276996869)
                ·
                  refine ⟨36178760618946028739436913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192953389967712153276996869 36178760618946028739436913)
                  ·
                    refine ⟨27134070464209521554577685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36178760618946028739436913 27134070464209521554577685)
                    ·
                      refine ⟨1271909553009821322870829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27134070464209521554577685 1271909553009821322870829)
                      ·
                        rfl

theorem cell23_2477035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_2477035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477035 prefixEnd_2477035 := by exact prefixLift 2477035
  have htrace : WordTrace (prefixWord ++ tailWord_2477035) baseStart_2477035 baseEnd_2477035 := by
    simpa [prefixWord, tailWord_2477035, baseEnd_2477035] using wordTrace_append hprefix tailTrace_2477035
  have hstable : (prefixWord ++ tailWord_2477035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477035).length < 2 ^ (prefixWord ++ tailWord_2477035).sum := by decide
  have hdescent : baseEnd_2477035 < baseStart_2477035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477110 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2477110 : Nat := 118140960795 + 2477110 * 2 ^ 59
def prefixEnd_2477110 : Nat := 4983230072969 + 3 ^ 40 * 2477110 * 2
def baseEnd_2477110 : Nat := 1271948064058908529432985

theorem tailTrace_2477110 : CollatzResearch.WordTrace tailWord_2477110 prefixEnd_2477110 1271948064058908529432985 := by
  unfold tailWord_2477110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646726503491312596990299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60231749370574001034563189 5646726503491312596990299)
  ·
    refine ⟨8470089755236968895485449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646726503491312596990299 8470089755236968895485449)
    ·
      refine ⟨6352567316427726671614087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470089755236968895485449 6352567316427726671614087)
      ·
        refine ⟨9528850974641590007421131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352567316427726671614087 9528850974641590007421131)
        ·
          refine ⟨14293276461962385011131697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9528850974641590007421131 14293276461962385011131697)
          ·
            refine ⟨10719957346471788758348773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14293276461962385011131697 10719957346471788758348773)
            ·
              refine ⟨2009992002463460392190395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10719957346471788758348773 2009992002463460392190395)
              ·
                refine ⟨3014988003695190588285593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009992002463460392190395 3014988003695190588285593)
                ·
                  refine ⟨2261241002771392941214195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014988003695190588285593 2261241002771392941214195)
                  ·
                    refine ⟨3391861504157089411821293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261241002771392941214195 3391861504157089411821293)
                    ·
                      refine ⟨1271948064058908529432985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391861504157089411821293 1271948064058908529432985)
                      ·
                        rfl

theorem cell23_2477110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2477110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477110 prefixEnd_2477110 := by exact prefixLift 2477110
  have htrace : WordTrace (prefixWord ++ tailWord_2477110) baseStart_2477110 baseEnd_2477110 := by
    simpa [prefixWord, tailWord_2477110, baseEnd_2477110] using wordTrace_append hprefix tailTrace_2477110
  have hstable : (prefixWord ++ tailWord_2477110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477110).length < 2 ^ (prefixWord ++ tailWord_2477110).sum := by decide
  have hdescent : baseEnd_2477110 < baseStart_2477110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477133 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2477133 : Nat := 118140960795 + 2477133 * 2 ^ 59
def prefixEnd_2477133 : Nat := 4983230072969 + 3 ^ 40 * 2477133 * 2
def baseEnd_2477133 : Nat := 1271959874113961939445379

theorem tailTrace_2477133 : CollatzResearch.WordTrace tailWord_2477133 prefixEnd_2477133 1271959874113961939445379 := by
  unfold tailWord_2477133
  simp only [CollatzResearch.WordTrace]
  refine ⟨90348462934777676479932053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60232308623185117653288035 90348462934777676479932053)
  ·
    refine ⟨4235084200067703584996815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90348462934777676479932053 4235084200067703584996815)
    ·
      refine ⟨6352626300101555377495223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235084200067703584996815 6352626300101555377495223)
      ·
        refine ⟨9528939450152333066242835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352626300101555377495223 9528939450152333066242835)
        ·
          refine ⟨14293409175228499599364253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9528939450152333066242835 14293409175228499599364253)
          ·
            refine ⟨5360028440710687349761595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14293409175228499599364253 5360028440710687349761595)
            ·
              refine ⟨8040042661066031024642393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360028440710687349761595 8040042661066031024642393)
              ·
                refine ⟨6030031995799523268481795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8040042661066031024642393 6030031995799523268481795)
                ·
                  refine ⟨9045047993699284902722693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030031995799523268481795 9045047993699284902722693)
                  ·
                    refine ⟨1695946498818615919260505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9045047993699284902722693 1695946498818615919260505)
                    ·
                      refine ⟨1271959874113961939445379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695946498818615919260505 1271959874113961939445379)
                      ·
                        rfl

theorem cell23_2477133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2477133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477133 prefixEnd_2477133 := by exact prefixLift 2477133
  have htrace : WordTrace (prefixWord ++ tailWord_2477133) baseStart_2477133 baseEnd_2477133 := by
    simpa [prefixWord, tailWord_2477133, baseEnd_2477133] using wordTrace_append hprefix tailTrace_2477133
  have hstable : (prefixWord ++ tailWord_2477133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477133).length < 2 ^ (prefixWord ++ tailWord_2477133).sum := by decide
  have hdescent : baseEnd_2477133 < baseStart_2477133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477166 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2477166 : Nat := 118140960795 + 2477166 * 2 ^ 59
def prefixEnd_2477166 : Nat := 4983230072969 + 3 ^ 40 * 2477166 * 2
def baseEnd_2477166 : Nat := 1271976818975560310332727

theorem tailTrace_2477166 : CollatzResearch.WordTrace tailWord_2477166 prefixEnd_2477166 1271976818975560310332727 := by
  unfold tailWord_2477166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11293708317957265389485419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60233111029105415410588901 11293708317957265389485419)
  ·
    refine ⟨16940562476935898084228129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11293708317957265389485419 16940562476935898084228129)
    ·
      refine ⟨12705421857701923563171097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16940562476935898084228129 12705421857701923563171097)
      ·
        refine ⟨9529066393276442672378323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12705421857701923563171097 9529066393276442672378323)
        ·
          refine ⟨14293599589914664008567485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9529066393276442672378323 14293599589914664008567485)
          ·
            refine ⟨5360099846217999003212807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14293599589914664008567485 5360099846217999003212807)
            ·
              refine ⟨8040149769326998504819211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360099846217999003212807 8040149769326998504819211)
              ·
                refine ⟨12060224653990497757228817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040149769326998504819211 12060224653990497757228817)
                ·
                  refine ⟨9045168490492873317921613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060224653990497757228817 9045168490492873317921613)
                  ·
                    refine ⟨3391938183934827494220605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9045168490492873317921613 3391938183934827494220605)
                    ·
                      refine ⟨1271976818975560310332727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3391938183934827494220605 1271976818975560310332727)
                      ·
                        rfl

theorem cell23_2477166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2477166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477166 prefixEnd_2477166 := by exact prefixLift 2477166
  have htrace : WordTrace (prefixWord ++ tailWord_2477166) baseStart_2477166 baseEnd_2477166 := by
    simpa [prefixWord, tailWord_2477166, baseEnd_2477166] using wordTrace_append hprefix tailTrace_2477166
  have hstable : (prefixWord ++ tailWord_2477166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477166).length < 2 ^ (prefixWord ++ tailWord_2477166).sum := by decide
  have hdescent : baseEnd_2477166 < baseStart_2477166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477216 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_2477216 : Nat := 118140960795 + 2477216 * 2 ^ 59
def prefixEnd_2477216 : Nat := 4983230072969 + 3 ^ 40 * 2477216 * 2
def baseEnd_2477216 : Nat := 424000831002761704902499

theorem tailTrace_2477216 : CollatzResearch.WordTrace tailWord_2477216 prefixEnd_2477216 424000831002761704902499 := by
  unfold tailWord_2477216
  simp only [CollatzResearch.WordTrace]
  refine ⟨45175745096738490827601751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60234326795651321103469001 45175745096738490827601751)
  ·
    refine ⟨67763617645107736241402627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45175745096738490827601751 67763617645107736241402627)
    ·
      refine ⟨101645426467661604362103941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67763617645107736241402627 101645426467661604362103941)
      ·
        refine ⟨19058517462686550817894489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101645426467661604362103941 19058517462686550817894489)
        ·
          refine ⟨14293888097014913113420867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19058517462686550817894489 14293888097014913113420867)
          ·
            refine ⟨21440832145522369670131301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14293888097014913113420867 21440832145522369670131301)
            ·
              refine ⟨4020156027285444313149619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21440832145522369670131301 4020156027285444313149619)
              ·
                refine ⟨6030234040928166469724429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020156027285444313149619 6030234040928166469724429)
                ·
                  refine ⟨2261337765348062426146661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6030234040928166469724429 2261337765348062426146661)
                  ·
                    refine ⟨424000831002761704902499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261337765348062426146661 424000831002761704902499)
                    ·
                      rfl

theorem cell23_2477216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_2477216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477216 prefixEnd_2477216 := by exact prefixLift 2477216
  have htrace : WordTrace (prefixWord ++ tailWord_2477216) baseStart_2477216 baseEnd_2477216 := by
    simpa [prefixWord, tailWord_2477216, baseEnd_2477216] using wordTrace_append hprefix tailTrace_2477216
  have hstable : (prefixWord ++ tailWord_2477216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477216).length < 2 ^ (prefixWord ++ tailWord_2477216).sum := by decide
  have hdescent : baseEnd_2477216 < baseStart_2477216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477223 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2477223 : Nat := 118140960795 + 2477223 * 2 ^ 59
def prefixEnd_2477223 : Nat := 4983230072969 + 3 ^ 40 * 2477223 * 2
def baseEnd_2477223 : Nat := 1272006087372866587319965

theorem tailTrace_2477223 : CollatzResearch.WordTrace tailWord_2477223 prefixEnd_2477223 1272006087372866587319965 := by
  unfold tailWord_2477223
  simp only [CollatzResearch.WordTrace]
  refine ⟨90351745504451621850708323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60234497002967747900472215 90351745504451621850708323)
  ·
    refine ⟨135527618256677432776062485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90351745504451621850708323 135527618256677432776062485)
    ·
      refine ⟨6352857105781754661377929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135527618256677432776062485 6352857105781754661377929)
      ·
        refine ⟨4764642829336315996033447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352857105781754661377929 4764642829336315996033447)
        ·
          refine ⟨7146964244004473994050171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764642829336315996033447 7146964244004473994050171)
          ·
            refine ⟨10720446366006710991075257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146964244004473994050171 10720446366006710991075257)
            ·
              refine ⟨8040334774505033243306443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10720446366006710991075257 8040334774505033243306443)
              ·
                refine ⟨12060502161757549864959665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040334774505033243306443 12060502161757549864959665)
                ·
                  refine ⟨9045376621318162398719749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060502161757549864959665 9045376621318162398719749)
                  ·
                    refine ⟨1696008116497155449759953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9045376621318162398719749 1696008116497155449759953)
                    ·
                      refine ⟨1272006087372866587319965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696008116497155449759953 1272006087372866587319965)
                      ·
                        rfl

theorem cell23_2477223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2477223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477223 prefixEnd_2477223 := by exact prefixLift 2477223
  have htrace : WordTrace (prefixWord ++ tailWord_2477223) baseStart_2477223 baseEnd_2477223 := by
    simpa [prefixWord, tailWord_2477223, baseEnd_2477223] using wordTrace_append hprefix tailTrace_2477223
  have hstable : (prefixWord ++ tailWord_2477223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477223).length < 2 ^ (prefixWord ++ tailWord_2477223).sum := by decide
  have hdescent : baseEnd_2477223 < baseStart_2477223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477239 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_2477239 : Nat := 118140960795 + 2477239 * 2 ^ 59
def prefixEnd_2477239 : Nat := 4983230072969 + 3 ^ 40 * 2477239 * 2
def baseEnd_2477239 : Nat := 1272014303063338524719891

theorem tailTrace_2477239 : CollatzResearch.WordTrace tailWord_2477239 prefixEnd_2477239 1272014303063338524719891 := by
  unfold tailWord_2477239
  simp only [CollatzResearch.WordTrace]
  refine ⟨90352329072393656583290771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60234886048262437722193847 90352329072393656583290771)
  ·
    refine ⟨135528493608590484874936157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90352329072393656583290771 135528493608590484874936157)
    ·
      refine ⟨50823185103221431828101059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135528493608590484874936157 50823185103221431828101059)
      ·
        refine ⟨76234777654832147742151589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50823185103221431828101059 76234777654832147742151589)
        ·
          refine ⟨14294020810281027701653423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76234777654832147742151589 14294020810281027701653423)
          ·
            refine ⟨21441031215421541552480135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294020810281027701653423 21441031215421541552480135)
            ·
              refine ⟨32161546823132312328720203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441031215421541552480135 32161546823132312328720203)
              ·
                refine ⟨48242320234698468493080305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32161546823132312328720203 48242320234698468493080305)
                ·
                  refine ⟨36181740176023851369810229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48242320234698468493080305 36181740176023851369810229)
                  ·
                    refine ⟨3392038141502236065919709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36181740176023851369810229 3392038141502236065919709)
                    ·
                      refine ⟨1272014303063338524719891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392038141502236065919709 1272014303063338524719891)
                      ·
                        rfl

theorem cell23_2477239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_2477239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477239 prefixEnd_2477239 := by exact prefixLift 2477239
  have htrace : WordTrace (prefixWord ++ tailWord_2477239) baseStart_2477239 baseEnd_2477239 := by
    simpa [prefixWord, tailWord_2477239, baseEnd_2477239] using wordTrace_append hprefix tailTrace_2477239
  have hstable : (prefixWord ++ tailWord_2477239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477239).length < 2 ^ (prefixWord ++ tailWord_2477239).sum := by decide
  have hdescent : baseEnd_2477239 < baseStart_2477239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477256 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2477256 : Nat := 118140960795 + 2477256 * 2 ^ 59
def prefixEnd_2477256 : Nat := 4983230072969 + 3 ^ 40 * 2477256 * 2
def baseEnd_2477256 : Nat := 1272023032234464958207313

theorem tailTrace_2477256 : CollatzResearch.WordTrace tailWord_2477256 prefixEnd_2477256 1272023032234464958207313 := by
  unfold tailWord_2477256
  simp only [CollatzResearch.WordTrace]
  refine ⟨45176474556666034243329811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60235299408888045657773081 45176474556666034243329811)
  ·
    refine ⟨67764711834999051364994717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45176474556666034243329811 67764711834999051364994717)
    ·
      refine ⟨25411766938124644261873019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67764711834999051364994717 25411766938124644261873019)
      ·
        refine ⟨38117650407186966392809529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25411766938124644261873019 38117650407186966392809529)
        ·
          refine ⟨28588237805390224794607147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38117650407186966392809529 28588237805390224794607147)
          ·
            refine ⟨42882356708085337191910721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28588237805390224794607147 42882356708085337191910721)
            ·
              refine ⟨32161767531064002893933041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42882356708085337191910721 32161767531064002893933041)
              ·
                refine ⟨24121325648298002170449781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32161767531064002893933041 24121325648298002170449781)
                ·
                  refine ⟨2261374279527937703479667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24121325648298002170449781 2261374279527937703479667)
                  ·
                    refine ⟨3392061419291906555219501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261374279527937703479667 3392061419291906555219501)
                    ·
                      refine ⟨1272023032234464958207313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392061419291906555219501 1272023032234464958207313)
                      ·
                        rfl

theorem cell23_2477256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2477256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477256 prefixEnd_2477256 := by exact prefixLift 2477256
  have htrace : WordTrace (prefixWord ++ tailWord_2477256) baseStart_2477256 baseEnd_2477256 := by
    simpa [prefixWord, tailWord_2477256, baseEnd_2477256] using wordTrace_append hprefix tailTrace_2477256
  have hstable : (prefixWord ++ tailWord_2477256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477256).length < 2 ^ (prefixWord ++ tailWord_2477256).sum := by decide
  have hdescent : baseEnd_2477256 < baseStart_2477256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477293 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2477293 : Nat := 118140960795 + 2477293 * 2 ^ 59
def prefixEnd_2477293 : Nat := 4983230072969 + 3 ^ 40 * 2477293 * 2
def baseEnd_2477293 : Nat := 424014010339560437814881

theorem tailTrace_2477293 : CollatzResearch.WordTrace tailWord_2477293 prefixEnd_2477293 424014010339560437814881 := by
  unfold tailWord_2477293
  simp only [CollatzResearch.WordTrace]
  refine ⟨90354298614198023805756533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60236199076132015870504355 90354298614198023805756533)
  ·
    refine ⟨8470715495081064731789675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90354298614198023805756533 8470715495081064731789675)
    ·
      refine ⟨12706073242621597097684513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8470715495081064731789675 12706073242621597097684513)
      ·
        refine ⟨9529554931966197823263385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12706073242621597097684513 9529554931966197823263385)
        ·
          refine ⟨7147166198974648367447539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9529554931966197823263385 7147166198974648367447539)
          ·
            refine ⟨10720749298461972551171309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147166198974648367447539 10720749298461972551171309)
            ·
              refine ⟨4020280986923239706689241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10720749298461972551171309 4020280986923239706689241)
              ·
                refine ⟨3015210740192429780016931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020280986923239706689241 3015210740192429780016931)
                ·
                  refine ⟨4522816110288644670025397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015210740192429780016931 4522816110288644670025397)
                  ·
                    refine ⟨424014010339560437814881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4522816110288644670025397 424014010339560437814881)
                    ·
                      rfl

theorem cell23_2477293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2477293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477293 prefixEnd_2477293 := by exact prefixLift 2477293
  have htrace : WordTrace (prefixWord ++ tailWord_2477293) baseStart_2477293 baseEnd_2477293 := by
    simpa [prefixWord, tailWord_2477293, baseEnd_2477293] using wordTrace_append hprefix tailTrace_2477293
  have hstable : (prefixWord ++ tailWord_2477293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477293).length < 2 ^ (prefixWord ++ tailWord_2477293).sum := by decide
  have hdescent : baseEnd_2477293 < baseStart_2477293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477310 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2477310 : Nat := 118140960795 + 2477310 * 2 ^ 59
def prefixEnd_2477310 : Nat := 4983230072969 + 3 ^ 40 * 2477310 * 2
def baseEnd_2477310 : Nat := 424016920063269248977355

theorem tailTrace_2477310 : CollatzResearch.WordTrace tailWord_2477310 prefixEnd_2477310 424016920063269248977355 := by
  unfold tailWord_2477310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294364831892054463640673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60236612436757623806083589 11294364831892054463640673)
  ·
    refine ⟨8470773623919040847730505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11294364831892054463640673 8470773623919040847730505)
    ·
      refine ⟨6353080217939280635797879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470773623919040847730505 6353080217939280635797879)
      ·
        refine ⟨9529620326908920953696819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353080217939280635797879 9529620326908920953696819)
        ·
          refine ⟨14294430490363381430545229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9529620326908920953696819 14294430490363381430545229)
          ·
            refine ⟨5360411433886268036454461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14294430490363381430545229 5360411433886268036454461)
            ·
              refine ⟨2010154287707350513670423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5360411433886268036454461 2010154287707350513670423)
              ·
                refine ⟨3015231431561025770505635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010154287707350513670423 3015231431561025770505635)
                ·
                  refine ⟨4522847147341538655758453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015231431561025770505635 4522847147341538655758453)
                  ·
                    refine ⟨424016920063269248977355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4522847147341538655758453 424016920063269248977355)
                    ·
                      rfl

theorem cell23_2477310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2477310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477310 prefixEnd_2477310 := by exact prefixLift 2477310
  have htrace : WordTrace (prefixWord ++ tailWord_2477310) baseStart_2477310 baseEnd_2477310 := by
    simpa [prefixWord, tailWord_2477310, baseEnd_2477310] using wordTrace_append hprefix tailTrace_2477310
  have hstable : (prefixWord ++ tailWord_2477310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477310).length < 2 ^ (prefixWord ++ tailWord_2477310).sum := by decide
  have hdescent : baseEnd_2477310 < baseStart_2477310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477323 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 2, 4]
def baseStart_2477323 : Nat := 118140960795 + 2477323 * 2 ^ 59
def prefixEnd_2477323 : Nat := 4983230072969 + 3 ^ 40 * 2477323 * 2
def baseEnd_2477323 : Nat := 424019145146105398689835

theorem tailTrace_2477323 : CollatzResearch.WordTrace tailWord_2477323 prefixEnd_2477323 424019145146105398689835 := by
  unfold tailWord_2477323
  simp only [CollatzResearch.WordTrace]
  refine ⟨90355392804089338929348623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60236928536059559286232415 90355392804089338929348623)
  ·
    refine ⟨135533089206134008394022935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90355392804089338929348623 135533089206134008394022935)
    ·
      refine ⟨203299633809201012591034403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135533089206134008394022935 203299633809201012591034403)
      ·
        refine ⟨304949450713801518886551605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203299633809201012591034403 304949450713801518886551605)
        ·
          refine ⟨28589011004418892395614213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304949450713801518886551605 28589011004418892395614213)
          ·
            refine ⟨5360439563328542324177665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28589011004418892395614213 5360439563328542324177665)
            ·
              refine ⟨4020329672496406743133249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360439563328542324177665 4020329672496406743133249)
              ·
                refine ⟨3015247254372305057349937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020329672496406743133249 3015247254372305057349937)
                ·
                  refine ⟨2261435440779228793012453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015247254372305057349937 2261435440779228793012453)
                  ·
                    refine ⟨424019145146105398689835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261435440779228793012453 424019145146105398689835)
                    ·
                      rfl

theorem cell23_2477323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 4].length) (baseStart_2477323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477323 prefixEnd_2477323 := by exact prefixLift 2477323
  have htrace : WordTrace (prefixWord ++ tailWord_2477323) baseStart_2477323 baseEnd_2477323 := by
    simpa [prefixWord, tailWord_2477323, baseEnd_2477323] using wordTrace_append hprefix tailTrace_2477323
  have hstable : (prefixWord ++ tailWord_2477323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477323).length < 2 ^ (prefixWord ++ tailWord_2477323).sum := by decide
  have hdescent : baseEnd_2477323 < baseStart_2477323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477336 : List Nat := [2, 1, 2, 3, 1, 5, 1, 8]
def baseStart_2477336 : Nat := 118140960795 + 2477336 * 2 ^ 59
def prefixEnd_2477336 : Nat := 4983230072969 + 3 ^ 40 * 2477336 * 2
def baseEnd_2477336 : Nat := 47113485580993505378035

theorem tailTrace_2477336 : CollatzResearch.WordTrace tailWord_2477336 prefixEnd_2477336 47113485580993505378035 := by
  unfold tailWord_2477336
  simp only [CollatzResearch.WordTrace]
  refine ⟨45177933476521121074785931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60237244635361494766381241 45177933476521121074785931)
  ·
    refine ⟨67766900214781681612178897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45177933476521121074785931 67766900214781681612178897)
    ·
      refine ⟨50825175161086261209134173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67766900214781681612178897 50825175161086261209134173)
      ·
        refine ⟨19059440685407347953425315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50825175161086261209134173 19059440685407347953425315)
        ·
          refine ⟨28589161028111021930137973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19059440685407347953425315 28589161028111021930137973)
          ·
            refine ⟨2680233846385408305950435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28589161028111021930137973 2680233846385408305950435)
            ·
              refine ⟨4020350769578112458925653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680233846385408305950435 4020350769578112458925653)
              ·
                refine ⟨47113485580993505378035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4020350769578112458925653 47113485580993505378035)
                ·
                  rfl

theorem cell23_2477336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 8].length) (baseStart_2477336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477336 prefixEnd_2477336 := by exact prefixLift 2477336
  have htrace : WordTrace (prefixWord ++ tailWord_2477336) baseStart_2477336 baseEnd_2477336 := by
    simpa [prefixWord, tailWord_2477336, baseEnd_2477336] using wordTrace_append hprefix tailTrace_2477336
  have hstable : (prefixWord ++ tailWord_2477336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477336).length < 2 ^ (prefixWord ++ tailWord_2477336).sum := by decide
  have hdescent : baseEnd_2477336 < baseStart_2477336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477343 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2477343 : Nat := 118140960795 + 2477343 * 2 ^ 59
def prefixEnd_2477343 : Nat := 4983230072969 + 3 ^ 40 * 2477343 * 2
def baseEnd_2477343 : Nat := 1272067705051406117819413

theorem tailTrace_2477343 : CollatzResearch.WordTrace tailWord_2477343 prefixEnd_2477343 1272067705051406117819413 := by
  unfold tailWord_2477343
  simp only [CollatzResearch.WordTrace]
  refine ⟨90356122264016882345076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60237414842677921563384455 90356122264016882345076683)
  ·
    refine ⟨135534183396025323517615025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90356122264016882345076683 135534183396025323517615025)
    ·
      refine ⟨101650637547018992638211269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135534183396025323517615025 101650637547018992638211269)
      ·
        refine ⟨19059494540066061119664613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101650637547018992638211269 19059494540066061119664613)
        ·
          refine ⟨3573655226262386459937115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19059494540066061119664613 3573655226262386459937115)
          ·
            refine ⟨5360482839393579689905673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573655226262386459937115 5360482839393579689905673)
            ·
              refine ⟨4020362129545184767429255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360482839393579689905673 4020362129545184767429255)
              ·
                refine ⟨6030543194317777151143883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020362129545184767429255 6030543194317777151143883)
                ·
                  refine ⟨9045814791476665726715825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030543194317777151143883 9045814791476665726715825)
                  ·
                    refine ⟨6784361093607499295036869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9045814791476665726715825 6784361093607499295036869)
                    ·
                      refine ⟨1272067705051406117819413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6784361093607499295036869 1272067705051406117819413)
                      ·
                        rfl

theorem cell23_2477343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2477343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477343 prefixEnd_2477343 := by exact prefixLift 2477343
  have htrace : WordTrace (prefixWord ++ tailWord_2477343) baseStart_2477343 baseEnd_2477343 := by
    simpa [prefixWord, tailWord_2477343, baseEnd_2477343] using wordTrace_append hprefix tailTrace_2477343
  have hstable : (prefixWord ++ tailWord_2477343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477343).length < 2 ^ (prefixWord ++ tailWord_2477343).sum := by decide
  have hdescent : baseEnd_2477343 < baseStart_2477343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477359 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_2477359 : Nat := 118140960795 + 2477359 * 2 ^ 59
def prefixEnd_2477359 : Nat := 4983230072969 + 3 ^ 40 * 2477359 * 2
def baseEnd_2477359 : Nat := 1272075920741878055219339

theorem tailTrace_2477359 : CollatzResearch.WordTrace tailWord_2477359 prefixEnd_2477359 1272075920741878055219339 := by
  unfold tailWord_2477359
  simp only [CollatzResearch.WordTrace]
  refine ⟨90356705831958917077659131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60237803887972611385106087 90356705831958917077659131)
  ·
    refine ⟨135535058747938375616488697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90356705831958917077659131 135535058747938375616488697)
    ·
      refine ⟨101651294060953781712366523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135535058747938375616488697 101651294060953781712366523)
      ·
        refine ⟨152476941091430672568549785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101651294060953781712366523 152476941091430672568549785)
        ·
          refine ⟨114357705818573004426412339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152476941091430672568549785 114357705818573004426412339)
          ·
            refine ⟨171536558727859506639618509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114357705818573004426412339 171536558727859506639618509)
            ·
              refine ⟨64326209522947314989856941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171536558727859506639618509 64326209522947314989856941)
              ·
                refine ⟨24122328571105243121196353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64326209522947314989856941 24122328571105243121196353)
                ·
                  refine ⟨18091746428328932340897265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24122328571105243121196353 18091746428328932340897265)
                  ·
                    refine ⟨13568809821246699255672949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18091746428328932340897265 13568809821246699255672949)
                    ·
                      refine ⟨1272075920741878055219339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13568809821246699255672949 1272075920741878055219339)
                      ·
                        rfl

theorem cell23_2477359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_2477359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477359 prefixEnd_2477359 := by exact prefixLift 2477359
  have htrace : WordTrace (prefixWord ++ tailWord_2477359) baseStart_2477359 baseEnd_2477359 := by
    simpa [prefixWord, tailWord_2477359, baseEnd_2477359] using wordTrace_append hprefix tailTrace_2477359
  have hstable : (prefixWord ++ tailWord_2477359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477359).length < 2 ^ (prefixWord ++ tailWord_2477359).sum := by decide
  have hdescent : baseEnd_2477359 < baseStart_2477359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477364 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2477364 : Nat := 118140960795 + 2477364 * 2 ^ 59
def prefixEnd_2477364 : Nat := 4983230072969 + 3 ^ 40 * 2477364 * 2
def baseEnd_2477364 : Nat := 1272078488145150535656817

theorem tailTrace_2477364 : CollatzResearch.WordTrace tailWord_2477364 prefixEnd_2477364 1272078488145150535656817 := by
  unfold tailWord_2477364
  simp only [CollatzResearch.WordTrace]
  refine ⟨45178444098470401465795573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60237925464627201954394097 45178444098470401465795573)
  ·
    refine ⟨4235479134231600137418335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45178444098470401465795573 4235479134231600137418335)
    ·
      refine ⟨6353218701347400206127503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235479134231600137418335 6353218701347400206127503)
      ·
        refine ⟨9529828052021100309191255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353218701347400206127503 9529828052021100309191255)
        ·
          refine ⟨14294742078031650463786883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9529828052021100309191255 14294742078031650463786883)
          ·
            refine ⟨21442113117047475695680325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294742078031650463786883 21442113117047475695680325)
            ·
              refine ⟨4020396209446401692940061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21442113117047475695680325 4020396209446401692940061)
              ·
                refine ⟨1507648578542400634852523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020396209446401692940061 1507648578542400634852523)
                ·
                  refine ⟨2261472867813600952278785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507648578542400634852523 2261472867813600952278785)
                  ·
                    refine ⟨1696104650860200714209089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2261472867813600952278785 1696104650860200714209089)
                    ·
                      refine ⟨1272078488145150535656817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696104650860200714209089 1272078488145150535656817)
                      ·
                        rfl

theorem cell23_2477364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2477364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477364 prefixEnd_2477364 := by exact prefixLift 2477364
  have htrace : WordTrace (prefixWord ++ tailWord_2477364) baseStart_2477364 baseEnd_2477364 := by
    simpa [prefixWord, tailWord_2477364, baseEnd_2477364] using wordTrace_append hprefix tailTrace_2477364
  have hstable : (prefixWord ++ tailWord_2477364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477364).length < 2 ^ (prefixWord ++ tailWord_2477364).sum := by decide
  have hdescent : baseEnd_2477364 < baseStart_2477364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
